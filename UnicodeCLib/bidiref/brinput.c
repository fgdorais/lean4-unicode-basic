/*
**      Unicode Bidirectional Algorithm
**      Reference Implementation
**      © 2024 Unicode®, Inc.
**      Unicode and the Unicode Logo are registered trademarks of Unicode, Inc. in the U.S. and other countries.
**      For terms of use and license, see https://www.unicode.org/terms_of_use.html
*/

/*
 * brinput.c
 *
 * Module to input lines from BidiTest.txt or other input-defining
 * data files, to obtain the string input to submit to the UBA
 * processing and the expected output of the UBA processing.
 *
 * This module contains the main dispatch routines called from
 * main().
 *
 * Exports:
 *  br_RunFileTests
 *  br_RunStaticTest 
 */

/*
 * Change history:
 *
 * 2013-May-31 kenw   Created.
 * 2013-Jun-07 kenw   Added asymmetrical bracket match example.
 * 2013-Jun-19 kenw   Added use of br_ErrPrint.
 * 2013-Jun-27 kenw   Add more static test cases.
 * 2013-Jun-29 kenw   Add another static test case.
 * 2013-Jul-08 kenw   Update use of BR_MAXINPUTLEN.
 * 2015-Jun-05 kenw   Update error return code handling.
 * 2015-Aug-19 kenw   Add support for continue on test err.
 * 2016-Sep-21 kenw   Suppress security warnings on compilation.
 *                    Add casts for strlen returns to deal with warnings.
 *                    Add datapath param to br_RunFileTests.
 */

#define _CRT_SECURE_NO_WARNINGS
#include <string.h>
#include <ctype.h>
#include <stdio.h>

#include "bidirefp.h"

static int testCasesProcessed;
static int testCasesPassed;
static int testCasesFailed;

extern int continueOnTestErr;

/*
 * 2013-Mar-16: Just define some static string input to
 * get the UBA implementation off the ground. Later
 * on, the details can be filled out for parsing records
 * from BidiTest.txt, based only on Bidi_Class value, and
 * the abstractions used there for expected level and
 * reordering results.
 *
 * These examples do not contain embedded paragraph
 * separators. The assumption here is that the splitting of
 * paragraphs has already occurred, and that the processing
 * starts from rule P2, on a per paragraph basis.
 */

#define C_L1  0x0061
#define C_R1  0x05D0
#define C_AL1 0x0627
#define C_EN1 0x0030
#define C_AN1 0x0600
#define C_ET1 0x0024
#define C_ES1 0x002D
#define C_CS1 0x002C 
#define C_WS1 0x0020
#define C_ON1 0x0022
#define C_ON2 0x002E
#define C_ON3 0x0028
#define C_ON4 0x0029
#define C_ON5 0x005B
#define C_ON6 0x005D
#define C_ON7 0x2329
#define C_ON8 0x3009
#define C_BN1 0x200B
#define C_NSM 0x0300
#define C_LRE 0x202A
#define C_RLE 0x202B
#define C_PDF 0x202C
#define C_LRI 0x2066
#define C_RLI 0x2067
#define C_FSI 0x2068
#define C_PDI 0x2069
#define C_B1  0x000A

/*
 * During development, the best terminal display is for examples no longer
 * than 13 characters. Longer examples can, of course, be printed to
 * file and examined in an editor.
 */

static U_Int_32 example1[ 6] = { C_L1, C_L1, C_WS1, C_AL1, C_AL1, C_ON2 };
static U_Int_32 example2[12] = { C_L1, C_RLE, C_L1, C_WS1, C_AL1, C_NSM, 
                                C_ON2, C_EN1, C_PDF, C_L1, C_R1, C_WS1 };
static U_Int_32 example3[ 3] = { C_LRE, C_PDF, C_L1 };
static U_Int_32 example4[12] = { C_ON2, C_LRE, C_ON4, C_RLI, C_L1, C_PDI, 
                                C_ON1, C_PDF, C_ET1, C_NSM, C_BN1, C_AL1 };
static U_Int_32 example5[13] = { C_R1, C_RLI, C_L1, C_LRI, C_L1, C_RLE, C_L1,
                                C_PDF, C_L1, C_PDI, C_L1, C_PDI, C_L1 };
static U_Int_32 example6[13] = { C_ON2, C_ON3, C_ON4, C_ON5, C_L1, C_ON3, 
                                C_ON1, C_ON4, C_ET1, C_NSM, C_ON6, C_AL1, C_AN1 };
static U_Int_32 example7[ 4] = { C_ON3, C_L1, C_ON4, C_L1 };
static U_Int_32 example8[ 2] = { C_LRE, C_LRI };
static U_Int_32 example9[ 2] = { C_RLI, C_R1 };
static U_Int_32 example10[4] = { C_R1, C_RLI, C_PDF, C_R1 };
static U_Int_32 example11[4] = { C_FSI, C_LRI, C_PDI, C_R1 };
static U_Int_32 example12[13] = { C_ON2, C_ON3, C_ON4, C_ON5, C_L1, C_ON7, 
                                C_ON1, C_ON8, C_ET1, C_NSM, C_ON6, C_AL1, C_AN1 };
static U_Int_32 example13[ 4] = { C_R1, C_ON3, C_EN1, C_ON4 };
static U_Int_32 example14[ 5] = { C_R1, C_LRI, C_RLE, C_PDI, C_R1 };
static U_Int_32 example15[ 5] = { C_R1, C_EN1, C_ON3, C_R1, C_ON4 };

/*
 * Use these variables to adjust the static test:
 */

static int exampleLen = 5;
static U_Int_32 *example = example15;

/***********************************************************/

/*
 * SECTION: Utilities
 */

/*
 * br_PrintTestResult
 *
 * A small routine to encapsulate printing out whether a test case
 * passed or failed. Enables better control over formatting for
 * output using trace flags.
 *
 * Use Trace13 to force display of PASS results. These are
 * otherwise omitted, because for big test sets, the listings
 * of uninteresting PASS results quickly gets too long.
 *
 * For now, for debug tracing, an extra line is added before and
 * after each test case result line, so it can be found more
 * easily in the trace data. For non-debug runs, the extra lines
 * are removed.
 */

static void br_PrintTestResult ( int testNum, int rc )
{
    if ( rc == 1 )
    {
        testCasesPassed++;
        if ( Trace ( Trace13 ) )
        {
            printf ( "Test %d PASS\n", testNum );
        }
    }
    else
    {
        testCasesFailed++;
        if ( Trace ( Trace0 ) )
        {
            printf ( "Test %d FAIL\n", testNum );
        }
    }
}

/*
 * br_ExitTest
 *
 * Check on test exit conditions. This small routine consolidates
 * the checking for special conditions for exiting the main
 * test loops.
 *
 * In particular, it checks whether the continueOnTestErr flag
 * is set and the error return is a BR_TESTERR (instead of
 * some other, more serious error, such as a parsing error,
 * allocation error, etc.).
 */

static int br_ExitTest ( int rc )
{
    if ( ( rc == BR_TESTERR ) && continueOnTestErr )
    {
        return ( 0 );
    }
    else if ( rc < 0 )
    {
        return ( 1 );
    }
    else return ( 0 );
}

/***********************************************************/

/*
 * SECTION: Parsing FORMAT_A (BidiCharacterTest.txt)
 */

/*
 * br_ConstructUInt32Vector
 *
 * Take a space-delimited input string of code points expressed in 4 (to 6)
 * digit hex. Convert that into a vector of code points expressed as U_Int_32
 * values. Calculate and return the length of the constructed vector.
 */

static int br_ConstructUInt32Vector ( char *input, U_Int_32 *output, int *len )
{
int tlen;
char *sp;
char *send;
U_Int_32 *dp;
U_Int_32 nn;
int rc;
char localbuf[BUFFERLEN];

/* 
 * localbuf is defined long to protect against anomalous input.
 * Ordinarily it will only need 4-6 characters plus a null to
 * represent character values parsed from the input.
 */

    dp = output;
    sp = input;
    /* input is null-terminated, so the following check is safe */
    tlen = (int) strlen ( input );
    send = sp + tlen;

    tlen = 0;
    while ( sp < send )
    {
        /* Parse out one space-delimited character value. */
        sp = copySubField ( localbuf, sp );
        /* Attempt to convert ASCII hex to a code point value. */
        rc = convertHexToInt ( &nn, localbuf );
        if ( rc == -1 )
        {
            br_ErrPrint ( "Error: Character input string malformed.\n" );
            return ( BR_INITERR );
        }
        else if ( rc == -2 )
        {
            br_ErrPrint ( "Error: Character input string contains non-hex data.\n" );
            return ( BR_INITERR );
        }
        else if ( nn > 0x10FFFF )
        {
            br_ErrPrint ( "Error: Character input string contains code point out of range.\n" );
            return ( BR_INITERR );
        }
        /*
         * Code point parsed o.k. Write into the U_Int_32 buffer
         * and increment the length.
         */
        *dp++ = nn;
        tlen++;
        /* Check against buffer overrun. */
        if ( tlen > BR_MAXINPUTLEN )
        {
            sprintf ( localbuf, "Error: Character input string exceeds %d characters\n", 
                BR_MAXINPUTLEN );
            br_ErrPrint ( localbuf );
            return ( BR_INITERR );
        }
    }
    *len = tlen;
    return ( 1 );
}

/*
 * br_ParseOneLine
 *
 * Take a FORMAT_A input data line and tokenize it into the 5 field
 * values.
 *
 * Convert the two numeric fields into integers.
 *
 * For the other 3 fields, just stuff the string values into
 * the relevant output parameters for further processing.
 *
 * For FORMAT_A, which is semicolon delimited, this parsing
 * can re-use the same parsing utility function used for
 * parsing the property files.
 *
 * For well-defined input data, the strings will always be
 * well-formed. If a field is missing or null, the output
 * parameter will be set to a null string.
 */

static int br_ParseOneLine ( char *data, char *text, int *pdir,
    int *pembdlvl, char *levels, char *order )
{
char *sp;
int tdir;
int rc;
char localbuf[80];

    sp = data;

    sp = copyField ( text, sp );

    sp = copyField ( localbuf, sp );

    rc = br_Evaluate ( localbuf, &tdir );

    if ( rc != 1 )
    {
        sprintf ( localbuf, "Error: Bad paragraph direction value %s in input\n", localbuf );
        br_ErrPrint ( localbuf );
        return ( rc );
    }

    /*
     * Paragraph direction values in this format should be either
     * 0, 1, or 2, so check for those values.
     */

    switch ( tdir )
    {
        case 0 : *pdir = Dir_LTR;  break;
        case 1 : *pdir = Dir_RTL;  break;
        case 2 : *pdir = Dir_Auto; break;
        default : *pdir = Dir_Unknown;
    }

    if ( *pdir == Dir_Unknown )
    {
        sprintf ( localbuf, "Error: Specified paragraph direction %d out of range in input.\n", tdir );
        br_ErrPrint ( localbuf );
        return ( BR_INITERR );
    }

    sp = copyField ( localbuf, sp );

    rc = br_Evaluate ( localbuf, pembdlvl );

    if ( rc != 1 )
    {
        br_ErrPrint ( "Error: Bad resolved paragraph embedding level in input\n" );
        return ( BR_INITERR );
    }

    /*
     * Resolved paragraph embedding level values in this format should be either
     * 0, or 1, so check for those values.
     */
    if ( ( *pembdlvl < 0 ) || ( *pembdlvl > 1 ) )
    {
        br_ErrPrint ( "Error: Paragraph embedding level out of range in input\n" );
        return ( BR_INITERR );
    }

    sp = copyField ( levels, sp );

    sp = copyField ( order, sp );

    return ( 1 );
}

/*
 * br_ParseFileFormatA
 *
 * Parse test cases out of a file following the
 * format of BidiCharacterTest.txt.
 *
 * This is a simple format, with one test case per line:
 *
 * 05D0 2067 202A 0041;1;1;1 1 x 4;3 1 0
 *
 * Field 0: test string expressed as a sequence of code points
 * Field 1: paragraph direction (0=LTR, 1=RTL, -1=auto-LTR)
 * Field 2: resolved paragraph embedding level
 * Field 3: list of resolved levels ("x" represents deleted character)
 * Field 4: list of indices showing resolved visual order
 *
 * Note that the sublists are delimited by spaces.
 * In practice the characters used in BidiCharacterTest.txt are
 * limited to the BMP, which simplifies some testing implementations
 * which then don't have to handle supplementary characters.
 * But this bidi reference implementation does not assume that
 * input strings in FORMAT_A are limited to the BMP.
 */

static int br_ParseFileFormatA ( FILE *fdi )
{
int rc;
char buffer[RAWBUFFERLEN];
char text[BUFFERLEN];
char expLevels[BUFFERLEN];
char expOrder[BUFFERLEN];
U_Int_32 text32[BR_MAXINPUTLEN];
int textLen;
int paragraphDirection;
int expEmbeddingLevel;

    if ( Trace ( Trace2 ) )
    {
        printf ( "Trace: Entering br_ParseFileFormatA\n" );
    }

    rc = 0;

    while ( fgets ( buffer, RAWBUFFERLEN, fdi ) != NULL )
    {
    int slen;
    int i;
    int lineIsBlank;

    /* Don't process empty lines or comments. */
        slen = (int) strlen ( buffer );
        if ( ( slen == 0 ) || ( buffer[0] == '#' ) )
            {
            /* Decomment following line to dump comments to output, too. */
            /*  fputs ( buffer, stdout );  */
                continue ;
            }
    /* Also check for non-zero length lines with just whitespace */
        lineIsBlank = 1;
        i = 0 ;
        while ( lineIsBlank && ( i < slen ) )
        {
            if ( !isspace ( buffer[i] ) )
            {
                lineIsBlank = 0;
            }
            i++;
        }
        if ( lineIsBlank )
        {
            continue;
        }

#ifdef NOTDEF
        fputs ( buffer, stdout );
#endif

        rc = br_ParseOneLine ( buffer, text, &paragraphDirection,
            &expEmbeddingLevel, expLevels, expOrder );
        /*
         * Stop processing on detection of error.
         */
        if ( rc < 0 )
        {
            break;
        }

        /*
         * Construct the text32 vector by parsing the code point
         * hex values out of the text subfield and converting
         * them into actual 32-bit integer values. Calculate
         * the text length.
         */

        rc = br_ConstructUInt32Vector ( text, text32, &textLen );
        if ( rc < 0 )
        {
            break;
        }

        /* 
         * Bump the number for the test case. This will be used
         * to label test case output, if displayed.
         */

        testCasesProcessed++;

        rc = br_ProcessOneTestCase ( testCasesProcessed, text32, textLen, 
            paragraphDirection, expEmbeddingLevel, expLevels, expOrder );

        br_PrintTestResult ( testCasesProcessed, rc );
#ifdef NOTDEF
        if ( testCasesProcessed > 110 )
        {
            break;
        }
        /*
         * Temporary hack to print out diagnostics for a failing test
         * case, once identified.
         */
        if ( testCasesProcessed == 17 )
        {
            /* Stop showing all the intermediate output. */
            TraceOff ( Trace11 );
        }
#endif
        /* 
         * If hit a test case error and the continueOnTestErr
         * flag is set, just continue the loop. Otherwise exit
         * the loop immediately.
         */

        if ( br_ExitTest (rc) )
        {
            break;
        }
    }
    if ( rc < 0 )
    {
        return ( rc );
    }
    return ( BR_TESTOK );
}

/***********************************************************/

/*
 * SECTION: Parsing FORMAT_B (BidiTest.txt)
 */

/*
 * br_ConstructUInt32VectorBC
 *
 * Take a space-delimited input string of Bidi_Class values expressed
 * symbolically. Convert that into a vector of Bidi_Class values expressed 
 * as enumerated values.
 *
 * For this function, the length is precalculated and checked to
 * ensure it will not overrun.
 */

static int br_ConstructUInt32VectorBC ( char *input, U_Int_32 *output )
{
char *sp;
char *send;
U_Int_32 *dp;
BIDIPROP bc;
char localbuf[BUFFERLEN]; 
/* 
 * localbuf is defined long to protect against anomalous input.
 * Ordinarily it will only need 1-3 characters plus a null to
 * represent Bidi_Class values parsed from the input.
 */
    if ( Trace ( Trace2 ) )
    {
        printf( "Trace: Entering br_ConstructUInt32VectorBC\n" );
    }
    dp = output;
    sp = input;
    send = sp + strlen (input );

    while ( sp < send )
    {
        /* Parse out one space-delimited Bidi_Class symbolic value. */
        sp = copySubField ( localbuf, sp );
        /* Attempt to convert to an enumerated Bidi_Class value */
        bc = br_GetBCFromLabel ( localbuf );

        if ( bc == BIDI_Unknown )
        {
            br_ErrPrint ( "Error: Unknown Bidi_Class value encountered.\n" );
            return ( BR_INITERR );
        }
        /*
         * Bidi_Class parsed o.k. Write into the U_Int_32 buffer.
         */
        *dp++ = bc;
    }
    return ( 1 );
}

/*
 * br_ParseAtVar
 *
 * Parse the expected value subfield out of one @-variable
 * line from BidiTest.txt.
 *
 * Lines for the @-variables are of the format:
 *
 * @Levels:    1 0
 * @Levels:    x 1 x 2
 * @Reorder:   1 0
 * @Reorder:   3 1
 *
 * The values consist of a list, indefinitely long, of space-delimited
 * individual values. Parsing the sub-field values is handled elsewhere.
 * Note that these are full lines parsed from the input, so they still
 * have terminating EOLN characters. Take those into account when
 * parsing out the significant values in the data.
 *
 * This routine is defined locally, instead of as part of the
 * generic field parsing utilities, because it is specific to
 * BidiTest.txt (Format B) test data file.
 */

static int br_ParseAtVar ( char *dest, char *src )
{
char *sp;
char *dp;

    sp = src;
    dp = dest;
    /* Scan ahead to the colon. */
    while ( ( *sp != ':' ) && ( *sp != '\0' ) )
    {
        sp++;
    }
    if ( *sp == '\0' )
    {
        return ( BR_INITERR );
    }
    sp++;

    /* Span past any initial whitespace in the subfield. */

    while ( ( ( *sp == ' ' ) || ( *sp == '\t' ) ) && ( *sp != '\0' ) )
    {
        sp++;
    }
    if ( *sp == '\0' )
    {
        return ( BR_INITERR );
    }

    /* Now sp points a non-null field to be copied. */

    while ( ( *sp != '\0' ) && ( *sp != '\n' ) )
    {
        *dp++ = *sp++;
    }
    *dp = '\0';

    return ( 1 );
}

/*
 * br_ParseOneDataLineB
 *
 * Take a FORMAT_B input data line and tokenize it into the 2 field
 * values.
 *
 * Convert the one numeric field into an integer.
 *
 * For the other field, just stuff the string value into
 * the text parameter for further processing.
 *
 * For FORMAT_B data lines, which are semicolon delimited, this parsing
 * can re-use the same parsing utility function used for
 * parsing the property files.
 *
 * For well-defined input data, the strings will always be
 * well-formed. If a field is missing or null, the output
 * parameter will be set to a null string.
 */

static int br_ParseOneDataLineB ( char *data, char *text, int *textLen, int *pdir )
{
char *sp;
char *sp2;
int len;
int rc;
char localbuf[6];

    sp = data;

    sp = copyField ( text, sp );

    /*
     * Calculate the number of units in the text field.
     * These are space-delimited. On this pass, throw
     * away the actual subfield data. That will be
     * processed later.
     */

    sp2 = text;
    len = 0;
    while ( *sp2 != '\0' )
    {
        sp2 = copySubField ( localbuf, sp2 );
        len++;
    }
    *textLen = len;

    sp = copyField ( localbuf, sp );

    rc = br_Evaluate ( localbuf, pdir );

    if ( rc != 1 )
    {
        printf ( "Error: Bad paragraph direction value in input\n" );
        return ( BR_INITERR );
    }
    /*
     * Paragraph direction values in this format are expressed
     * as a bitset. 1 = auto-LTR, 2 = LTR, 4 = RTL. Therefore
     * the expected range of possible values for this in the
     * data should be 1..7. Check for those values.
     */
    if ( ( *pdir < 1 ) || ( *pdir > 7 ) )
    {
        br_ErrPrint ( "Error: Paragraph direction bitset out of range in input\n" );
        return ( BR_INITERR );
    }

    return ( 1 );
}

/*
 * br_ParseFileFormatB
 *
 * Parse test cases out of a file following the
 * format of BidiTest.txt.
 *
 * This format is more complex and compacted, using
 * @-variables to define values which persist across
 * multiple sets of input data.
 *
 * Also, the input data is expressed in terms of Bidi_Class
 * values, instead of code points. This requires special
 * handling, particularly for the version 6.3 implementation,
 * which assumes access to code points for doing the
 * parenthesis matching part of the algorithm.
 */

/*
 * Values for the paragraph direction bitset.
 */
#define AUTO_BIT (1)
#define LTR_BIT (2)
#define RTL_BIT (4)

static int br_ParseFileFormatB ( FILE *fdi )
{
int rc;
int levelLines;
int orderLines;
char buffer[RAWBUFFERLEN];
char text[BUFFERLEN];
char expLevels[BUFFERLEN];
char expOrder[BUFFERLEN];
U_Int_32 text32[BR_MAXINPUTLEN];
char errString[80];
int textLen;
int pdBitset;

    if ( Trace ( Trace2 ) )
    {
        printf ( "Trace: Entering br_ParseFileFormatB\n" );
    }

    /* Initialize variables. */
    rc = 0;
    levelLines = 0;
    orderLines = 0;
    /* 
     * Initialize output parameters. This bombproofs against
     * a potential problem in BidiTest.txt format files containing
     * a test case line before the appropriate @-variables
     * are defined.
     */
    expLevels[0] = '\0';
    expOrder[0] = '\0';

    while ( fgets ( buffer, 512, fdi ) != NULL )
    {
    int slen;
    int i;
    int lineIsBlank;

    /* Don't process empty lines or comments. */
        slen = (int) strlen ( buffer );
        if ( ( slen == 0 ) || ( buffer[0] == '#' ) )
            {
            /* Decomment following line to dump comments to output, too. */
            /*  fputs ( buffer, stdout );  */
                continue ;
            }
    /* Also check for non-zero length lines with just whitespace */
        lineIsBlank = 1;
        i = 0 ;
        while ( lineIsBlank && ( i < slen ) )
        {
            if ( !isspace ( buffer[i] ) )
            {
                lineIsBlank = 0;
            }
            i++;
        }
        if ( lineIsBlank )
        {
            continue;
        }

#ifdef NOTDEF
        fputs ( buffer, stdout );
#endif
        /*
         * The guts of the parsing go here, distinguishing
         * between @-variable lines and test case data lines, and
         * branching accordingly.
         */
        if ( buffer[0] == '@' )
        {
            if ( strstr ( buffer, "Levels" ) != NULL )
            {
                levelLines++;
                rc = br_ParseAtVar ( expLevels, buffer );
                if ( rc != 1 )
                {
                    br_ErrPrint ( "Error: Syntax error in @-variable.\n" );
                    return ( rc );
                }
                else if ( Trace ( Trace12 ) )
                {
                    printf ( "Parsed levels: [%s]\n", expLevels );
                }
            }
            else if ( strstr ( buffer, "Reorder") != NULL )
            {
                orderLines++;
                rc = br_ParseAtVar ( expOrder, buffer );
                if ( rc != 1 )
                {
                    br_ErrPrint ( "Error: Syntax error in @-variable.\n" );
                    return ( rc );
                }
                else if ( Trace ( Trace12 ) )
                {
                    printf ( "Parsed order:  [%s]\n", expOrder );
                }
            }
            else
            {
                /* 
                 * BidiTest.txt says to ignore any other @-variable
                 * but for a reference implementation for particular
                 * versions, that seems inadvisable. Stop with an
                 * error. Update this processing whenever new
                 * @-variables are defined in BidiTest.txt.
                 */
                br_ErrPrint ( "Error: Invalid @-variable found.\n" );
                return ( BR_INITERR );
            }
        }
        else
        /* 
         * We have a regular test case data input line, of the format:
         * L LRE R R; 7
         * Parse out the two fields for further processing.
         * Also calculate the text length.
         */
        {
            rc = br_ParseOneDataLineB ( buffer, text, &textLen, &pdBitset );

            if ( rc < 0 )
            {
                break;
            }
            if ( Trace ( Trace12 ) )
            {
                printf ( "Parsed: text len: %d, pd bitset: %d\n", textLen, pdBitset );
            }

            /*
             * Set up a dummy text line, based on the calculated textLen.
             * Note that the actual content of the parsed text here is a
             * list of Bidi_Class values. To prevent having to set up more
             * structures and divergent processing, the BidiClass values
             * are temporarily stored in text32 and are then transferred into
             * the BIDIUNIT Bidi_Class storage when the UBACONTEXT is constructed
             * for the test case.
             */

            if ( textLen > BR_MAXINPUTLEN )
            {
                sprintf ( errString, "Error: Parsed input length %d exceeds limit %d\n", 
                    textLen, BR_MAXINPUTLEN );
                br_ErrPrint ( errString );
                rc = BR_INITERR;
                break;
            }
            else
            {
                rc = br_ConstructUInt32VectorBC ( text, text32 );
                if ( rc < 0 )
                {
                    break;
                }
            }

            /*
             * Then process the paragraphDirection bitset. For each
             * bit set, run the test case once with the appropriate
             * Direction value. 1=Dir_Auto, 2=Dir_LTR, 4=Dir_RTL.
             */

            if ( ( pdBitset & AUTO_BIT ) == AUTO_BIT )
            {
                if ( Trace ( Trace12 ) )
                {
                    printf ( "Paragraph Direction: Auto\n" );
                }
                testCasesProcessed++;
                rc = br_ProcessOneTestCase ( testCasesProcessed, text32, textLen, 
                    Dir_Auto, 0, expLevels, expOrder );
                br_PrintTestResult ( testCasesProcessed, rc );
                if ( br_ExitTest (rc) )
                {
                   break;
                }
            }

            if ( ( pdBitset & LTR_BIT ) == LTR_BIT )
            {
                if ( Trace ( Trace12 ) )
                {
                    printf ( "Paragraph Direction: LTR\n" );
                }
                testCasesProcessed++;
                rc = br_ProcessOneTestCase ( testCasesProcessed, text32, textLen, 
                    Dir_LTR, 0, expLevels, expOrder );
                br_PrintTestResult ( testCasesProcessed, rc );
                if ( br_ExitTest (rc) )
                {
                   break;
                }
            }

            if ( ( pdBitset & RTL_BIT ) == RTL_BIT )
            {
                if ( Trace ( Trace12 ) )
                {
                    printf ( "Paragraph Direction: RTL\n" );
                }
                testCasesProcessed++;
                rc = br_ProcessOneTestCase ( testCasesProcessed, text32, textLen, 
                    Dir_RTL, 0, expLevels, expOrder );
                br_PrintTestResult ( testCasesProcessed, rc );
                if ( br_ExitTest (rc) )
                {
                   break;
                }
            }

            /*
             * For debug purposes, throttle the input, so as not to get
             * overwhelmed by too many test cases.
             */
#ifdef NOTDEF
            if ( testCasesProcessed > 472 )
            {
                break;
            }
            /*
             * Temporary hack to print out diagnostics for a failing test
             * case, once identified.
             */
            if ( testCasesProcessed == 470 )
            {
            /* Start showing all the intermediate output. */
                TraceOn ( Trace11 );
            }
#endif
        }
    }
    if ( Trace ( Trace12 ) )
    {
        printf ( "Parsed:    %d @Level Lines, %d @Reorder Lines\n", 
            levelLines, orderLines );
    }
    if ( rc < 0 )
    {
        return ( rc );
    }
    return ( BR_TESTOK );
}

/***********************************************************/

/*
 * SECTION: Main dispatch routines.
 *
 * These are called from bidiref.c.
 */

/*
 * br_RunStaticTest
 *
 * Routine used mostly during development of the bidiref
 * implementation. This runs *one* test case, based on
 * static values defined in this module.
 *
 * It has no expected output defined.
 */

int br_RunStaticTest ( void )
{
int rc;

    if ( Trace ( Trace2 ) )
    {
        printf ( "Trace: Entering br_RunStaticTest\n" );
    }

    rc = br_ProcessOneTestCase ( 1, example, exampleLen, Dir_Auto, -1, NULL, NULL );

    return ( rc );
}

/*
 * br_RunFileTests
 *
 * Default mode of operation. Parse an input file and
 * run test cases sequentially, testing each against
 * expected output, which is also parsed from the input file.
 *
 * This function just opens the input file, then calls
 * the appropriate routine to parse and run the test
 * cases, depending on the file format.
 *
 * TBD: validate the actual file format by examining
 * the header and/or other specifics in the test data,
 * before calling the parse function for the test cases.
 */

int br_RunFileTests ( int version, char *datapath, char *input )
{
FILE *fdi;
int rc;
int usepath;
char fqfn[512];
char errString[BUFFERLEN];

    if ( Trace ( Trace2 ) )
    {
        printf ( "Trace: Entering br_RunFileTests\n" );
    }

    /*
     * If datapath is NULL or is a zero-length string, ignore it.
     * Otherwise use it.
     */

    if ( datapath == NULL )
    {
        usepath = 0;
    }
    else if ( strcmp ( datapath, "" ) == 0 )
    {
        usepath = 0;
    }
    else
    {
        usepath = 1;
    }

    if ( usepath )
    {
        strcpy ( fqfn, datapath );
        strcat ( fqfn, input );
    }
    else
    {
        strcpy ( fqfn, input );
    }

    fdi = fopen ( fqfn, "rt" );

    if ( fdi == NULL )
    {
        sprintf ( errString, "Error: Cannot open input file: \"%s\"\n", fqfn );
        br_ErrPrint ( errString );
        return ( BR_INITERR ) ;
    }

    if ( Trace ( Trace2 ) )
    {
        printf ( "Parsing %s\n", fqfn );
    }

    /* Do the work */

    testCasesProcessed = 0;
    testCasesPassed = 0;
    testCasesFailed = 0;

    if ( GetFileFormat() == FORMAT_A )
    {
        rc = br_ParseFileFormatA ( fdi );
    }
    else
    {
        rc = br_ParseFileFormatB ( fdi );
    }

    fclose ( fdi );

    if ( Trace ( Trace0 ) )
    {
        printf ( "Processed: %d test cases, %d PASS, %d FAIL\n", 
            testCasesProcessed, testCasesPassed, testCasesFailed );
    }

    if ( rc < 0 )
    {
        br_ErrPrint ( "Error: abnormal termination.\n" );
        return ( rc );
    }

    return ( BR_TESTOK );
}
