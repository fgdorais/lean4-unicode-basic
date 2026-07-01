/*
**      Unicode Bidirectional Algorithm
**      Reference Implementation Demo Program
**      © 2024 Unicode®, Inc.
**      Unicode and the Unicode Logo are registered trademarks of Unicode, Inc. in the U.S. and other countries.
**      For terms of use and license, see https://www.unicode.org/terms_of_use.html
*/

#include <string.h>
#include <stdio.h>
#include <stdlib.h>

#include "bidiref.h"

#define OUTPUTBUFLEN 800
#define INBUFLEN 200

static int ubaParagraphDir = 2;
/*
 * MAINTENANCE NOTE: Each time a new UBA version is added to
 * bidiref, update this ubaVersion to the latest supported version.
 */
static UBA_Version_Type ubaVersion = UBA160;
static U_Int_32 ubaInputSeq[INBUFLEN];
static int ubaInputSeqLen = 0;


/*
 * MAINTENANCE NOTE: Each time a new UBA version is added to
 * bidiref, add the corresponding number to the usage message
 * for -u and to the switch statement processing the -u parameter.
 */
int ParseArgs ( int argc, char *argv[] )
{
    char *arg;
    char *str;
    char *nexttoken = NULL;

    if ( argc != 6 )
    {
        printf ( "Usage:\n    bidiref1 -b[0-2] -u[62,63,70,80,90,100,110,120,130,140,150,151,160] -d[2-4] -y[0-1] \"-s hhhh hhhh...\"\n" );
        return 0;
    }

    do
    {
        --argc;
        ++argv;
        arg = argv[0];

        if ( arg[0] == '-' )
        {
            switch ( arg[1] )
            {
            case 'b':
                if ( '0' <= arg[2] && arg[2] <= '2' )
                {
                    ubaParagraphDir = arg[2] - '0';
                }
                break;
            case 'u':
                if ( arg[2] != '\0' && arg[3] != '\0')
                {
                    str = arg + 2;
                    if ( strncmp ( str, "62", 2 ) == 0 )        { ubaVersion = UBA62; }
                    else if ( strncmp ( str, "63", 2 ) == 0 )   { ubaVersion = UBA63; }
                    else if ( strncmp ( str, "70", 2 ) == 0 )   { ubaVersion = UBA70; }
                    else if ( strncmp ( str, "80", 2 ) == 0 )   { ubaVersion = UBA80; }
                    else if ( strncmp ( str, "90", 2 ) == 0 )   { ubaVersion = UBA90; }
                    else if ( strncmp ( str, "100", 3 ) == 0 )  { ubaVersion = UBA100; }
                    else if ( strncmp ( str, "110", 3 ) == 0 )  { ubaVersion = UBA110; }
                    else if ( strncmp ( str, "120", 3 ) == 0 )  { ubaVersion = UBA120; }
                    else if ( strncmp ( str, "130", 3 ) == 0 )  { ubaVersion = UBA130; }
                    else if ( strncmp ( str, "140", 3 ) == 0 )  { ubaVersion = UBA140; }
                    else if ( strncmp ( str, "150", 3 ) == 0 )  { ubaVersion = UBA150; }
                    else if ( strncmp ( str, "151", 3 ) == 0 )  { ubaVersion = UBA151; }
                    else if ( strncmp ( str, "160", 3 ) == 0 )  { ubaVersion = UBA160; }
                }
                break;
            case 'd':
                if ( '2' <= arg[2] && arg[2] <= '4' )
                {
                    TraceOff ( TraceAll );
                    switch ( arg[2] )
                    {
                    case '4':
                        TraceOn ( Trace4 | Trace7 | Trace9 | Trace12 );
                    case '3':
                        TraceOn ( Trace3 | Trace5 | Trace6 | Trace8 );
                    case '2':
                        TraceOn ( Trace0 | Trace1 | Trace2 | Trace11 | Trace15 );
                        break;
                    }
                }
                break;
            case 'y':
                switch ( arg[2] )
                {
                case '0':
                    TraceOff ( Trace14 );
                    break;
                case '1':
                    TraceOn ( Trace14 );
                    break;
                }
                break;
            case 's':
                ubaInputSeq[ubaInputSeqLen++] = (int) strtol ( arg + 2, &nexttoken, 16 );
                while ( nexttoken != NULL && nexttoken[0] != '\0' )
                {
                    ubaInputSeq[ubaInputSeqLen++] = (int) strtol ( nexttoken, &nexttoken, 16 );
                }
                break;
            }
        }
    } while (argc > 1);

    return ( 1 );
}


int main ( int argc, char *argv[] )
{
    int rc;
    int resEmbeddingLevel;
    char resLevels[OUTPUTBUFLEN];
    char resOrder[OUTPUTBUFLEN];

    if ( ParseArgs( argc, argv ) == 0 )
    {
        return 0;
    }

#ifdef _WIN32
    rc = br_InitWithPath ( ubaVersion, "ucd\\" );
#else
    rc = br_InitWithPath ( ubaVersion, "ucd/" );
#endif

    if ( rc != 1 )
    {
        printf ( "Error in initialization.\n" );
        return ( rc );
    }

    rc = br_QueryOneTestCase ( ubaInputSeq, ubaInputSeqLen, ubaParagraphDir,
        &resEmbeddingLevel, resLevels, OUTPUTBUFLEN, resOrder, OUTPUTBUFLEN );

    printf("--------------------------------------------------------------------------------\n");

    if ( rc == 1 )
    {
        printf ( "Paragraph Embedding Level: %d\n", resEmbeddingLevel );
        printf ( "Resolved Levels: [%s]\n", resLevels );
        printf ( "Resolved Order:  [%s]\n", resOrder );
    }
    else
    {
        printf ( "An error occurred (return code %d).\n", rc );
    }

    return ( 1 );
}
