/*
**      Unicode Bidirectional Algorithm
**      Reference Implementation
**      © 2024 Unicode®, Inc.
**      Unicode and the Unicode Logo are registered trademarks of Unicode, Inc. in the U.S. and other countries.
**      For terms of use and license, see https://www.unicode.org/terms_of_use.html
*/

/*
 * bidiref.c
 *
 * Unicode Bidirectional Algorithm (UBA)
 * Reference Implementation
 *
 * This reference implementation is deliberately designed to
 * be literal and to explicitly follow the UBA specification
 * in UAX #9 for didactic reasons. It is not optimized, nor
 * intended as a direct guide to how to build an efficient
 * implementation. Instead, it is designed to make the steps
 * of the algorithm clear, so as to provide unambiguous
 * interpretation of the intended results of the UBA in all
 * input cases.
 */

/*
 * Change history:
 *
 * 2013-May-31 kenw   Created to match UBA 6.2.0 spec and
 *                    UBA 6.3.0 spec.
 * 2013-Jun-02 kenw   Reworked to put the UBA and initial
 *                    table loading into a dll (or static
 *                    library) with a public API.
 * 2013-Jun-07 kenw   Added Trace14.
 * 2013-Jun-19 kenw   Added Trace15.
 * 2013-Jun-21 kenw   Tweaks for U_Int_32 definition.
 * 2013-Jun-26 kenw   Version 1.5.
 * 2013-Jun-27 kenw   Version 1.6. (Various bug fixes)
 * 2013-Jun-29 kenw   Version 1.7. (Bug fix in N0)
 * 2013-Jul-08 kenw   Version 1.8. (Bug fix in br_DropSequence)
 * 2014-Apr-17 kenw   Version 7.0.0. Update for Unicode 7.0
 *                    and synch bidiref version to the standard.
 * 2015-Jun-04 kenw   Further updates for Unicode 7.0.
 * 2015-Jun-05 kenw   Version 8.0.0.
 * 2015-Aug-19 kenw   Add flag to support continue on test err.
 * 2015-Dec-04 kenw   Updated build date.
 * 2016-Sep-22 kenw   Version 9.0.0. Add input path setting.
 * 2016-Oct-06 kenw   Update version string date, tweak usage msg.
 * 2017-Jun-26 kenw   Version 10.0.0.
 * 2018-Jul-22 kenw   Version 11.0.0. Updates for file path handling
 *                    and loading of version-specific data files.
 * 2019-Nov-19 kenw   Version 12.0.0.
 * 2020-Mar-27 kenw   Version 13.0.0.
 * 2021-Sep-23 kenw   Version 14.0.0.
 * 2022-Sep-30 kenw   Version 15.0.0.
 * 2023-Oct-03 kenw   Version 15.1.0.
 * 2024-Sep-25 kenw   Version 16.0.0.
 */

#define _CRT_SECURE_NO_WARNINGS
#include <string.h>
#include <stdio.h>
#include <ctype.h>

#include "bidirefp.h"

/*
 * MAINTENANCE NOTE: Update this version string and date for each
 * new bidiref version.
 */

static char versionString[] = "bidiref version 16.0.0, 2024-09-25\n";

static char infile[] = "BidiRefTest.txt"; /* default file name */

/*
 * Set the MAXARGLEN value fairly high, to allow fully-qualified
 * input file names.
 */
#define MAXARGLEN (512)

char inputFileName[MAXARGLEN];
char datapath[MAXARGLEN];

int debugLevel; /* Set level for debug output */
int staticTest; /* Use static test string(s) */

/*
 * Note: The following flag, if it proves useful, could be
 * upgraded for set/reset through an API, to allow active
 * control by an application running test cases.
 */
int continueOnTestErr; /* Don't stop if test case fails. */

/***********************************************************/

/*
 * SetInitialTraceFlags
 *
 * Adjust the initial traceFlags value based on the
 * overall debug level chosen at the command line or
 * at runtime.
 */

static void SetInitialTraceFlags ( void )
{
    TraceOn ( Trace0 );
    TraceOn ( Trace15 );
    if ( debugLevel > 0 )
    {
        TraceOn ( Trace1 | Trace2 );
    }
    if ( debugLevel > 1 )
    {
        TraceOn ( Trace11 );
    }
    if ( debugLevel > 2 )
    {
        TraceOn ( Trace3 | Trace5 | Trace6 | Trace8 );
    }
    if ( debugLevel > 3 )
    {
        TraceOn ( Trace4 | Trace7 | Trace9 | Trace12 );
    }
    /* Temporary testing of single trace flag */
    /* TraceOn ( Trace10 ); */
}

/***********************************************************/

/*
 * SECTION: Command Line Processing.
 *
 * MAINTENANCE NOTE: Update the usageMsg listing of the default UBA version
 * for each new version. Also update the list of valid values each time a
 * new UBA version is added to the code.
 */

static void usageMsg( void )
{
    fputs ("Usage: bidiref (-dn)(-unn)(-xyzvh)(-p path)(filename)\n", stdout );
    fputs ("       Default input is BidiRefTest.txt\n", stdout );
    fputs ("       Default UBA version is 16.0.\n", stdout );
    fputs ("       -dn  set diagnostic mode: 1 minimum, 2 medium, 3 high, 4 maximum.\n",
        stdout );
    fputs ("       -c   continue if test case fails.\n", stdout );
    fputs ("       -p path\\   read input files from directory specified by path.\n", stdout );
    fputs ("       -unn set UBA version to n.n. (valid values: -u62, -u63, -u70, -u80, -u90, -u100, -u110, -u120, -u130, -u140, -u150, -u151, -u160 )\n",
        stdout );
    fputs ("       -x   set UBA version to 6.3. (= -u63)\n", stdout );
    fputs ("       -y   omit output for vacuous rule application (Trace14 on).\n", stdout );
    fputs ("       -z   run one statically defined test diagnostic.\n", stdout );
    fputs ("       -v   show bidiref program version.\n", stdout );
    fputs ("       -h   show this usage message.\n", stdout );
}

static void versionMsg(void)
{
    fputs ( versionString, stdout );
}

/*
 * processArguments()
 *
 * -1 Error return code. Post error message and stop.
 *  0 Stop return code. Stop without further processing.
 *  1 Continue return code. Continue processing.
 *
 * MAINTENANCE NOTE: Each time a new UBA version is added,
 * extend the switch statement processing for "-u" to pick
 * up and properly parse that new UBA version.
 */

static int processArguments( int argc, char *argv[] )
{
char argstring[MAXARGLEN];
char* tmp;
char c;
int numargs = argc;
int foundFile = 0;

/*
 * Set up default values for input parameters.
 */
    debugLevel = 0;
    staticTest = 0;
    continueOnTestErr = 0;
    SetUBAVersion ( UBACUR ); /* Will default to latest. */
    strcpy ( datapath, "" );

    while ( numargs > 1 )
    {
        strncpy ( argstring, *++argv, MAXARGLEN );
        argstring[MAXARGLEN - 1] = '\0';
        numargs--;
        tmp = argstring;
        c = *tmp++;
        if ( c == '-' )
        {
            c = *tmp;
            switch ( c )
            {
            case 'd' :
                tmp++;
                if ( *tmp == '1' )
                {
                    debugLevel = 1;
                }
                else if ( *tmp == '2' )
                {
                    debugLevel = 2;
                }
                else if ( *tmp == '3' )
                {
                    debugLevel = 3;
                }
                else if ( *tmp == '4' )
                {
                    debugLevel = 4;
                }
                else
                {
                    usageMsg();
                    return -1;
                }
                break;
            case 'u' :
                tmp++;
                if ( *tmp == '6' )
                {
                    tmp++;
                    if ( *tmp == '2')
                    {
                        SetUBAVersion (UBA62);
                    }
                    else if ( *tmp == '3')
                    {
                        SetUBAVersion (UBA63);
                    }
                    else
                    {
                        usageMsg();
                        return -1;
                    }
                }
                else if ( *tmp == '7' )
                {
                    tmp++;
                    if ( *tmp == '0')
                    {
                        SetUBAVersion (UBA70);
                    }
                    else
                    {
                        usageMsg();
                        return -1;
                    }
                }
                else if ( *tmp == '8' )
                {
                    tmp++;
                    if ( *tmp == '0' )
                    {
                        SetUBAVersion (UBA80);
                    }
                    else
                    {
                        usageMsg();
                        return -1;
                    }
                }
                else if ( *tmp == '9' )
                {
                    tmp++;
                    if ( *tmp == '0' )
                    {
                        SetUBAVersion (UBA90);
                    }
                    else
                    {
                        usageMsg();
                        return -1;
                    }
                }
                else if ( *tmp == '1' )
                {
                    tmp++;
                    if ( *tmp == '0' )
                    {
                        tmp++;
                        if ( *tmp == '0' )
                        {
                            SetUBAVersion (UBA100);
                        }
                        else
                        {
                            usageMsg();
                            return -1;
                        }
                    }
                    else if ( *tmp == '1' )
                    {
                        tmp++;
                        if ( *tmp == '0' )
                        {
                            SetUBAVersion (UBA110);
                        }
                        else
                        {
                            usageMsg();
                            return -1;
                        }
                    }
                    else if ( *tmp == '2' )
                    {
                        tmp++;
                        if ( *tmp == '0' )
                        {
                            SetUBAVersion (UBA120);
                        }
                        else
                        {
                            usageMsg();
                            return -1;
                        }
                    }
                    else if ( *tmp == '3' )
                    {
                        tmp++;
                        if ( *tmp == '0' )
                        {
                            SetUBAVersion (UBA130);
                        }
                        else
                        {
                            usageMsg();
                            return -1;
                        }
                    }
                    else if ( *tmp == '4' )
                    {
                        tmp++;
                        if ( *tmp == '0' )
                        {
                            SetUBAVersion (UBA140);
                        }
                        else
                        {
                            usageMsg();
                            return -1;
                        }
                    }
                    else if ( *tmp == '5' )
                    {
                        tmp++;
                        if ( *tmp == '0' )
                        {
                            SetUBAVersion (UBA150);
                        }
                        else if ( *tmp == '1' )
                        {
                            SetUBAVersion (UBA151);
                        }
                        else
                        {
                            usageMsg();
                            return -1;
                        }
                    }
                    else if ( *tmp == '6' )
                    {
                        tmp++;
                        if ( *tmp == '0' )
                        {
                            SetUBAVersion (UBA160);
                        }
                        else
                        {
                            usageMsg();
                            return -1;
                        }
                    }
                    else
                    {
                        usageMsg();
                        return -1;
                    }
                }
                else
                {
                    usageMsg();
                    return -1;
                }
                break;
            case 'p' :
                if ( numargs > 1 )
                {
                    strncpy (argstring, *++argv, MAXARGLEN );
                    /* Truncate if necessary */
                    argstring[MAXARGLEN - 1] = '\0';
                    numargs--;
                    strcpy ( datapath, argstring );
                }
                else
                {
                    usageMsg();
                    return -1 ;
                }
                break;
            case 'x' :
                SetUBAVersion ( UBA63 );
                break;
            case 'v' :
                versionMsg();
                return 0;
            /* The -y command line arg is a temporary hack. */
            case 'y' :
                TraceOn ( Trace14 );
                break;
            case 'c' :
                continueOnTestErr = 1;
                break;
            case 'z' :
                staticTest = 1;
                break;
            case '?' :
            case 'h' :
                usageMsg();
                return 0;
            default:
                usageMsg();
                return -1;
            }
        }
        else if ( !foundFile )
        {
            strncpy ( inputFileName, argstring, MAXARGLEN );
            foundFile = 1;
        }
        else
        {
            usageMsg();
            return -1;
        }
    }
/*
 * Default empty parameter1 to input file name as BidiRefTest.txt.
 */
    if ( !foundFile )
    {
        strcpy ( inputFileName, infile );
    }

/*
 * Detect whether the input for test set data is BidiTest.txt.
 * If so, reset the fileFormat to FORMAT_B. For a simple test,
 * just check whether "BidiTest" occurs anywhere in the
 * inputFileName string, because we aren't actually parsing
 * fully-qualified paths here.
 */
    tmp = strstr ( inputFileName, "BidiTest" );
    if ( tmp != NULL )
    {
        /* 
         * TBD: Further checking to ensure name meets
         * qualification for FORMAT_B.
         */
        SetFileFormat ( FORMAT_B );
    } 

    return ( 1 );
}

/***********************************************************/

int main ( int argc, char *argv[] )
{
int rc;

    rc = processArguments ( argc, argv );
    if ( rc != 1 )
    {
        if ( rc < 0 )
        {
            br_ErrPrint ( "Error in processing command line arguments.\n" );           
        }
        return ( BR_INITERR );
    }

    /*
     * Set any individual trace flags based on overall debug levels.
     */

    SetInitialTraceFlags();

    if ( Trace ( Trace2 ) )
    {
        if ( staticTest )
        {
            printf ( "Trace: Starting bidiref, UBA version=%s, with static input.\n",
                GetUBAVersionStr() );
        }
        else
        {
            printf ( "Trace: Starting bidiref, UBA version=%s, input file=\"%s\"\n", 
                GetUBAVersionStr(), inputFileName );
        }
    }

    /* 
     * Initialize property tables from UnicodeData.txt and BidiBrackets.txt.
     */

    rc = br_InitTable ( GetUBAVersion(), datapath );
    if ( rc != 1 )
    {
        br_ErrPrint ( "Error in processing property tables.\n" );
        return ( BR_INITERR );
    }

    if ( staticTest )
    {
        rc = br_RunStaticTest();
    }
    else
    {
        rc = br_RunFileTests ( GetUBAVersion(), datapath, inputFileName );
    }

    return ( rc );
}

