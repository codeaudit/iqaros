// $ANTLR 3.1 /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g 2008-09-25 19:01:14


package org.oxford.comlab.perfectref.parser;
import java.util.LinkedList;
import java.util.List;

import org.antlr.runtime.BaseRecognizer;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.DFA;
import org.antlr.runtime.EarlyExitException;
import org.antlr.runtime.Lexer;
import org.antlr.runtime.MismatchedSetException;
import org.antlr.runtime.NoViableAltException;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.RecognizerSharedState;

public class QueriesLexer extends Lexer {
    public static final int WS=9;
    public static final int T__15=15;
    public static final int T__12=12;
    public static final int T__11=11;
    public static final int T__14=14;
    public static final int T__13=13;
    public static final int T__10=10;
    public static final int NUMBER=5;
    public static final int CHAR=8;
    public static final int ALPHAVAR=4;
    public static final int INT=7;
    public static final int EOF=-1;
    public static final int ALPHA=6;


        private List<String> errors = new LinkedList<String>();

        @Override
		public void displayRecognitionError(String[] tokenNames,RecognitionException e) {
            String hdr = getErrorHeader(e);
            String msg = getErrorMessage(e, tokenNames);
            errors.add(hdr + " " + msg);
        }

        public List<String> getErrors() {
            return errors;
        }


    // delegates
    // delegators

    public QueriesLexer() {;}
    public QueriesLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public QueriesLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);

    }
    @Override
	public String getGrammarFileName() { return "/Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g"; }

    // $ANTLR start "T__10"
    public final void mT__10() throws RecognitionException {
        try {
            int _type = T__10;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:24:7: ( '<-' )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:24:9: '<-'
            {
            match("<-");


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__10"

    // $ANTLR start "T__11"
    public final void mT__11() throws RecognitionException {
        try {
            int _type = T__11;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:25:7: ( ',' )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:25:9: ','
            {
            match(',');

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__11"

    // $ANTLR start "T__12"
    public final void mT__12() throws RecognitionException {
        try {
            int _type = T__12;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:26:7: ( 'Q' )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:26:9: 'Q'
            {
            match('Q');

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__12"

    // $ANTLR start "T__13"
    public final void mT__13() throws RecognitionException {
        try {
            int _type = T__13;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:27:7: ( '(' )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:27:9: '('
            {
            match('(');

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__13"

    // $ANTLR start "T__14"
    public final void mT__14() throws RecognitionException {
        try {
            int _type = T__14;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:28:7: ( ')' )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:28:9: ')'
            {
            match(')');

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__14"

    // $ANTLR start "T__15"
    public final void mT__15() throws RecognitionException {
        try {
            int _type = T__15;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:29:7: ( '?' )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:29:9: '?'
            {
            match('?');

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__15"

    // $ANTLR start "NUMBER"
    public final void mNUMBER() throws RecognitionException {
        try {
            int _type = NUMBER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:217:9: ( ( '0' .. '9' )+ )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:217:11: ( '0' .. '9' )+
            {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:217:11: ( '0' .. '9' )+
            int cnt1=0;
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( ((LA1_0>='0' && LA1_0<='9')) )
					alt1=1;


                switch (alt1) {
            	case 1 :
            	    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:217:11: '0' .. '9'
            	    {
            	    matchRange('0','9');

            	    }
            	    break;

            	default :
            	    if ( cnt1 >= 1 ) break loop1;
                        EarlyExitException eee =
                            new EarlyExitException(1, input);
                        throw eee;
                }
                cnt1++;
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "NUMBER"

    // $ANTLR start "ALPHAVAR"
    public final void mALPHAVAR() throws RecognitionException {
        try {
            int _type = ALPHAVAR;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:219:11: ( ( ALPHA | INT | CHAR )+ )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:219:15: ( ALPHA | INT | CHAR )+
            {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:219:15: ( ALPHA | INT | CHAR )+
            int cnt2=0;
            loop2:
            do {
                int alt2=4;
                switch ( input.LA(1) ) {
                case 'A':
                case 'B':
                case 'C':
                case 'D':
                case 'E':
                case 'F':
                case 'G':
                case 'H':
                case 'I':
                case 'J':
                case 'K':
                case 'L':
                case 'M':
                case 'N':
                case 'O':
                case 'P':
                case 'Q':
                case 'R':
                case 'S':
                case 'T':
                case 'U':
                case 'V':
                case 'W':
                case 'X':
                case 'Y':
                case 'Z':
                case 'a':
                case 'b':
                case 'c':
                case 'd':
                case 'e':
                case 'f':
                case 'g':
                case 'h':
                case 'i':
                case 'j':
                case 'k':
                case 'l':
                case 'm':
                case 'n':
                case 'o':
                case 'p':
                case 'q':
                case 'r':
                case 's':
                case 't':
                case 'u':
                case 'v':
                case 'w':
                case 'x':
                case 'y':
                case 'z':
                    {
                    alt2=1;
                    }
                    break;
                case '0':
                case '1':
                case '2':
                case '3':
                case '4':
                case '5':
                case '6':
                case '7':
                case '8':
                case '9':
                    {
                    alt2=2;
                    }
                    break;
                case '!':
                case '#':
                case '%':
                case '&':
                case '*':
                case '+':
                case '-':
                case '.':
                case ':':
                case '=':
                case '@':
                case '_':
                    {
                    alt2=3;
                    }
                    break;

                }

                switch (alt2) {
            	case 1 :
            	    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:219:16: ALPHA
            	    {
            	    mALPHA();

            	    }
            	    break;
            	case 2 :
            	    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:219:24: INT
            	    {
            	    mINT();

            	    }
            	    break;
            	case 3 :
            	    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:219:30: CHAR
            	    {
            	    mCHAR();

            	    }
            	    break;

            	default :
            	    if ( cnt2 >= 1 ) break loop2;
                        EarlyExitException eee =
                            new EarlyExitException(2, input);
                        throw eee;
                }
                cnt2++;
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ALPHAVAR"

    // $ANTLR start "CHAR"
    public final void mCHAR() throws RecognitionException {
        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:222:8: ( ( '_' | '-' | '*' | '&' | '@' | '!' | '#' | '%' | '+' | '=' | ':' | '.' ) )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:222:10: ( '_' | '-' | '*' | '&' | '@' | '!' | '#' | '%' | '+' | '=' | ':' | '.' )
            {
            if ( input.LA(1)=='!'||input.LA(1)=='#'||(input.LA(1)>='%' && input.LA(1)<='&')||(input.LA(1)>='*' && input.LA(1)<='+')||(input.LA(1)>='-' && input.LA(1)<='.')||input.LA(1)==':'||input.LA(1)=='='||input.LA(1)=='@'||input.LA(1)=='_' )
				input.consume();
			else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}


            }

        }
        finally {
        }
    }
    // $ANTLR end "CHAR"

    // $ANTLR start "ALPHA"
    public final void mALPHA() throws RecognitionException {
        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:225:9: ( ( 'a' .. 'z' | 'A' .. 'Z' )+ )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:225:13: ( 'a' .. 'z' | 'A' .. 'Z' )+
            {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:225:13: ( 'a' .. 'z' | 'A' .. 'Z' )+
            int cnt3=0;
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( ((LA3_0>='A' && LA3_0<='Z')||(LA3_0>='a' && LA3_0<='z')) )
					alt3=1;


                switch (alt3) {
            	case 1 :
            	    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:
            	    {
            	    if ( (input.LA(1)>='A' && input.LA(1)<='Z')||(input.LA(1)>='a' && input.LA(1)<='z') )
						input.consume();
					else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    if ( cnt3 >= 1 ) break loop3;
                        EarlyExitException eee =
                            new EarlyExitException(3, input);
                        throw eee;
                }
                cnt3++;
            } while (true);


            }

        }
        finally {
        }
    }
    // $ANTLR end "ALPHA"

    // $ANTLR start "INT"
    public final void mINT() throws RecognitionException {
        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:228:7: ( ( '0' .. '9' )+ )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:228:11: ( '0' .. '9' )+
            {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:228:11: ( '0' .. '9' )+
            int cnt4=0;
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( ((LA4_0>='0' && LA4_0<='9')) )
					alt4=1;


                switch (alt4) {
            	case 1 :
            	    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:228:11: '0' .. '9'
            	    {
            	    matchRange('0','9');

            	    }
            	    break;

            	default :
            	    if ( cnt4 >= 1 ) break loop4;
                        EarlyExitException eee =
                            new EarlyExitException(4, input);
                        throw eee;
                }
                cnt4++;
            } while (true);


            }

        }
        finally {
        }
    }
    // $ANTLR end "INT"

    // $ANTLR start "WS"
    public final void mWS() throws RecognitionException {
        try {
            int _type = WS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:230:7: ( ( ' ' | '\\t' | ( '\\r' | '\\r\\n' ) )+ )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:230:11: ( ' ' | '\\t' | ( '\\r' | '\\r\\n' ) )+
            {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:230:11: ( ' ' | '\\t' | ( '\\r' | '\\r\\n' ) )+
            int cnt6=0;
            loop6:
            do {
                int alt6=4;
                switch ( input.LA(1) ) {
                case ' ':
                    {
                    alt6=1;
                    }
                    break;
                case '\t':
                    {
                    alt6=2;
                    }
                    break;
                case '\r':
                    {
                    alt6=3;
                    }
                    break;

                }

                switch (alt6) {
            	case 1 :
            	    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:230:12: ' '
            	    {
            	    match(' ');

            	    }
            	    break;
            	case 2 :
            	    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:230:16: '\\t'
            	    {
            	    match('\t');

            	    }
            	    break;
            	case 3 :
            	    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:230:21: ( '\\r' | '\\r\\n' )
            	    {
            	    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:230:21: ( '\\r' | '\\r\\n' )
            	    int alt5=2;
            	    int LA5_0 = input.LA(1);

            	    if ( (LA5_0=='\r') ) {
            	        int LA5_1 = input.LA(2);

            	        if ( (LA5_1=='\n') )
							alt5=2;
						else
							alt5=1;
            	    }
            	    else {
            	        NoViableAltException nvae =
            	            new NoViableAltException("", 5, 0, input);

            	        throw nvae;
            	    }
            	    switch (alt5) {
            	        case 1 :
            	            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:230:22: '\\r'
            	            {
            	            match('\r');

            	            }
            	            break;
            	        case 2 :
            	            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:230:27: '\\r\\n'
            	            {
            	            match("\r\n");


            	            }
            	            break;

            	    }


            	    }
            	    break;

            	default :
            	    if ( cnt6 >= 1 ) break loop6;
                        EarlyExitException eee =
                            new EarlyExitException(6, input);
                        throw eee;
                }
                cnt6++;
            } while (true);

            skip();

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "WS"

    @Override
	public void mTokens() throws RecognitionException {
        // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:1:8: ( T__10 | T__11 | T__12 | T__13 | T__14 | T__15 | NUMBER | ALPHAVAR | WS )
        int alt7=9;
        alt7 = dfa7.predict(input);
        switch (alt7) {
            case 1 :
                // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:1:10: T__10
                {
                mT__10();

                }
                break;
            case 2 :
                // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:1:16: T__11
                {
                mT__11();

                }
                break;
            case 3 :
                // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:1:22: T__12
                {
                mT__12();

                }
                break;
            case 4 :
                // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:1:28: T__13
                {
                mT__13();

                }
                break;
            case 5 :
                // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:1:34: T__14
                {
                mT__14();

                }
                break;
            case 6 :
                // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:1:40: T__15
                {
                mT__15();

                }
                break;
            case 7 :
                // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:1:46: NUMBER
                {
                mNUMBER();

                }
                break;
            case 8 :
                // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:1:53: ALPHAVAR
                {
                mALPHAVAR();

                }
                break;
            case 9 :
                // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:1:62: WS
                {
                mWS();

                }
                break;

        }

    }


    protected DFA7 dfa7 = new DFA7(this);
    static final String DFA7_eotS =
        "\3\uffff\1\12\3\uffff\1\13\4\uffff";
    static final String DFA7_eofS =
        "\14\uffff";
    static final String DFA7_minS =
        "\1\11\2\uffff\1\41\3\uffff\1\41\4\uffff";
    static final String DFA7_maxS =
        "\1\172\2\uffff\1\172\3\uffff\1\172\4\uffff";
    static final String DFA7_acceptS =
        "\1\uffff\1\1\1\2\1\uffff\1\4\1\5\1\6\1\uffff\1\10\1\11\1\3\1\7";
    static final String DFA7_specialS =
        "\14\uffff}>";
    static final String[] DFA7_transitionS = {
            "\1\11\3\uffff\1\11\22\uffff\1\11\1\10\1\uffff\1\10\1\uffff\2"+
            "\10\1\uffff\1\4\1\5\2\10\1\2\2\10\1\uffff\12\7\1\10\1\uffff"+
            "\1\1\1\10\1\uffff\1\6\21\10\1\3\11\10\4\uffff\1\10\1\uffff\32"+
            "\10",
            "",
            "",
            "\1\10\1\uffff\1\10\1\uffff\2\10\3\uffff\2\10\1\uffff\2\10\1"+
            "\uffff\13\10\2\uffff\1\10\2\uffff\33\10\4\uffff\1\10\1\uffff"+
            "\32\10",
            "",
            "",
            "",
            "\1\10\1\uffff\1\10\1\uffff\2\10\3\uffff\2\10\1\uffff\2\10\1"+
            "\uffff\12\7\1\10\2\uffff\1\10\2\uffff\33\10\4\uffff\1\10\1\uffff"+
            "\32\10",
            "",
            "",
            "",
            ""
    };

    static final short[] DFA7_eot = DFA.unpackEncodedString(DFA7_eotS);
    static final short[] DFA7_eof = DFA.unpackEncodedString(DFA7_eofS);
    static final char[] DFA7_min = DFA.unpackEncodedStringToUnsignedChars(DFA7_minS);
    static final char[] DFA7_max = DFA.unpackEncodedStringToUnsignedChars(DFA7_maxS);
    static final short[] DFA7_accept = DFA.unpackEncodedString(DFA7_acceptS);
    static final short[] DFA7_special = DFA.unpackEncodedString(DFA7_specialS);
    static final short[][] DFA7_transition;

    static {
        int numStates = DFA7_transitionS.length;
        DFA7_transition = new short[numStates][];
        for (int i=0; i<numStates; i++)
			DFA7_transition[i] = DFA.unpackEncodedString(DFA7_transitionS[i]);
    }

    class DFA7 extends DFA {

        public DFA7(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 7;
            this.eot = DFA7_eot;
            this.eof = DFA7_eof;
            this.min = DFA7_min;
            this.max = DFA7_max;
            this.accept = DFA7_accept;
            this.special = DFA7_special;
            this.transition = DFA7_transition;
        }
        @Override
		public String getDescription() {
            return "1:1: Tokens : ( T__10 | T__11 | T__12 | T__13 | T__14 | T__15 | NUMBER | ALPHAVAR | WS );";
        }
    }


}