// $ANTLR 3.1 /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g 2008-09-25 19:01:14


package org.oxford.comlab.perfectref.parser;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.antlr.runtime.BitSet;
import org.antlr.runtime.NoViableAltException;
import org.antlr.runtime.Parser;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.RecognizerSharedState;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenStream;
import org.oxford.comlab.perfectref.rewriter.Clause;
import org.oxford.comlab.perfectref.rewriter.Term;
import org.oxford.comlab.perfectref.rewriter.TermFactory;

public class QueriesParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "ALPHAVAR", "NUMBER", "ALPHA", "INT", "CHAR", "WS", "'<-'", "','", "'Q'", "'('", "')'", "'?'"
    };
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

    // delegates
    // delegators


        public QueriesParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public QueriesParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);

        }


    @Override
	public String[] getTokenNames() { return QueriesParser.tokenNames; }
    @Override
	public String getGrammarFileName() { return "/Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g"; }



    private TermFactory termFactory = new TermFactory();
    private ArrayList<Term> headAtoms = new ArrayList<Term>();
    private ArrayList<Term>	bodyAtoms = new ArrayList<Term>();
    private ArrayList<Term>	headVariables = new ArrayList<Term>();
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

    boolean error1 = false;

    public void resetErrorFlag() {
    	error1 = false;
    }

    public boolean getErrorFlag() {
    	return error1;
    }

    public Clause getQuery() {

    	Term[] hvariables = new Term[headVariables.size()];

    	for(int i=0; i< headVariables.size(); i++)
			hvariables[i] = headVariables.get(i);

    	headAtoms.add(termFactory.getFunctionalTerm("Q",hvariables));

    	Term[] hAtoms = new Term[headAtoms.size()];

    	for(int i=0; i< headAtoms.size(); i++)
			hAtoms[i] = headAtoms.get(i);

    	Term[] bAtoms = new Term[bodyAtoms.size()];

    	for(int i=0; i< bodyAtoms.size(); i++)
			bAtoms[i] = bodyAtoms.get(i);

    	return new Clause(bAtoms, hAtoms[0]);
    }



    // $ANTLR start "parse"
    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:90:1: parse returns [boolean value] : clause EOF ;
    public final boolean parse() throws RecognitionException {
        boolean value = false;

        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:91:1: ( clause EOF )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:91:3: clause EOF
            {
            pushFollow(FOLLOW_clause_in_parse47);
            clause();

            state._fsp--;

            match(input,EOF,FOLLOW_EOF_in_parse49);

            		value = !error1;


            }

        }
        catch (RecognitionException ex) {

            //		reportError(ex);
            		value = false;
            		throw ex;

        }
        finally {
        }
        return value;
    }
    // $ANTLR end "parse"


    // $ANTLR start "clause"
    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:101:1: clause : headAtom '<-' bodyAtom ( ',' bodyAtom )* ;
    public final void clause() throws RecognitionException {
        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:102:2: ( headAtom '<-' bodyAtom ( ',' bodyAtom )* )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:102:4: headAtom '<-' bodyAtom ( ',' bodyAtom )*
            {
            pushFollow(FOLLOW_headAtom_in_clause70);
            headAtom();

            state._fsp--;

            match(input,10,FOLLOW_10_in_clause72);
            pushFollow(FOLLOW_bodyAtom_in_clause74);
            bodyAtom();

            state._fsp--;

            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:102:27: ( ',' bodyAtom )*
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( (LA1_0==11) )
					alt1=1;


                switch (alt1) {
            	case 1 :
            	    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:102:28: ',' bodyAtom
            	    {
            	    match(input,11,FOLLOW_11_in_clause77);
            	    pushFollow(FOLLOW_bodyAtom_in_clause79);
            	    bodyAtom();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop1;
                }
            } while (true);


            }

        }
        catch (RecognitionException ex) {

            		//reportError(ex);
            		error1 = true;
            		throw ex;

        }
        finally {
        }
        return ;
    }
    // $ANTLR end "clause"


    // $ANTLR start "headAtom"
    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:109:1: headAtom : 'Q' '(' distinguishedVar ( ',' distinguishedVar )* ')' ;
    public final void headAtom() throws RecognitionException {
        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:110:2: ( 'Q' '(' distinguishedVar ( ',' distinguishedVar )* ')' )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:110:4: 'Q' '(' distinguishedVar ( ',' distinguishedVar )* ')'
            {
            match(input,12,FOLLOW_12_in_headAtom101);
            match(input,13,FOLLOW_13_in_headAtom103);
            pushFollow(FOLLOW_distinguishedVar_in_headAtom105);
            distinguishedVar();

            state._fsp--;

            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:110:29: ( ',' distinguishedVar )*
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( (LA2_0==11) )
					alt2=1;


                switch (alt2) {
            	case 1 :
            	    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:110:30: ',' distinguishedVar
            	    {
            	    match(input,11,FOLLOW_11_in_headAtom108);
            	    pushFollow(FOLLOW_distinguishedVar_in_headAtom110);
            	    distinguishedVar();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop2;
                }
            } while (true);

            match(input,14,FOLLOW_14_in_headAtom114);

            }

        }
        catch (RecognitionException ex) {

            		//reportError(ex);
            		error1 = true;
            		throw ex;

        }
        finally {
        }
        return ;
    }
    // $ANTLR end "headAtom"


    // $ANTLR start "bodyAtom"
    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:117:1: bodyAtom : ( unaryAtom | binaryAtom );
    public final void bodyAtom() throws RecognitionException {
        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:118:2: ( unaryAtom | binaryAtom )
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0==ALPHAVAR) ) {
                int LA3_1 = input.LA(2);

                if ( (LA3_1==13) ) {
                    int LA3_2 = input.LA(3);

                    if ( (LA3_2==15) ) {
                        int LA3_3 = input.LA(4);

                        if ( (LA3_3==NUMBER) ) {
                            int LA3_4 = input.LA(5);

                            if ( (LA3_4==11) )
								alt3=2;
							else if ( (LA3_4==14) )
								alt3=1;
							else {
                                NoViableAltException nvae =
                                    new NoViableAltException("", 3, 4, input);

                                throw nvae;
                            }
                        }
                        else {
                            NoViableAltException nvae =
                                new NoViableAltException("", 3, 3, input);

                            throw nvae;
                        }
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("", 3, 2, input);

                        throw nvae;
                    }
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 3, 1, input);

                    throw nvae;
                }
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;
            }
            switch (alt3) {
                case 1 :
                    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:118:4: unaryAtom
                    {
                    pushFollow(FOLLOW_unaryAtom_in_bodyAtom136);
                    unaryAtom();

                    state._fsp--;


                    }
                    break;
                case 2 :
                    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:119:5: binaryAtom
                    {
                    pushFollow(FOLLOW_binaryAtom_in_bodyAtom142);
                    binaryAtom();

                    state._fsp--;


                    }
                    break;

            }
        }
        catch (RecognitionException ex) {

            		//reportError(ex);
            		error1 = true;
            		throw ex;

        }
        finally {
        }
        return ;
    }
    // $ANTLR end "bodyAtom"


    // $ANTLR start "unaryAtom"
    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:128:1: unaryAtom : predicate '(' var ')' ;
    public final void unaryAtom() throws RecognitionException {
        String predicate1 = null;

        Term var2 = null;


        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:129:2: ( predicate '(' var ')' )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:129:4: predicate '(' var ')'
            {
            pushFollow(FOLLOW_predicate_in_unaryAtom162);
            predicate1=predicate();

            state._fsp--;

            match(input,13,FOLLOW_13_in_unaryAtom164);
            pushFollow(FOLLOW_var_in_unaryAtom166);
            var2=var();

            state._fsp--;

            match(input,14,FOLLOW_14_in_unaryAtom168);


            		Term atom = termFactory.getFunctionalTerm(predicate1, var2);
            		bodyAtoms.add(atom);


            }

        }
        catch (RecognitionException ex) {

            		//reportError(ex);
            		error1 = true;
            		throw ex;
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "unaryAtom"


    // $ANTLR start "binaryAtom"
    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:140:1: binaryAtom : predicate '(' var1 ',' var2 ')' ;
    public final void binaryAtom() throws RecognitionException {
        String predicate3 = null;

        Term var14 = null;

        Term var25 = null;


        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:141:2: ( predicate '(' var1 ',' var2 ')' )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:141:4: predicate '(' var1 ',' var2 ')'
            {
            pushFollow(FOLLOW_predicate_in_binaryAtom189);
            predicate3=predicate();

            state._fsp--;

            match(input,13,FOLLOW_13_in_binaryAtom191);
            pushFollow(FOLLOW_var1_in_binaryAtom193);
            var14=var1();

            state._fsp--;

            match(input,11,FOLLOW_11_in_binaryAtom195);
            pushFollow(FOLLOW_var2_in_binaryAtom197);
            var25=var2();

            state._fsp--;

            match(input,14,FOLLOW_14_in_binaryAtom199);


            		Term atom = termFactory.getFunctionalTerm(predicate3, var14, var25);
            		bodyAtoms.add(atom);


            }

        }
        catch (RecognitionException ex) {

            		//reportError(ex);
            		error1 = true;
            		throw ex;

        }
        finally {
        }
        return ;
    }
    // $ANTLR end "binaryAtom"


    // $ANTLR start "distinguishedVar"
    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:152:1: distinguishedVar : '?' number ;
    public final void distinguishedVar() throws RecognitionException {
        String number6 = null;


        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:153:2: ( '?' number )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:153:4: '?' number
            {
            match(input,15,FOLLOW_15_in_distinguishedVar219);
            pushFollow(FOLLOW_number_in_distinguishedVar221);
            number6=number();

            state._fsp--;



            		Integer index = new Integer(number6);
                        	Term var = termFactory.getVariable(index.intValue());
            		headVariables.add(var);


            }

        }
        catch (RecognitionException ex) {

            		//reportError(ex);
            		error1 = true;
            		throw ex;

        }
        finally {
        }
        return ;
    }
    // $ANTLR end "distinguishedVar"


    // $ANTLR start "var"
    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:166:1: var returns [Term value] : '?' number ;
    public final Term var() throws RecognitionException {
        Term value = null;

        String number7 = null;


        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:167:2: ( '?' number )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:167:4: '?' number
            {
            match(input,15,FOLLOW_15_in_var247);
            pushFollow(FOLLOW_number_in_var249);
            number7=number();

            state._fsp--;



            		Integer index = new Integer(number7);
                        	Term var = termFactory.getVariable(index.intValue());
            		value = var;


            }

        }
        catch (RecognitionException ex) {

            		//reportError(ex);
            		error1 = true;
            		throw ex;

        }
        finally {
        }
        return value;
    }
    // $ANTLR end "var"


    // $ANTLR start "var1"
    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:179:1: var1 returns [Term value] : var ;
    public final Term var1() throws RecognitionException {
        Term value = null;

        Term var8 = null;


        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:180:2: ( var )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:180:4: var
            {
            pushFollow(FOLLOW_var_in_var1274);
            var8=var();

            state._fsp--;


            		value = var8;


            }

        }
        catch (RecognitionException ex) {

            		//reportError(ex);
            		error1 = true;
            		throw ex;

        }
        finally {
        }
        return value;
    }
    // $ANTLR end "var1"


    // $ANTLR start "var2"
    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:190:1: var2 returns [Term value] : var ;
    public final Term var2() throws RecognitionException {
        Term value = null;

        Term var9 = null;


        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:191:2: ( var )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:191:4: var
            {
            pushFollow(FOLLOW_var_in_var2301);
            var9=var();

            state._fsp--;


            		value = var9;


            }

        }
        catch (RecognitionException ex) {

            		//reportError(ex);
            		error1 = true;
            		throw ex;

        }
        finally {
        }
        return value;
    }
    // $ANTLR end "var2"


    // $ANTLR start "predicate"
    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:201:1: predicate returns [String value] : ALPHAVAR ;
    public final String predicate() throws RecognitionException {
        String value = null;

        Token ALPHAVAR10=null;

        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:202:2: ( ALPHAVAR )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:202:4: ALPHAVAR
            {
            ALPHAVAR10=(Token)match(input,ALPHAVAR,FOLLOW_ALPHAVAR_in_predicate329);
            value = (ALPHAVAR10!=null?ALPHAVAR10.getText():null);

            }

        }
        catch (RecognitionException ex) {

            		//reportError(ex);
            		error1 = true;
            		throw ex;

        }
        finally {
        }
        return value;
    }
    // $ANTLR end "predicate"


    // $ANTLR start "number"
    // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:209:1: number returns [String value] : NUMBER ;
    public final String number() throws RecognitionException {
        String value = null;

        Token NUMBER11=null;

        try {
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:210:2: ( NUMBER )
            // /Users/hekanibru/Documents/DPhil/Prototype/Grammar/ReQuIEMQueries.g:210:4: NUMBER
            {
            NUMBER11=(Token)match(input,NUMBER,FOLLOW_NUMBER_in_number354);
            value = (NUMBER11!=null?NUMBER11.getText():null);

            }

        }
        catch (RecognitionException ex) {

            		//reportError(ex);
            		error1 = true;
            		throw ex;

        }
        finally {
        }
        return value;
    }
    // $ANTLR end "number"

    // Delegated rules




    public static final BitSet FOLLOW_clause_in_parse47 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_parse49 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_headAtom_in_clause70 = new BitSet(new long[]{0x0000000000000400L});
    public static final BitSet FOLLOW_10_in_clause72 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_bodyAtom_in_clause74 = new BitSet(new long[]{0x0000000000000802L});
    public static final BitSet FOLLOW_11_in_clause77 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_bodyAtom_in_clause79 = new BitSet(new long[]{0x0000000000000802L});
    public static final BitSet FOLLOW_12_in_headAtom101 = new BitSet(new long[]{0x0000000000002000L});
    public static final BitSet FOLLOW_13_in_headAtom103 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_distinguishedVar_in_headAtom105 = new BitSet(new long[]{0x0000000000004800L});
    public static final BitSet FOLLOW_11_in_headAtom108 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_distinguishedVar_in_headAtom110 = new BitSet(new long[]{0x0000000000004800L});
    public static final BitSet FOLLOW_14_in_headAtom114 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_unaryAtom_in_bodyAtom136 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_binaryAtom_in_bodyAtom142 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_predicate_in_unaryAtom162 = new BitSet(new long[]{0x0000000000002000L});
    public static final BitSet FOLLOW_13_in_unaryAtom164 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_var_in_unaryAtom166 = new BitSet(new long[]{0x0000000000004000L});
    public static final BitSet FOLLOW_14_in_unaryAtom168 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_predicate_in_binaryAtom189 = new BitSet(new long[]{0x0000000000002000L});
    public static final BitSet FOLLOW_13_in_binaryAtom191 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_var1_in_binaryAtom193 = new BitSet(new long[]{0x0000000000000800L});
    public static final BitSet FOLLOW_11_in_binaryAtom195 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_var2_in_binaryAtom197 = new BitSet(new long[]{0x0000000000004000L});
    public static final BitSet FOLLOW_14_in_binaryAtom199 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_15_in_distinguishedVar219 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_number_in_distinguishedVar221 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_15_in_var247 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_number_in_var249 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_var_in_var1274 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_var_in_var2301 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ALPHAVAR_in_predicate329 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_NUMBER_in_number354 = new BitSet(new long[]{0x0000000000000002L});

}