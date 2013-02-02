package edu.ntua.image.refinement;
//package edu.ntua.image.Refine;
//
//import java.util.ArrayList;
//import java.util.Collections;
//import java.util.HashSet;
//import java.util.Set;
//import java.util.Stack;
//
//import org.oxford.comlab.perfectref.rewriter.Clause;
//import org.oxford.comlab.perfectref.rewriter.PI;
//import org.oxford.comlab.perfectref.rewriter.Saturator;
//import org.oxford.comlab.perfectref.rewriter.Term;
//import org.oxford.comlab.perfectref.rewriter.TermFactory;
//import org.oxford.comlab.perfectref.rewriter.Variable;
//
//import edu.ntua.image.Tree.Node;
//import edu.ntua.image.Tree.Tree;
//
//public class Refine_Refactoring {
//
//	private static final TermFactory m_termFactory = new TermFactory();
//	private static final Saturator m_saturator = new Saturator(m_termFactory);
//
//	protected ArrayList<String> m_clausesCanonicals = new ArrayList<String>();
//	protected ArrayList<Node<Clause>> m_workedOffClauses = new ArrayList<Node<Clause>>();;
//
//	private Set<Clause> m_activeSubsumers = new HashSet<Clause>();
//
//	public Set<Clause> computeRewritingIncrementally( Tree<Clause> tree , Term extraAtom , ArrayList<PI> pis ) {
//
//		Term clauseHead = tree.getRootElement().getNodeLabel().getHead();
//		Set<Clause> result = new HashSet<Clause>();
//		Set<Term> rewOfNewAtom = rewAtom( extraAtom, pis );
//
//		Stack<Node<Clause>> stack = new Stack<Node<Clause>>();
//		stack.push( tree.getRootElement() );
//		int iterations = 0;
//		while (!stack.isEmpty()) {
//			Node<Clause> currentNode = stack.pop();
//			Clause currentClause = currentNode.getNodeLabel();
//
//			ArrayList<Variable> currentClauseVars = currentClause.getVariables();
//			iterations++;
//			if( m_workedOffClauses.contains(currentNode))
//				continue;
//			m_workedOffClauses.add(currentNode);
//			if (!isEligibleForProcessing( currentClauseVars, extraAtom.getArguments()))
//				continue;
//			boolean clauseRefined = refineClause(currentNode,rewOfNewAtom,clauseHead,result);
//			if (clauseRefined)
//				stack.addAll( currentNode.getChildren() );
//		}
//		System.out.println( "Refinement algorithm performed " + iterations + " iterations" );
//		return result;
//	}
//
//	private boolean refineClause(Node<Clause> currentNode, Set<Term> rewOfNewAtom, Term clauseHead, Set<Clause> result){
//		Clause currentClause = currentNode.getNodeLabel();
//		ArrayList<Variable> currentClauseVars = currentClause.getVariables();
//		Term[] currentClauseBody = currentClause.getBody();
//		boolean clauseRefined = false;
//		Set<Clause> tempResult = new HashSet<Clause>();
//		boolean isEligibleForRefinement = isEligibleForRefinement(currentClause);
//
//		for (Term subsTerm : rewOfNewAtom) {
//
//			Term[] subsTermArgs = subsTerm.getArguments();
//			int subsTermArity = subsTerm.getArity();
//
//			if (subsTermArity == 1 && currentClauseVars.contains( subsTermArgs[0] )) {
//				if ( conceptAppearsInBodyOf( subsTerm , currentClauseBody ) ) {
//					result.addAll( getNonRedundantChildrenOf( currentNode ) );
//					return false;
//				}
//				else
//					if (isEligibleForRefinement && !subsTerm.getName().contains("AUX-")) {
//						tempResult.add( createNewQueriesWithExtraAtom( subsTerm, currentClauseBody, clauseHead) );
////						m_activeClauses.add(currentClause);
//						clauseRefined = true;
//					}
//			}
//			else if (subsTermArity == 2 && (currentClauseVars.contains(subsTermArgs[0]) || currentClauseVars.contains(subsTermArgs[1]))) {
//				if (roleAppearsInBodyOf(subsTerm, currentClause)) {
//					result.addAll( getNonRedundantChildrenOf( currentNode ) );
//					return false;
//				}
//				else
//					if (isEligibleForRefinement && !subsTerm.getName().contains("AUX-")) {
//						tempResult.add( createNewQueriesWithExtraAtom( subsTerm, currentClauseBody, clauseHead) );
////						m_activeClauses.add(currentClause);
//						clauseRefined = true;
//					}
//			}
//		}
//		if (clauseRefined)
//			result.addAll( tempResult );
//		return clauseRefined;
//	}
//
//	private boolean isEligibleForProcessing(ArrayList<Variable> variables, Term[] arguments) {
//		for (Term term : arguments)
//			if (variables.contains(term))
//				return true;
//		return false;
//	}
//
//	private boolean isEligibleForRefinement(Clause currentClause) {
//		if (containsAUX(currentClause))
//			return false;
//		if (m_activeSubsumers.contains(currentClause.getSubsumer()))
//			return false;
//		return true;
//	}
//
//	private Clause createNewQueriesWithExtraAtom( Term extraAtom , Term[] body, Term head) {
//
//		Term[] newBody = new Term[body.length + 1];
//		for (int i=0 ; i<body.length ; i++)
//			newBody[i] = body[i];
//		newBody[body.length] = extraAtom;
//
//		return new Clause( newBody , head );
//	}
//
//	private Set<Clause> getNonRedundantChildrenOf( Node<Clause> node ) {
//		Set<Clause> result = new HashSet<Clause>();
//		Stack<Node<Clause>> stack = new Stack<Node<Clause>>();
//		stack.push(node);
//		while (!stack.isEmpty()) {
//			Node<Clause> currentNode = stack.pop();
//			Clause clause = currentNode.getNodeLabel();
//
////			if ( !containsAUX( clause ) && clause.getSubsumer()==null ) {
////			if ( !containsAUX( clause ) && !m_activeClauses.contains(clause.getSubsumer())) {
//			if ( !containsAUX( clause ) && !m_activeSubsumers.contains(clause.getSubsumer())) {
//				clause.setSubsumer(null);
//				result.add( clause );
//				m_activeSubsumers.add( clause );
//			}
//			stack.addAll(currentNode.getChildren());
//		}
//		return result;
//	}
//
//	private boolean containsAUX( Clause clause ) {
//		return clause.toString().contains("AUX-");
//	}
//
//	private boolean conceptAppearsInBodyOf( Term term, Term[] body ) {
//		for ( Term bodyTerm : body )
//			if( bodyTerm.toString().equals( term.toString() ) )
//				return true;
//		return false;
//	}
//
//	private boolean roleAppearsInBodyOf( Term term, Clause clause ) {
//		for ( Term bodyTerm : clause.getBody() )
//			if ( bodyTerm.getArity() == 2 && isEqualRoleTerm( clause, term, bodyTerm ) )
//				return true;
//		return false;
//	}
//
//	public boolean isEqualRoleTerm( Clause currentClause,  Term subsTerm, Term currentClauseBodyTerm ) {
//		if ( currentClauseBodyTerm.getName().equals( subsTerm.getName() ) ) {
//			Term[] subsTermArgs = subsTerm.getArguments();
//			Term[] currentClauseTermVars = currentClauseBodyTerm.getArguments();
//			ArrayList<Variable> currentClauseVars = currentClause.getVariables();
//			boolean equal = true;
//			if ( !currentClauseTermVars[1].equals( subsTermArgs[1] ) || !currentClauseTermVars[0].equals( subsTermArgs[0] ))
//				equal = false;
//
//			if ( equal )
//				return true;
//			else if ( subsTermArgs[0].toString().equals("X5000") && subsTermArgs[1].toString().equals( currentClauseTermVars[1].toString() ) )
//				return true;
//			else if ( subsTermArgs[1].toString().equals("X5000") && subsTermArgs[0].toString().equals( currentClauseTermVars[0].toString() ) )
//				return true;
//			else if ( currentClauseTermVars[0].toString().equals( subsTermArgs[0].toString() ) && ( !currentClause.isBound( ( Variable )currentClauseTermVars[1] ) || !currentClauseVars.contains( subsTermArgs[1] ) ) )
//				return true;
//			else if ( currentClauseTermVars[1].toString().equals( subsTermArgs[1].toString() ) && ( !currentClause.isBound( ( Variable )currentClauseTermVars[0] ) || !currentClauseVars.contains( subsTermArgs[0] ) ) )
//				return true;
//		}
//		return false;
//
//	}
//	public Set<Term> rewAtom(Term g, ArrayList<PI> pis) {
//
//		Set<Term> checkedList = new HashSet<Term>();
//		Set<Term> arNew = new HashSet<Term>();
//		Set<Term> ar = new HashSet<Term>( Collections.singleton(g) );
//		HashSet<PI> piList = new HashSet<PI>();
//		do {
//			arNew = new HashSet<Term>(ar);
//
//			for( Term a : arNew )
//				if ( !checkedList.contains( a ) ) {
//					checkedList.add( a );
//					for ( PI pi : pis )
//						if ( !piList.contains( pi ) ) {
//							Term head = m_termFactory.getFunctionalTerm("Q", g.getArguments());
//							Term[] body = new Term[1];
//							body[0] = a;
//							Clause clause = new Clause( body , head );
//							Term newAtom = m_saturator.getSubsumees( pi , clause);
////							if ( newAtom != null ) {
//							//avenet - gia na min paragontai sto rewOfAtom concepts poy periexoun unbound var
//							if ( newAtom != null && !( newAtom.getArity() == 1 && newAtom.getArgument( 0 ).toString().equals("X5000") ) ){
//								piList.add( pi );
//								ar.add( newAtom );
//							}
//						}
//				}
//		} while (arNew.size() < ar.size());
//
//		return ar;
//	}
//}