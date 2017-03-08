/*
 * #%L
 * IQAROS
 *
 * $Id$
 * $HeadURL$
 * %%
 * Copyright (C) 2011 by the Image, Video and Multimedia Laboratory, NTUA
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */

package edu.ntua.image.refinement;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import org.oxford.comlab.perfectref.rewriter.Clause;
import org.oxford.comlab.perfectref.rewriter.PI;
import org.oxford.comlab.perfectref.rewriter.Saturator;
import org.oxford.comlab.perfectref.rewriter.Substitution;
import org.oxford.comlab.perfectref.rewriter.Term;
import org.oxford.comlab.perfectref.rewriter.TermFactory;
import org.oxford.comlab.perfectref.rewriter.Variable;

import edu.ntua.image.datastructures.Tree;
import edu.ntua.image.datastructures.TreeNode;

public class Refine_Unif {

	private static final TermFactory m_termFactory = new TermFactory();
	private static final Saturator m_saturator = new Saturator(m_termFactory);
	private boolean bothVariablesMustMatch = false;

	public Set<Clause> refineRewriting( Tree<Clause> tree, Term extraAtom, ArrayList<PI> pis ) {

		Set<TreeNode<Clause>> processedNodes = new HashSet<TreeNode<Clause>>();

		Set<Clause> activeSubsumers = new HashSet<Clause>();

		Term clauseHead = tree.getRootElement().getNodeLabel().getHead();
		Set<Clause> result = new HashSet<Clause>();
		Set<Term> rewOfNewAtom = computeRewritingOfAtom( extraAtom, pis , tree.getRootElement().getNodeLabel() );

		int iterations = 0;
		//Do a BFS over the rewriting DAG
		Queue<TreeNode<Clause>> queue = new LinkedList<TreeNode<Clause>>();
		queue.add( tree.getRootElement() );
		while (!queue.isEmpty()) {
			TreeNode<Clause> currentNode = queue.poll();
			Clause currentClause = currentNode.getNodeLabel();

			ArrayList<Variable> currentClauseVars = currentClause.getVariables();
			Term[] currentClauseBodyAtoms = currentClause.getBody();
			iterations++;
			if (processedNodes.contains(currentNode))
				continue;
			processedNodes.add(currentNode);
			boolean subTreeHasBeenCopied = false;
			Set<Clause> tempResult = new HashSet<Clause>();
			boolean childrenAreElidgibleForProcessing = isEligibleForProcessing( currentClauseVars, extraAtom.getArguments());
//			if (!isEligibleForProcessing( currentClauseVars, extraAtom.getArguments()))
//				continue;
			boolean isEligibleForRefinement = isEligibleForRefinement(currentClause, activeSubsumers);
			for (Term subsTerm : rewOfNewAtom) {

				int subsTermArity = subsTerm.getArity();

				if ( subsTermArity == 1 ) {
					Term subsTermAfterRenamings = getRightConceptAtomAfterVariableRenamings(currentClause, subsTerm );
					if ( subsTermAfterRenamings != null )
						if ( conceptAtomAppearsInQueryBody(subsTermAfterRenamings, currentClauseBodyAtoms ) ) {
							result.addAll( getNonRedundantChildrenOf( currentNode, activeSubsumers ) );
							subTreeHasBeenCopied = true;
							break;
						}
						else
							if (isEligibleForRefinement && !subsTermAfterRenamings.getName().contains("AUX$")) {
								Clause newClause = createNewQueriesWithExtraAtom(subsTermAfterRenamings, currentClauseBodyAtoms, clauseHead);
								tempResult.add( newClause );
							}
				}
				else if ( subsTermArity == 2 ) {
					Term subsTermAfterRenamings = getRightRoleAtomAfterVariableRenamings(currentClause, subsTerm );
					if ( subsTermAfterRenamings != null )
						if (roleAtomAppearsInQueryBody(subsTermAfterRenamings, currentClause)) {
							result.addAll( getNonRedundantChildrenOf( currentNode, activeSubsumers ) );
							subTreeHasBeenCopied = true;
							break;
						}
						else
							if (isEligibleForRefinement && !subsTermAfterRenamings.getName().contains("AUX$")) {
								Clause newClause = createNewQueriesWithExtraAtom( subsTermAfterRenamings, currentClauseBodyAtoms, clauseHead);
								tempResult.add( newClause );
							}
				}
				if (subTreeHasBeenCopied)
					break;
			}
			if (!subTreeHasBeenCopied) {
				if ( childrenAreElidgibleForProcessing )
					queue.addAll( currentNode.getChildren() );
				result.addAll( tempResult );
			}
		}
//		System.out.println( "Refinement algorithm performed " + iterations + " iterations" );
		return result;
	}


	private Term getRightRoleAtomAfterVariableRenamings(Clause currentClause,Term subsTerm) {
		ArrayList<Variable> currentClauseVars = currentClause.getVariables();
		Term[] subsTermArgs = subsTerm.getArguments();
		Term unifFor0 = findVariableWithRightUnificationForTermInClause(currentClause, subsTerm.getArgument( 0 ) );
		Term unifFor1 = findVariableWithRightUnificationForTermInClause(currentClause, subsTerm.getArgument( 1 ) );
		if ( ( currentClauseVars.contains(subsTermArgs[0]) && currentClauseVars.contains(subsTermArgs[1]) ) ||
				( currentClauseVars.contains(subsTermArgs[0]) && unifFor1 == null ) ||
				( currentClauseVars.contains(subsTermArgs[1]) && unifFor0 == null )	)
			return subsTerm;
		else if ( currentClauseVars.contains( subsTermArgs[0] ) && unifFor1 != null )
			return m_termFactory.getFunctionalTerm( subsTerm.getName() , subsTermArgs[0] , unifFor1 );
		else if ( currentClauseVars.contains( subsTermArgs[1] ) && unifFor0 != null )
			return m_termFactory.getFunctionalTerm( subsTerm.getName() , unifFor0 , subsTermArgs[1] );
		else if ( unifFor0 != null && unifFor1 != null )
			return m_termFactory.getFunctionalTerm( subsTerm.getName() , unifFor0 , unifFor1 );
		return null;
	}

	private Term getRightConceptAtomAfterVariableRenamings(Clause currentClause, Term conceptAtom) {
		if (currentClause.getVariables().contains(conceptAtom.getArgument(0)))
			return conceptAtom;
		else {
			Term newTerm = findVariableWithRightUnificationForTermInClause( currentClause , conceptAtom.getArgument(0) );
			if (newTerm != null)
				return m_termFactory.getFunctionalTerm( conceptAtom.getName(), newTerm );
		}
		return null;
	}

	public boolean isEligibleForProcessing(ArrayList<Variable> variables, Term[] arguments) {
		for (Term term : arguments)
			if (variables.contains(term))
				return true;
		return false;
	}

	private boolean isEligibleForRefinement(Clause currentClause, Set<Clause> activeSubsumers) {
		if (containsAUX(currentClause))
			return false;
		if (activeSubsumers.contains(currentClause.getSubsumer()))
			return false;
		return true;
	}

	private Clause createNewQueriesWithExtraAtom( Term extraAtom , Term[] body, Term head) {

		Term[] newBody = new Term[body.length + 1];
		for (int i=0 ; i<body.length ; i++)
			newBody[i] = body[i];
		newBody[body.length] = extraAtom;

		return new Clause( newBody , head );
	}

	private Set<Clause> getNonRedundantChildrenOf( TreeNode<Clause> node, Set<Clause> activeSubsumers ) {
		Set<Clause> result = new HashSet<Clause>();
		Set<TreeNode<Clause>> visited = new HashSet<TreeNode<Clause>>();
		Stack<TreeNode<Clause>> stack = new Stack<TreeNode<Clause>>();
		stack.push(node);
		while (!stack.isEmpty()) {
			TreeNode<Clause> currentNode = stack.pop();
			Clause clause = currentNode.getNodeLabel();
			if (!visited.contains(currentNode)){
				if ( !containsAUX( clause ) && !activeSubsumers.contains(clause.getSubsumer())) {
					clause.setSubsumer(null);
					result.add( clause );
					activeSubsumers.add( clause );
				}
				visited.add(currentNode);
				stack.addAll(currentNode.getChildren());
			}
		}
		return result;
	}

	private boolean containsAUX( Clause clause ) {
		return clause.toString().contains("AUX$");
	}

	private boolean conceptAtomAppearsInQueryBody(Term conceptAtom, Term[] queryBodyAtoms) {
		for (Term bodyAtom : queryBodyAtoms)
			if (bodyAtom.toString().equals(conceptAtom.toString()))
				return true;
		return false;
	}

	private boolean roleAtomAppearsInQueryBody(Term roleAtom, Clause currentQuery ) {
		for (Term bodyAtom : currentQuery.getBody())
			if (bodyAtom.getArity() == 2 && isEqualRoleTerm(currentQuery, roleAtom, bodyAtom ))
				return true;
		return false;
	}

	public boolean isEqualRoleTerm( Clause currentQuery,  Term roleAtom, Term bodyAtom ) {
		if ( bodyAtom.getName().equals( roleAtom.getName() ) ) {
			Term[] roleAtomVariables = roleAtom.getArguments();
			Term[] bodyAtomVariables = bodyAtom.getArguments();
			ArrayList<Variable> currentClauseVars = currentQuery.getVariables();
			boolean equal = true;
			if ( !bodyAtomVariables[1].equals( roleAtomVariables[1] ) || !bodyAtomVariables[0].equals( roleAtomVariables[0] ))
				equal = false;

			if ( !bothVariablesMustMatch )
				if ( equal )
					return true;
//				else if ( roleAtomVariables[0].toString().equals("X5000") && roleAtomVariables[1].toString().equals( bodyAtomVariables[1].toString() ) )
//					return true;
//				else if ( roleAtomVariables[1].toString().equals("X5000") && roleAtomVariables[0].toString().equals( bodyAtomVariables[0].toString() ) )
//					return true;
				else if ( bodyAtomVariables[0].toString().equals( roleAtomVariables[0].toString() ) && ( !currentQuery.isBound( ( Variable )bodyAtomVariables[1] ) || !currentClauseVars.contains( roleAtomVariables[1] ) ) )
					return true;
				else if ( bodyAtomVariables[1].toString().equals( roleAtomVariables[1].toString() ) && ( !currentQuery.isBound( ( Variable )bodyAtomVariables[0] ) || !currentClauseVars.contains( roleAtomVariables[0] ) ) )
					return true;
		}
		return false;
	}

	public Set<Term> computeRewritingOfAtom(Term extraAtom, ArrayList<PI> pis , Clause query) {

		Set<Term> rewOfExtraAtom = new HashSet<Term>( Collections.singleton(extraAtom) );
		int extraAtomArity = extraAtom.getArity();
		Term[] extraAtomArguments = extraAtom.getArguments();
		ArrayList<Variable> queryVars = query.getVariables();
		Term head = null;

		if ( extraAtomArity == 1 && queryVars.contains( extraAtomArguments[0] ) )
			head = m_termFactory.getFunctionalTerm( "Q", extraAtomArguments[0] );
		else if ( extraAtomArity == 2 )
			if ( queryVars.contains( extraAtomArguments[0] ) && queryVars.contains( extraAtomArguments[1] ) ) {
				head = m_termFactory.getFunctionalTerm( "Q", extraAtomArguments[0], extraAtomArguments[1]);
				bothVariablesMustMatch = true;
			}
			else if ( queryVars.contains( extraAtomArguments[0] ) )
				head = m_termFactory.getFunctionalTerm( "Q", extraAtomArguments[0] );
			else if ( queryVars.contains( extraAtomArguments[1] ) )
				head = m_termFactory.getFunctionalTerm( "Q", extraAtomArguments[1] );

		if ( head != null ) {
			Set<Term> checkedList = new HashSet<Term>();
			HashSet<PI> piList = new HashSet<PI>();
			Set<Term> newTerms = new HashSet<Term>();
			do {
				newTerms = new HashSet<Term>();
				for( Term a : rewOfExtraAtom )
					if ( !checkedList.contains( a ) ) {
						checkedList.add( a );
						for ( PI pi : pis )
							if ( !piList.contains( pi ) ) {
								Term[] body =  new Term[1];
								body[0] = a;
								Clause clause = new Clause( body , head );
								Clause cl = m_saturator.getNewQueryNoRename(pi, 0, clause);
								Term newAtom = null;
								if ( cl!= null )
									newAtom = cl.getBody()[0];
								if ( newAtom != null && !( newAtom.getArity() == 1 && newAtom.getArgument( 0 ).toString().equals("X5000") ) ) {
									piList.add( pi );
									newTerms.add( newAtom );
								}
							}
					}
				rewOfExtraAtom.addAll(newTerms);
			} while (!newTerms.isEmpty());
		}
		return rewOfExtraAtom;
	}

	private Term findVariableWithRightUnificationForTermInClause( Clause clause, Term queryAtomVariable ) {

		Set<Substitution> unifications = clause.getUnifications();
		ArrayList<Term> alreadyAdded = new ArrayList<Term>();
		Term t = findUnificationForterm( unifications, queryAtomVariable, alreadyAdded );

		if ( t == null )
			return null;

		ArrayList<Variable> clauseVars = clause.getVariables();
		ArrayList<Term> termSet = new ArrayList<Term>();

		termSet.add( t );
		alreadyAdded.add( t );
		while ( !termSet.isEmpty() ) {
			Term queryAtomNewVariable = termSet.remove( 0 );
			if ( clauseVars.contains( queryAtomNewVariable ) )
				return queryAtomNewVariable;
			else {
				Term q = findUnificationForterm( unifications , queryAtomNewVariable , alreadyAdded );
				if ( q!= null )
				{
					termSet.add( q );
					alreadyAdded.add( q );
				}
			}
		}

		return null;
	}

	private Term findUnificationForterm( Set<Substitution> unifications , Term term, ArrayList<Term> alreadyAdded) {

		for ( Substitution sub : unifications )
			if ( sub.containsKey( term ) && !alreadyAdded.contains( sub.get( term ) ) )
				return sub.get( term );
		return null;
	}
}