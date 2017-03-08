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
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import org.oxford.comlab.perfectref.rewriter.Clause;
import org.oxford.comlab.perfectref.rewriter.PI;
import org.oxford.comlab.perfectref.rewriter.Substitution;
import org.oxford.comlab.perfectref.rewriter.Term;
import org.oxford.comlab.perfectref.rewriter.TermFactory;
import org.oxford.comlab.perfectref.rewriter.Variable;

import edu.ntua.image.datastructures.Tree;
import edu.ntua.image.datastructures.TreeNode;
import edu.ntua.image.incremental.Incremental;
import edu.ntua.image.redundancy.RedundancyElimination;

public class RewritingExtensionManager {

	private static final TermFactory m_termFactory = new TermFactory();
	private boolean bothVariablesMustMatch = false;
	private Set<Variable> joinVars;
	private Set<TreeNode<Clause>> processedNodes;
	private RedundancyElimination redundancyEliminator;

	private HashMap<String, Substitution> substitutionsMap = new HashMap<String, Substitution>();
	
	public HashMap<String, Substitution> getsubstitutionsMap() {
		return substitutionsMap;
	}
	
	
	private boolean renameExtraAtom = false;
	private Term equalRole = null;

	public RewritingExtensionManager(RedundancyElimination redundancyManager) {
		redundancyEliminator=redundancyManager;
	}

	public Set<Clause> extendRewriting( Tree<Clause> tree, Term extraAtom, ArrayList<PI> pis, Set<Term> mainQueryVars, HashMap<String, Substitution> substitMap ) {
		this.substitutionsMap = substitMap;

		int extraAtomArity = extraAtom.getArity();
		Term[] extraAtomArguments = extraAtom.getArguments();
		joinVars = new HashSet<Variable>();
		processedNodes = new HashSet<TreeNode<Clause>>();

		if (extraAtomArity == 1 && mainQueryVars.contains(extraAtomArguments[0]))
			joinVars.add((Variable)extraAtomArguments[0]);
		else if (extraAtomArity == 2) {
			joinVars.add((Variable)extraAtomArguments[0]);
			joinVars.add((Variable)extraAtomArguments[1]);
			if (!mainQueryVars.contains( extraAtomArguments[0]))
				joinVars.remove( extraAtomArguments[0] );
			else if (!mainQueryVars.contains( extraAtomArguments[1]))
				joinVars.remove( extraAtomArguments[1] );
		}
		if (joinVars.isEmpty()) {
			System.err.println( "\ncomputeRewritingOfAtomAs Tree ERROR" );
			System.exit(0);
		}

		Term clauseHead = tree.getRootElement().getNodeLabel().getHead();
		Set<Clause> result = new HashSet<Clause>();
		Set<Term> rewOfNewAtom = computeRewritingOfAtom( extraAtom, pis, mainQueryVars);

		redundancyEliminator.initialise(this, tree.getRootElement().getSubTreeAsSet(), rewOfNewAtom);

		Queue<TreeNode<Clause>> queue = new LinkedList<TreeNode<Clause>>();
		queue.add( tree.getRootElement() );
		while (!queue.isEmpty()) {
			TreeNode<Clause> currentNode = queue.poll();
			Clause currentClause = currentNode.getNodeLabel();

			ArrayList<Variable> currentClauseVars = currentClause.getVariables();
			Term[] currentClauseBody = currentClause.getBody();

			if (processedNodes.contains(currentNode))
				continue;
			processedNodes.add(currentNode);
			boolean subTreeHasBeenCopied = false;
			Set<Clause> tempResult = new HashSet<Clause>();
			if (!isEligibleForProcessing( currentClause ) )
				continue;
			if (redundancyEliminator.isClauseRedundant(currentClause,joinVars)) {
				queue.addAll(currentNode.getChildren());
//				System.out.println("2: " + currentClause + " " + currentClause.getSubsumer() );
				continue;
			}
			boolean isEligibleForExtension = isEligibleForExtension(currentClause);

			for (Term subsTerm : rewOfNewAtom) {
				Term[] subsTermArgs = subsTerm.getArguments();
				int subsTermArity = subsTerm.getArity();

				if (subsTermArity == 1 ) {//&& currentClauseVars.contains( subsTermArgs[0] )) {
					if ( conceptAtomAppearsInQueryBody( subsTerm , currentClauseBody ) ) {
						result.addAll( getNonRedundantChildrenOf( currentNode ) );
						subTreeHasBeenCopied = true;
						break;
					}
					else
						if (isEligibleForExtension && !subsTerm.getName().contains("AUX$") && !isInteger(subsTerm.getName() ) ) {
							Clause newClause;
							if (renameExtraAtom) {
								newClause = createNewQueriesWithExtraAtom( subsTerm.apply(substitutionsMap.get(currentClause.m_canonicalRepresentation), m_termFactory), currentClauseBody, clauseHead);
								renameExtraAtom = false;
							}
							else
								newClause = createNewQueriesWithExtraAtom(subsTerm, currentClauseBody, clauseHead);
							tempResult.add( newClause );
							redundancyEliminator.checkAndMarkClauseAsPossiblyNonRedundant(currentClause, subsTerm, newClause);
						}
				}
				else if (subsTermArity == 2 ) {// && (currentClauseVars.contains(subsTermArgs[0]) || currentClauseVars.contains(subsTermArgs[1]))) {
					Substitution sub = roleAtomAppearsInQueryBody(subsTerm, currentClause);
					if ( sub != null ) {
						if (sub.isEmpty()) {
							result.addAll( getNonRedundantChildrenOf( currentNode ) );
							subTreeHasBeenCopied = true;
							break;
						}
						else {
							substitutionsMap.put(currentClause.m_canonicalRepresentation, sub);
							Variable mappedVariable = sub.keySet().iterator().next();
							//currentNode contains the mappedVariable
							if ( currentClause.getVariables().contains( mappedVariable ) )
								for (TreeNode<Clause> currentChildNode : currentNode.getChildren() ) {
									Clause currentChildClause = currentChildNode.getNodeLabel();

									//currentChild does not contain equalRole and the term that replaces it is a concept
									if ( !currentChildClause.m_canonicalRepresentation.contains( equalRole.toString() ) &&
										findTermThatReplacesEqualRole( currentClause , currentChildClause ).getArity() == 1 ) {
										TreeNode<Clause> newCurrentNode = renameGraph( currentNode , sub );
										result.addAll( newCurrentNode.getSubTreeAsSet());
										processedNodes.add(currentChildNode);
									} else
										;

								}
							else {
								result.addAll( getNonRedundantChildrenOf( currentNode ) );
								subTreeHasBeenCopied = true;
								break;
							}
						}
					}
					else
						if (isEligibleForExtension && !subsTerm.getName().contains("AUX$") && !isInteger(subsTerm.getName() ) ) {
							Clause newClause;
							if (renameExtraAtom) {
								newClause = createNewQueriesWithExtraAtom( subsTerm.apply(substitutionsMap.get(currentClause.m_canonicalRepresentation), m_termFactory), currentClauseBody, clauseHead);
								renameExtraAtom = false;
							}
							else
								newClause = createNewQueriesWithExtraAtom( subsTerm, currentClauseBody, clauseHead);
							tempResult.add( newClause );
							redundancyEliminator.checkAndMarkClauseAsPossiblyNonRedundant(currentClause, subsTerm, newClause);
						}
				}
				if (subTreeHasBeenCopied)
					break;
			}
			if (!subTreeHasBeenCopied) {
				for (TreeNode<Clause> child : currentNode.getChildren())
					if (!processedNodes.contains(child))
						queue.add(child);
				result.addAll( tempResult );
				redundancyEliminator.flush(currentClause);
			}
		}
		return result;
	}

	public boolean isInteger( String input ) {
	   try {
	      Integer.parseInt( input );
	      return true;
	   } catch(NumberFormatException e){} {
	      return false;
	   }
	}

//	public boolean isEligibleForProcessing(Clause clause) {
//		return clause.getVariables().containsAll(joinVars);
//	}

	private Term findTermThatReplacesEqualRole(Clause originalClause, Clause newClause) {

		Term[] newBody = newClause.getBody();

		for ( int i = 0 ; i < newBody.length ; i++ )
			if ( !originalClause.m_canonicalRepresentation.contains( newBody[i].toString() ) )
				return newBody[i];

		return null;
	}

	public boolean isEligibleForProcessing(Clause clause) {

		ArrayList<Variable> clauseVariables = clause.getVariables();

		if (clauseVariables.containsAll(joinVars) )
			return true;
		else {
			Substitution sub = substitutionsMap.get(clause.m_canonicalRepresentation);
			if ( joinVars.size() == 1 && findMappedVariableInClause( clause, sub , (Variable)joinVars.toArray()[0] ) ) {
				renameExtraAtom = true;
				return true;
			} else if ( findMappedVariableInClause( clause , sub , (Variable)joinVars.toArray()[0] ) &&
			findMappedVariableInClause( clause , sub , (Variable)joinVars.toArray()[1] ) ) {
				renameExtraAtom = true;
				return true;
			}
		}
		return false;
	}

	private boolean findMappedVariableInClause( Clause c, Substitution s, Term var ) {

		Term currentVar = var;
		Set<Term> checkedVars = new HashSet<Term>();
		ArrayList<Variable> clauseVariables = c.getVariables();

		if ( s == null )
			return false;

		while ( !checkedVars.contains( currentVar ) && s.get( currentVar ) != null) {
			Term tempTerm = s.get( currentVar );
			if ( tempTerm != null )
				if ( clauseVariables.contains( tempTerm ) )
					return true;
				else {
					checkedVars.add( currentVar );
					currentVar = tempTerm;
				}
		}
		return false;
	}


	private boolean isEligibleForExtension(Clause currentClause) {
		if (containsAUX(currentClause))
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

	private Set<Clause> getNonRedundantChildrenOf( TreeNode<Clause> node ) {
		Set<Clause> result = new HashSet<Clause>();
		Set<TreeNode<Clause>> visited = new HashSet<TreeNode<Clause>>();
		Stack<TreeNode<Clause>> stack = new Stack<TreeNode<Clause>>();
		stack.push(node);
		while (!stack.isEmpty()) {
			TreeNode<Clause> currentNode = stack.pop();
			Clause clause = currentNode.getNodeLabel();
			if (!visited.contains(currentNode)){
				if (!containsAUX(clause) && redundancyEliminator.isClauseNonRedundant(clause,joinVars)) {
					redundancyEliminator.checkAndMarkClauseAsNonRedundant(clause);
					result.add(clause);
					redundancyEliminator.addActiveSubsumer(clause);
				}
				processedNodes.add(currentNode);
				visited.add(currentNode);
				stack.addAll(currentNode.getChildren());
			}
		}
		return result;
	}

	public boolean containsAUX( Clause clause ) {
		Term[] m_body = clause.getBody();
		for(int i=0; i < clause.getBody().length; i++){
			//Auxiliary predicates introduced in the clausification
			if (m_body[i].getName().contains("AUX$"))
				return true;
			try{
				//Auxiliary symbols introduced in the normalization (HermiT)
				Integer.parseInt(m_body[i].getName());
				return true;
			}
			catch(NumberFormatException e){}
		}
		return false;
	}

	public boolean conceptAtomAppearsInQueryBody(Term conceptAtom, Term[] queryBodyAtoms) {
		for (Term bodyAtom : queryBodyAtoms)
			if (bodyAtom.toString().equals(conceptAtom.toString()))
				return true;
		return false;
	}

	public Substitution roleAtomAppearsInQueryBody(Term roleAtom, Clause currentQuery ) {
		equalRole = null;
		for (Term bodyAtom : currentQuery.getBody())
			if (bodyAtom.getArity() == 2 ) {
				Substitution s = isEqualRoleTerm(currentQuery, roleAtom, bodyAtom );
				if ( s!= null )
					return s;
			}
		return null;
	}

	public Substitution isEqualRoleTerm( Clause currentQuery,  Term roleAtom, Term bodyAtom ) {
		if ( bodyAtom.getName().equals( roleAtom.getName() ) ) {
			Term[] roleAtomVariables = roleAtom.getArguments();
			Term[] bodyAtomVariables = bodyAtom.getArguments();
			ArrayList<Variable> currentClauseVars = currentQuery.getVariables();
			if (bodyAtomVariables[1].equals( roleAtomVariables[1] ) && bodyAtomVariables[0].equals( roleAtomVariables[0] ))
				return new Substitution();

//			if ( bothVariablesMustMatch ) {
//				if ( bodyAtomVariables[0].toString().equals( roleAtomVariables[0].toString() ) && ( !currentQuery.isBound( ( Variable )bodyAtomVariables[1] ) ) )
//					return true;
//				else if ( bodyAtomVariables[1].toString().equals( roleAtomVariables[1].toString() ) && ( !currentQuery.isBound( ( Variable )bodyAtomVariables[0] ) ) )
//					return true;
//			}
			if (!bothVariablesMustMatch) {
				Substitution s = new Substitution();
				if ( bodyAtomVariables[0].toString().equals( roleAtomVariables[0].toString() ) ) {
					equalRole = roleAtom;
					s.put( (Variable) roleAtomVariables[1], bodyAtomVariables[1]);
					return s;
				}
				else if ( bodyAtomVariables[1].toString().equals( roleAtomVariables[1].toString() ) ) {
					equalRole = roleAtom;
					s.put( (Variable) roleAtomVariables[0], bodyAtomVariables[0]);
					return s;
				}
			}
		}
		return null;
	}

	public Set<Term> computeRewritingOfAtom(Term extraAtom, ArrayList<PI> pis, Set<Term> mainQueryVars) {

		int extraAtomArity = extraAtom.getArity();
		Term[] extraAtomArguments = extraAtom.getArguments();
		Term head = null;

		if ( extraAtomArity == 1 && mainQueryVars.contains( extraAtomArguments[0] ) )
			head = m_termFactory.getFunctionalTerm( "Q", extraAtomArguments[0] );
		else if ( extraAtomArity == 2 )
			if ( mainQueryVars.contains( extraAtomArguments[0] ) && mainQueryVars.contains( extraAtomArguments[1] ) ) {
				head = m_termFactory.getFunctionalTerm( "Q", extraAtomArguments[0], extraAtomArguments[1]);
				bothVariablesMustMatch = true;
			}
			else if ( mainQueryVars.contains( extraAtomArguments[0] ) )
				head = m_termFactory.getFunctionalTerm( "Q", extraAtomArguments[0] );
			else if ( mainQueryVars.contains( extraAtomArguments[1] ) )
				head = m_termFactory.getFunctionalTerm( "Q", extraAtomArguments[1] );
		TreeNode<Term> rootElement = new TreeNode<Term>( extraAtom );
		if ( head != null ) {
			Stack<TreeNode<Term>> toVisit = new Stack<TreeNode<Term>>();
			HashMap<String,TreeNode<Term>> m_canonicalsToRewOfExtraAtom = new HashMap<String,TreeNode<Term>>();
			toVisit.push(rootElement);
			m_canonicalsToRewOfExtraAtom.put(extraAtom.toString(),rootElement);
			while(!toVisit.isEmpty()) {
				TreeNode<Term> currentTermNode = toVisit.pop();
				Term[] body =  new Term[1];
				body[0] = currentTermNode.getNodeLabel();
				Clause clause = new Clause( body , head );
				for ( PI pi : pis ) {
					Clause cl = Incremental.applyPositiveInclusion(pi, 0, clause);
					if ( cl != null )
						if ( !( cl.getBody()[0].getArity() == 1 && Integer.parseInt( cl.getBody()[0].getArgument( 0 ).toString().substring(1, cl.getBody()[0].getArgument( 0 ).toString().length())) > 500 ) ) {
							Term newAtom = cl.getBody()[0];
							TreeNode<Term> newTermNode = null;
							TreeNode<Term> nodeInRew = m_canonicalsToRewOfExtraAtom.get(newAtom.toString());
							if (nodeInRew == null) {
								newTermNode = new TreeNode<Term>( newAtom );
								m_canonicalsToRewOfExtraAtom.put(newAtom.toString(), newTermNode );
								toVisit.push( newTermNode );
							}
							else
								newTermNode = m_canonicalsToRewOfExtraAtom.get( newAtom.toString() );

							currentTermNode.addChild( newTermNode );
						}
				}
			}
		}
		return rootElement.getSubTreeAsSet();
	}

	private TreeNode<Clause> renameGraph(TreeNode<Clause> currentT1, Substitution currentMapping) {

		HashMap<TreeNode<Clause>,TreeNode<Clause>> oldNode2NewNode = new HashMap<TreeNode<Clause>, TreeNode<Clause>>();

		Stack<TreeNode<Clause>> stack = new Stack<TreeNode<Clause>>();
		stack.push(currentT1);

		Set<TreeNode<Clause>> visitedNodes = new HashSet<TreeNode<Clause>>();

		TreeNode<Clause> newCurrentT1 = new TreeNode<Clause>( getNewQuery(  currentMapping, currentT1.getNodeLabel() ) );
		oldNode2NewNode.put(currentT1, newCurrentT1);
		substitutionsMap.put(newCurrentT1.getNodeLabel().m_canonicalRepresentation, substitutionsMap.get(currentT1.getNodeLabel().m_canonicalRepresentation ) );

		while ( !stack.isEmpty() ) {
			TreeNode<Clause> currentNode = stack.pop();
			visitedNodes.add(currentNode);
//			Substitution currentMapping = substitutionsMap.get( currentNode.getNodeLabel().m_canonicalRepresentation );

			TreeNode<Clause> currentNewNode = oldNode2NewNode.get( currentNode );

			for ( TreeNode<Clause> child : currentNode.getChildren() ) {
				if (visitedNodes.contains(child))
					continue;
				stack.push(child);
				TreeNode<Clause> newChildNode = new TreeNode( getNewQuery( currentMapping, child.getNodeLabel() ) );
				currentNewNode.addChild( newChildNode );
				oldNode2NewNode.put(child, newChildNode);
				substitutionsMap.put(newChildNode.getNodeLabel().m_canonicalRepresentation, currentMapping);
			}
		}
		return newCurrentT1;
	}


	/**
	 * Creates a new query by applying the mgu of two atoms to a given query
	 * @param mgu
	 * @param clause
	 * @return
	 */
	private Clause getNewQuery(Substitution mgu, Clause clause){

		if ( mgu == null )
			return clause;

		Set<Term> newBody = new LinkedHashSet<Term>();
        //Copy the atoms from the main premise
        for (int index=0; index < clause.getBody().length; index++)
			newBody.add(clause.getBody()[index].apply(mgu, m_termFactory));

        //New body and head
        Term[] body = new Term[newBody.size()];
        newBody.toArray(body);
        Term head = clause.getHead().apply(mgu, m_termFactory);

        Clause newQuery = new Clause(body, head);

		return newQuery;
	}
}