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

package edu.ntua.image.incremental;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;
import java.util.Map.Entry;

import org.apache.log4j.Logger;
import org.apache.log4j.PropertyConfigurator;
import org.oxford.comlab.perfectref.rewriter.Clause;
import org.oxford.comlab.perfectref.rewriter.PI;
import org.oxford.comlab.perfectref.rewriter.Substitution;
import org.oxford.comlab.perfectref.rewriter.Term;
import org.oxford.comlab.perfectref.rewriter.TermFactory;
import org.oxford.comlab.perfectref.rewriter.Variable;

import edu.ntua.image.Configuration;
import edu.ntua.image.Configuration.RedundancyEliminationStrategy;
import edu.ntua.image.datastructures.LabeledGraph;
import edu.ntua.image.datastructures.Tree;
import edu.ntua.image.datastructures.TreeNode;
import edu.ntua.image.redundancy.NonRedundantClausesTracker;
import edu.ntua.image.redundancy.RedundancyElimination;
import edu.ntua.image.redundancy.SimpleRedundancyEliminator;
import edu.ntua.image.refinement.RewritingExtensionManager;

public class Incremental {

	protected static Logger	logger = Logger.getLogger( Incremental.class );

	private static TermFactory m_termFactory;
	private static int localSkolemIndex;

	private Map<String,TreeNode<Clause>> m_canonicalsToDAGNodes;
	private RewritingExtensionManager m_refine;
	private RedundancyElimination redundancyEliminator;
	private Configuration config;

	private HashMap<String, Substitution> substitutionsMap = new HashMap<String, Substitution>();
	
	public HashMap<String, Substitution> getsubstitutionsMap() {
		HashMap<String, Substitution> refineSubs = m_refine.getsubstitutionsMap();
		if ( refineSubs != null && refineSubs.size() > substitutionsMap.size() )
			return refineSubs;
		return substitutionsMap;
	}

	private Term equalRole = null;
	private boolean renameExtraAtom = false;

	public Incremental() {
		this(new Configuration());
	}

	public Incremental(Configuration c) {
		if (c != null)
			this.config = c;
		else
			config = new Configuration();
		m_termFactory = new TermFactory();
		m_canonicalsToDAGNodes = new HashMap<String,TreeNode<Clause>>();
		if (config.redundancyElimination == RedundancyEliminationStrategy.Full_Subsumption)
			redundancyEliminator = new SimpleRedundancyEliminator();
		else if (config.redundancyElimination == RedundancyEliminationStrategy.Restricted_Subsumption)
			redundancyEliminator = new NonRedundantClausesTracker();
		m_refine = new RewritingExtensionManager(redundancyEliminator);
		localSkolemIndex=1;

		PropertyConfigurator.configure("./logger.properties");
	}

	public ArrayList<Clause> computeUCQRewriting(ArrayList<PI> tBoxAxioms, Clause originalQuery) {
		long t1 = System.currentTimeMillis();
		logger.info( "Rewriting query: " + originalQuery + "\n");
		Term[] queryBody = new Term[originalQuery.getBody().length];
		queryBody = findRightOrderOfQuery(originalQuery);

		HashMap<Term,Tree <Clause>> termToTreeUCQRews = new HashMap<Term,Tree <Clause>>();
		Set<Term> activeVariablesSoFar = new HashSet<Term>( originalQuery.getDistinguishedVariables() );
		logger.info("Starting with term: " + queryBody[0] );
		Tree<Clause> incrementalTree = computeRewritingOfAtomAsTree(queryBody[0], tBoxAxioms, activeVariablesSoFar, true);
		logger.debug("term had UCQ size: " + incrementalTree.getRootElement().getSubTreeAsSet().size() + " in " + (System.currentTimeMillis() - t1) + " ms" );
		addNewActiveVariables(activeVariablesSoFar,queryBody[0].getArguments());
		int maxUCQOfConceptTerm=0;
		Term conceptTermWithMaxUCQRew=null;
		ArrayList<Clause> ucqOfConceptTermWithMaxUCQRew=null;
		Tree<Clause> treeOfConceptTermWithMaxUCQRew = null;
		for (int i=1 ; i < queryBody.length ; i++) {
			if (queryBody[i].getArguments().length == 1) {
				logger.debug( "\ncomputing UCQ for concept term: " + queryBody[i] );
				Tree<Clause> treeUCQRew = computeRewritingOfAtomAsTree(queryBody[i], tBoxAxioms, activeVariablesSoFar, false);
				termToTreeUCQRews.put(queryBody[i], treeUCQRew);
				ucqOfConceptTermWithMaxUCQRew = new ArrayList<Clause> (treeUCQRew.getRootElement().getSubTreeAsSet());
				int currentTermUCQSize=ucqOfConceptTermWithMaxUCQRew.size();
				if (currentTermUCQSize > maxUCQOfConceptTerm) {
					maxUCQOfConceptTerm=currentTermUCQSize;
					conceptTermWithMaxUCQRew=queryBody[i];
					treeOfConceptTermWithMaxUCQRew = treeUCQRew;
				}
			}
			addNewActiveVariables(activeVariablesSoFar,queryBody[i].getArguments());
		}

		activeVariablesSoFar = new HashSet<Term>( originalQuery.getDistinguishedVariables() );
		addNewActiveVariables(activeVariablesSoFar,queryBody[0].getArguments());
		ArrayList<Clause> ucqRewriting = new ArrayList<Clause>();
		for (int i = 1 ; i < queryBody.length ; i++) {
			long st=System.currentTimeMillis();
			Tree<Clause> bodyRew = termToTreeUCQRews.get(queryBody[i]);
			//If it is null then it is a role
			if( bodyRew == null )
				bodyRew = computeRewritingOfAtomAsTree(queryBody[i], tBoxAxioms, activeVariablesSoFar, false);
			//otherwise it is a concept and we skip it if it is the one with the largest UCQ. We will connect it last.
			else if (queryBody[i]==conceptTermWithMaxUCQRew)
				continue;
			boolean checkOfconceptTermWithMaxUCQRewAndQueryBodyLength = conceptTermWithMaxUCQRew == null && i == queryBody.length-1;
			if (checkOfconceptTermWithMaxUCQRewAndQueryBodyLength) {
				logger.debug("Before finalisation UCQ size: " + incrementalTree.getRootElement().getSubTreeAsSet().size() + " in "+ (System.currentTimeMillis() -t1) + "ms");
				long t = System.currentTimeMillis();
				//Run only join mode
//				incrementalTree = joinTreeWithExtraAtomTree(incrementalTree, bodyRew);
//				ucqRewriting = new ArrayList<Clause>( incrementalTree.getRootElement().getSubTreeAsSet() );
				// run refinement mode
				ucqRewriting = new ArrayList<Clause>( m_refine.extendRewriting(incrementalTree, queryBody[i], tBoxAxioms, activeVariablesSoFar, substitutionsMap) );
				logger.debug("Finalising with term: " + queryBody[i] + " with UCQ size: " + bodyRew.getRootElement().getSubTreeAsSet().size() + " in " + (System.currentTimeMillis() - t) + "msec" );
			}
			else {
				logger.info("conjoining term: " + queryBody[i] );
				incrementalTree = joinTreeWithExtraAtomTree( incrementalTree , bodyRew );
				logger.debug("term had UCQ size: " + bodyRew.getRootElement().getSubTreeAsSet().size());
			}
			if ( !checkOfconceptTermWithMaxUCQRewAndQueryBodyLength ) {
				logger.debug("current size is: " + incrementalTree.getRootElement().getSubTreeAsSet().size() + " joinned in = " + (System.currentTimeMillis()-st) + " ms");
//				for ( Clause c : incrementalTree.getRootElement().getSubTreeAsSet() )
//					System.out.println( c + "\t\t" + substitutionsMap.get(c.m_canonicalRepresentation) );
				logger.debug( "and tree size is: " + incrementalTree.getRootElement().getSubTreeAsSet().size() );
			}
			addNewActiveVariables(activeVariablesSoFar,queryBody[i].getArguments());
		}
		if( conceptTermWithMaxUCQRew != null ) {
			logger.debug("Before finalisation UCQ size: " + incrementalTree.getRootElement().getSubTreeAsSet().size() + " in "+ (System.currentTimeMillis() -t1) + "ms");
//			logger.debug("Finalising with term: " + conceptTermWithMaxUCQRew + " with UCQ size: " + maxUCQOfConceptTerm);
			long t = System.currentTimeMillis();
			//run join mode
//			incrementalTree = joinTreeWithExtraAtomTree(incrementalTree, treeOfConceptTermWithMaxUCQRew );
			ucqRewriting = new ArrayList<Clause>( incrementalTree.getRootElement().getSubTreeAsSet() );
			//run refinement mode
			ucqRewriting = new ArrayList<Clause>( m_refine.extendRewriting(incrementalTree, conceptTermWithMaxUCQRew, tBoxAxioms, activeVariablesSoFar, substitutionsMap) );
			logger.debug("Finalising with term: " + conceptTermWithMaxUCQRew + " with UCQ size: " + maxUCQOfConceptTerm + " in " + (System.currentTimeMillis() - t) + "msec" );
		}

		//If there was just a single term then the result is in incrementalTree
		if( queryBody.length == 1 ) {
			ucqRewriting = new ArrayList<Clause>( incrementalTree.getRootElement().getSubTreeAsSet() );
			//run refine mode
			ucqRewriting = redundancyEliminator.pruneAUX( ucqRewriting );
			logger.debug("Finalising with term: in " + (System.currentTimeMillis() - t1) + "msec" );
		}

		long auxT = System.currentTimeMillis();
		//run join mode
//		ucqRewriting = redundancyEliminator.pruneAUX( ucqRewriting );
//		logger.info("prunning AUX in " + (System.currentTimeMillis() - auxT) + "ms" );

		logger.info( "Size of UCQ before subsumption = " + ucqRewriting.size() + " computed in " + (System.currentTimeMillis() - t1) + "ms" );

		long st=System.currentTimeMillis();
		ucqRewriting = redundancyEliminator.removeRedundantClauses(ucqRewriting);
		logger.info("Subsumption produced UCQ size = " + ucqRewriting.size() + " and required: " + (System.currentTimeMillis()-st) + "ms");

		logger.info( "\nFINAL non-redundant UCQ = " + ucqRewriting.size() + " in TOTAL " + (System.currentTimeMillis() - t1) +"ms\n\n");

//		printTree(incrementalTree);
		return ucqRewriting;
	}

	private void addNewActiveVariables(Set<Term> queryActiveVars, Term[] arguments) {
		queryActiveVars.add( arguments[0] );
		if (arguments.length==2)
			queryActiveVars.add( arguments[1] );
	}

	private Tree<Clause> computeRewritingOfAtomAsTree(Term extraAtom, ArrayList<PI> pis , Set<Term> queryVarsSoFar, boolean firstTree) {
		int extraAtomArity = extraAtom.getArity();
		Term[] extraAtomArguments = extraAtom.getArguments();
		Term head = null;

		if (firstTree)
			head  = m_termFactory.getFunctionalTerm( "Q", queryVarsSoFar.toArray(new Term[queryVarsSoFar.size()]) );
		else if ( extraAtomArity == 1 && queryVarsSoFar.contains( extraAtomArguments[0] ) )
			head = m_termFactory.getFunctionalTerm( "Q", extraAtomArguments[0] );
		else if ( extraAtomArity == 2 )
			if ( queryVarsSoFar.contains( extraAtomArguments[0] ) && queryVarsSoFar.contains( extraAtomArguments[1] ) )
				head = m_termFactory.getFunctionalTerm( "Q", extraAtomArguments[0], extraAtomArguments[1]);
			else if ( queryVarsSoFar.contains( extraAtomArguments[0] ) )
				head = m_termFactory.getFunctionalTerm( "Q", extraAtomArguments[0] );
			else if ( queryVarsSoFar.contains( extraAtomArguments[1] ) )
				head = m_termFactory.getFunctionalTerm( "Q", extraAtomArguments[1] );
		if ( head == null ) {
			System.err.println( "\ncomputeRewritingOfAtomAs Tree ERROR: " + extraAtom + " " + queryVarsSoFar + " " + firstTree);
			System.exit(0);
		}
		Term[] ebody = new Term[1];
		ebody[0] = extraAtom;
		TreeNode<Clause> rootElement = new TreeNode<Clause>( new Clause( ebody , head) );
		Tree<Clause> rewritingDAG = new Tree<Clause>(rootElement);

		HashMap<String, TreeNode<Clause>> m_canonicalsToRewOfExtraAtom = new HashMap<String, TreeNode<Clause>>();
		m_canonicalsToRewOfExtraAtom.put(rootElement.getNodeLabel().m_canonicalRepresentation, rootElement );
		Stack<TreeNode<Clause>> toVisit = new Stack<TreeNode<Clause>>();
		toVisit.push(rootElement);
		while(!toVisit.isEmpty()) {
			TreeNode<Clause> currentNode = toVisit.pop();
			Clause currentNodeClause = currentNode.getNodeLabel();
			for (PI pi : pis) {
				Clause cl = applyPositiveInclusion(pi, 0, currentNodeClause);
				if (cl != null) {
					logger.debug( cl + " was produced by " + currentNodeClause );
					if (!( cl.getBody()[0].getArity() == 1 && Integer.parseInt( cl.getBody()[0].getArgument( 0 ).toString().substring(1, cl.getBody()[0].getArgument( 0 ).toString().length())) > 500 )) {
						TreeNode<Clause> newClauseNode = null;
						TreeNode<Clause> nodeInRew = m_canonicalsToRewOfExtraAtom.get(cl.m_canonicalRepresentation);
						if (nodeInRew == null) {
							newClauseNode = new TreeNode<Clause>( cl );
							m_canonicalsToRewOfExtraAtom.put(cl.m_canonicalRepresentation, newClauseNode );
							toVisit.push( newClauseNode );
						}
						else
							newClauseNode = nodeInRew;

						currentNode.addChild( newClauseNode );
					}
				}
			}
		}
		localSkolemIndex++;
		return rewritingDAG;
	}

	private Tree<Clause> joinTreeWithExtraAtomTree( Tree<Clause> t1 , Tree<Clause> t2 ) {


		Tree<Clause> finalTree = new Tree<Clause>();
		ClauseExtensionCache clauseExtensionCache = new ClauseExtensionCache();
		//Do we need to keep the nodes generated in previous runs??
		m_canonicalsToDAGNodes = new HashMap<String,TreeNode<Clause>>();

		TreeNode<Clause> t1Root = t1.getRootElement();
		TreeNode<Clause> t2Root = t2.getRootElement();

		Clause t1RootClause = t1Root.getNodeLabel();
		Clause t2RootClause = t2Root.getNodeLabel();

		Set<TreeNode<Clause>> alreadyUsedT1 = new HashSet<TreeNode<Clause>>();

		if (isEligibleForProcessing( t1RootClause, t2RootClause , substitutionsMap.get( t1RootClause.m_canonicalRepresentation ) ) ) {
			Clause rootClause = clauseExtensionCache.extendClauseWithTerm( t1RootClause, t2RootClause );
			TreeNode<Clause> rootNode = new TreeNode<Clause>( rootClause );
			
			finalTree.setRootElement( rootNode );

			Substitution sub = clauseExtensionCache.isContainedIn(t1RootClause, t2RootClause);
			
//			if (sub != null)
//				System.out.println( sub + "\t\t" + t1RootClause + "\t\t" + t2RootClause );
			if ( sub != null )
				if ( sub.isEmpty() ) {
					if (t2RootClause.getBody()[0].getArity() == 1 || sub.isEmpty() )
						return t1;
					else if ( t2RootClause.getBody()[0].getArity() == 2 ) {
						rootNode.addChild( t1Root );
						return finalTree;
					}
				}
				else {
					Variable mappedVariable = sub.keySet().iterator().next();
					//mappedVariable exists in t1.rootNode
					if ( t1RootClause.getVariables().contains( mappedVariable )  )
						//We do not create t1+t2 because it has already been created (finalTree.setRootElement( rootNode ))
						for ( TreeNode<Clause> t1Child : t1Root.getChildren() ) {
							Clause t1ChildClause = t1Child.getNodeLabel();

							//t1ChildClause does not contain equalRole which has been replaced by a concept
							if ( !t1ChildClause.m_canonicalRepresentation.contains( equalRole.toString() ) &&
									findTermThatReplacesEqualRole( t1RootClause , t1ChildClause ).getArity() == 1) {

								TreeNode<Clause> t1NewChild = renameGraph(t1Child,sub);
								rootNode.addChild( t1NewChild );

								addSubstitutionToSubTree(sub, t1NewChild );
								alreadyUsedT1.add( t1Child );
							} //else
								//;
						}
					else if (t2.getRootElement().getNodeLabel().getBody()[0].getArity() == 1 ) {
						addSubstitutionToSubTree( sub, t1.getRootElement() );
//						return t1;
					}
					else if ( t2.getRootElement().getNodeLabel().getBody()[0].getArity() == 2 ) {
						addSubstitutionToSubTree( sub, t1.getRootElement() );
						rootNode.addChild( t1.getRootElement() );
//						return finalTree;
					}
				}
			m_canonicalsToDAGNodes.put(rootClause.m_canonicalRepresentation, rootNode);
		}
		else
			return t1;
		
//		printTree(finalTree);

		Queue<TreeNode<Clause>> queueT1 = new LinkedList<TreeNode<Clause>>(Collections.singleton(t1.getRootElement()));
		while (!queueT1.isEmpty()) {
			TreeNode<Clause> currentT1 = queueT1.poll();

			if (alreadyUsedT1.contains(currentT1))
				continue;
			alreadyUsedT1.add(currentT1);

			Clause currentT1Clause = currentT1.getNodeLabel();
			if ( isEligibleForProcessing( currentT1Clause, t2.getRootElement().getNodeLabel(), substitutionsMap.get(currentT1Clause.m_canonicalRepresentation) ) ) {
				Queue<TreeNode<Clause>> queueT2 = new LinkedList<TreeNode<Clause>>(Collections.singleton(t2.getRootElement()));

				Set<TreeNode<Clause>> alreadyUsedT2 = new LinkedHashSet<TreeNode<Clause>>();
				while (!queueT2.isEmpty()) {
					TreeNode<Clause> currentT2 = queueT2.poll();

					if (alreadyUsedT2.contains( currentT2 ))
						continue;
					alreadyUsedT2.add(currentT2);

//					System.out.println( "ADDING " + currentT1Clause + "\tTO\t" + currentT2.getNodeLabel() + " \tWITH\t" + renameExtraAtom + "\t\t" + substitutionsMap.get(currentT1Clause.m_canonicalRepresentation) );
					
					Clause currentClauseExtended;
					if ( renameExtraAtom ) {
						currentClauseExtended = addTermToBodyOfClauseNoEqCheck(currentT1Clause, getNewQuery( substitutionsMap.get(currentT1Clause.m_canonicalRepresentation), currentT2.getNodeLabel() ) );
						renameExtraAtom = false;
					}
					else
						currentClauseExtended = addTermToBodyOfClauseNoEqCheck(currentT1Clause, currentT2.getNodeLabel());

					TreeNode<Clause> currentNodeInFinalTree = getEquivalentNodeAlreadyInDAG( currentClauseExtended );
					if (currentNodeInFinalTree == null)
						currentNodeInFinalTree = new TreeNode<Clause>( currentClauseExtended );
					
//					System.out.println( "CURRENT NODE = " + currentNodeInFinalTree.getNodeLabel() );

//					boolean subTreeHasBeenCopied=false;
					//bazoume sto currentT1+currentT2 san paidia tou ton currentT1+paidiaTouCurrentT2
					for (TreeNode<Clause> childOfCurrentT2 : currentT2.getChildren()) {
						Substitution sub = clauseExtensionCache.isContainedIn( currentT1Clause, childOfCurrentT2.getNodeLabel() );
						if ( sub != null ) {
							//identical substitution
							if ( sub.isEmpty() ) {
								currentNodeInFinalTree.addChild( currentT1 );
								alreadyUsedT1.addAll(currentT1.getChildren());
//								subTreeHasBeenCopied=true;
//								break;
							}
							//exists substitution
							else {
								Variable mappedVariable = sub.entrySet().iterator().next().getKey();

								Clause newClause = clauseExtensionCache.extendClauseWithTerm( currentT1Clause, childOfCurrentT2.getNodeLabel() );
								TreeNode<Clause> newNode = getEquivalentNodeAlreadyInDAG(newClause);
								if ( newNode == null )
									newNode = new TreeNode<Clause> ( newClause );
								
								currentNodeInFinalTree.addChild( newNode );
								m_canonicalsToDAGNodes.put(newClause.m_canonicalRepresentation, newNode);
//								substitutionsMap.put(newClause.m_canonicalRepresentation, addSubstitution( substitutionsMap.get( newClause.m_canonicalRepresentation ) , substitutionsMap.get(currentT1Clause.m_canonicalRepresentation) ) );
								
								//mappedVariable exists in currentT1Clause
								if ( currentT1Clause.getVariables().contains(mappedVariable) ) {

									boolean childOfCurrentT2InQ = false;
									//must see if equalRole is contained in its children (or replaced by a role) or if it has been replaced by a concept
									for ( TreeNode<Clause> childOfCurrentT1Node : currentT1.getChildren() ) {
										Clause childOfCurrentT1Clause = childOfCurrentT1Node.getNodeLabel();
										//not contained in children and instead exists a concept
//										//equalRole can be null only when possitives are used in isContained
//										if ( equalRole == null )
//											equalRole = findTermThatReplacesEqualRole(currentT1Clause, childOfCurrentT2.getNodeLabel());
										if ( !childOfCurrentT1Clause.m_canonicalRepresentation.contains( equalRole.toString() ) &&
												findTermThatReplacesEqualRole( currentT1Clause , childOfCurrentT1Clause ).getArity() == 1 ) {

											TreeNode<Clause> newChildOfCurrentT1 = renameGraph( childOfCurrentT1Node, sub );
											newNode.addChild(newChildOfCurrentT1);
											addSubstitutionToSubTree(sub, newChildOfCurrentT1);
											alreadyUsedT1.add( childOfCurrentT1Node );
										} else
											childOfCurrentT2InQ = true;
//											if ( !queueT2.contains(childOfCurrentT2) )
//												queueT2.add(childOfCurrentT2);
									}
									if ( childOfCurrentT2InQ )
										queueT2.add(childOfCurrentT2);
								}
								//mappedVariable does not exist in currentT1Clause
								else {
									currentNodeInFinalTree.addChild( currentT1 );
									addSubstitutionToSubTree( sub, currentT1 );
//									alreadyUsedT1.addAll(currentT1.getChildren());
//									subTreeHasBeenCopied=true;
//									break;
								}
							}
						}
						else {
							Clause newClause = clauseExtensionCache.extendClauseWithTerm( currentT1Clause, childOfCurrentT2.getNodeLabel() );
							TreeNode<Clause> newNode = getEquivalentNodeAlreadyInDAG(newClause);
							if ( newNode == null )
								newNode = new TreeNode<Clause> ( newClause );
							queueT2.add(childOfCurrentT2);
							currentNodeInFinalTree.addChild( newNode );
							m_canonicalsToDAGNodes.put(newClause.m_canonicalRepresentation, newNode);
						}
					}
//					if( subTreeHasBeenCopied )
//						break;
					//bazoume ston currentT1+currentT2 san paidia tou ta paidiaToucurrentT1+currentT2
					Set<TreeNode<Clause>> currentT1Children = currentT1.getChildren();
					for (TreeNode<Clause> childOfCurrentT1 : currentT1Children) {
						if (isEligibleForProcessing(childOfCurrentT1.getNodeLabel() , t2.getRootElement().getNodeLabel(), substitutionsMap.get(childOfCurrentT1.getNodeLabel().m_canonicalRepresentation) )) {
							//term appears in the body of clause to be joined
							Substitution sub = clauseExtensionCache.isContainedIn(childOfCurrentT1.getNodeLabel(), currentT2.getNodeLabel());
							if ( sub != null ) {
								//identical substitution (role or concept)
								if ( sub.isEmpty() )
									currentNodeInFinalTree.addChild( childOfCurrentT1 );
								//not identical substitution (role)
								else {
									Variable mappedVariable = sub.entrySet().iterator().next().getKey();

									Clause newClause = clauseExtensionCache.extendClauseWithTerm( childOfCurrentT1.getNodeLabel() , currentT2.getNodeLabel() );
									TreeNode<Clause> newNode = getEquivalentNodeAlreadyInDAG(newClause);
									if ( newNode == null )
										newNode = new TreeNode<Clause> ( newClause );
									
									currentNodeInFinalTree.addChild( newNode );
									m_canonicalsToDAGNodes.put(newClause.m_canonicalRepresentation, newNode);
//									substitutionsMap.put(newClause.m_canonicalRepresentation, addSubstitution( substitutionsMap.get( newClause.m_canonicalRepresentation ) , substitutionsMap.get(childOfCurrentT1.getNodeLabel().m_canonicalRepresentation) ) );
									
									//mappedVariable exists in currentT1Clause0
									if ( currentT1Clause.getVariables().contains(mappedVariable) ) {
										boolean childOfCurrentT1InQ = false;
										//must see if equalRole is contained in its children (or replaced by a role) or if it has been replaced by a concept
										for ( TreeNode<Clause> childOfChildOfCurrentT1 : childOfCurrentT1.getChildren() ) {
											Clause childOfChildOfCurrentT1Clause = childOfChildOfCurrentT1.getNodeLabel();
											//replaced by a concept
											if ( !childOfChildOfCurrentT1Clause.m_canonicalRepresentation.contains( equalRole.toString() ) &&
													findTermThatReplacesEqualRole( childOfCurrentT1.getNodeLabel(), childOfChildOfCurrentT1Clause ).getArity() == 1 ) {
												TreeNode<Clause> newChildOfCurrentT1 = renameGraph(childOfCurrentT1 , sub);												
												newNode.addChild(newChildOfCurrentT1);
												addSubstitutionToSubTree(sub, newChildOfCurrentT1);
												alreadyUsedT1.add( childOfCurrentT1 );
											} else
												childOfCurrentT1InQ = true;
//												if ( !queueT1.contains(childOfCurrentT1) )
//													queueT1.add(childOfCurrentT1);
										}
										if ( childOfCurrentT1InQ )
											queueT1.add(childOfCurrentT1);
									} else {
										currentNodeInFinalTree.addChild(childOfCurrentT1);
//										addSubstitutionToSubTree(sub, childOfCurrentT1);
									}
								}
							}
							else {
								Clause newClause;
								if (renameExtraAtom) {
									newClause= clauseExtensionCache.extendClauseWithTerm( childOfCurrentT1.getNodeLabel(), getNewQuery(substitutionsMap.get( childOfCurrentT1.getNodeLabel().m_canonicalRepresentation ), currentT2.getNodeLabel() ) );
									renameExtraAtom = false;
								}
								else
									newClause= clauseExtensionCache.extendClauseWithTerm( childOfCurrentT1.getNodeLabel(), currentT2.getNodeLabel() );
								TreeNode<Clause> newNode = getEquivalentNodeAlreadyInDAG(newClause);
								if ( newNode == null )
									newNode = new TreeNode<Clause>(newClause);

								currentNodeInFinalTree.addChild( newNode );

								queueT1.add(childOfCurrentT1);
								m_canonicalsToDAGNodes.put(newClause.m_canonicalRepresentation, newNode);
							}
						}
					}
				}
			}
		}

//		if (print) {
//			System.out.println("\n\n");
//			for ( Entry<String, TreeNode<Clause>> entry : m_canonicalsToDAGNodes.entrySet())
//				System.out.println( entry.getKey() );
//			System.out.println("\n\n");
//			printTree(finalTree);
//			System.out.println("\n\n");
//
//		}
		
//		System.out.println( "\n\nSubstitutions: ");
//		for ( String en : substitutionsMap.keySet() ) {
//			System.out.println( en+ "\t\t" + substitutionsMap.get(en) );
//		}
//		printTree(finalTree);
		return finalTree;
	}


	private Term findTermThatReplacesEqualRole(Clause originalClause, Clause newClause) {

		Term[] newBody = newClause.getBody();
		for ( int i = 0 ; i < newBody.length ; i++ )
			if ( !originalClause.m_canonicalRepresentation.contains( newBody[i].toString() ) )
				return newBody[i];
		return null;
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
	public Clause getNewQuery(Substitution mgu, Clause clause){

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

        return new Clause(body, head);
	}



	private void addSubstitutionToSubTree(Substitution sub,	TreeNode<Clause> node) {

		Set<Clause> subTreeAsSet = node.getSubTreeAsSet();
		subTreeAsSet.add(node.getNodeLabel());

//		System.out.println( "Add Sub to subtree" + sub + "\t\t\t" + subTreeAsSet); 

		for ( Clause clause : subTreeAsSet ) {
			//replace the substitution of clause with one that also contains sub
//			System.out.println( "\nAdding Substitution to " + clause + "\t\t" + substitutionsMap.get(clause.m_canonicalRepresentation) + "\t\t" + sub + "\n");
			Substitution newSub = null;
			if (substitutionsMap.get(clause.m_canonicalRepresentation)!=null) {
				newSub = addSubstitution(substitutionsMap.get(clause.m_canonicalRepresentation), sub);
//				System.out.println ( "\t\t\t\t\t" + sub + "+" + substitutionsMap.get(clause.m_canonicalRepresentation) + " = " + newSub);
				if ( !substitutionsMap.get(clause.m_canonicalRepresentation).isEmpty() )
					substitutionsMap.remove(clause.m_canonicalRepresentation);
			}
			else
				newSub = sub;

			substitutionsMap.put(clause.m_canonicalRepresentation, newSub);
//			System.out.println(clause + "\t\t" + substitutionsMap.get(clause.m_canonicalRepresentation) + "\n");
		}

	}

	private TreeNode<Clause> getEquivalentNodeAlreadyInDAG( Clause newClause ){
		return m_canonicalsToDAGNodes.get(newClause.m_canonicalRepresentation);
	}

	private Clause addTermToBodyOfClauseNoEqCheck(Clause clauseFromH1, Clause clauseFromH2) {

		Term[] body = clauseFromH1.getBody();
		Term[] newBody = new Term[body.length + 1];

		for (int i = 0 ; i < body.length ; i++)
			newBody[i] = body[i];
		newBody[body.length] = clauseFromH2.getBody()[0];
		return new Clause( newBody, clauseFromH1.getHead() );
	}

	private Substitution isEqualRoleTerm( Clause currentQuery, Term roleAtom, Term bodyAtom ) {

		Substitution s = new Substitution();

		if (bodyAtom.getName().equals(roleAtom.getName())) {
			Term[] roleAtomVariables = roleAtom.getArguments();
			Term[] bodyAtomVariables = bodyAtom.getArguments();

			if (bodyAtomVariables[1].equals( roleAtomVariables[1] ) && bodyAtomVariables[0].equals( roleAtomVariables[0]))
				return s;
			else if ( bodyAtomVariables[0].toString().equals( roleAtomVariables[0].toString() ) ) {
				s.put( (Variable) roleAtomVariables[1], bodyAtomVariables[1]);
				return s;
			}
			else if ( bodyAtomVariables[1].toString().equals( roleAtomVariables[1].toString() ) ) {
				s.put( (Variable) roleAtomVariables[0], bodyAtomVariables[0]);
				return s;
			}
		}
		return null;
	}

	//Returns true if avar(extra) is a subset of var(clause)
	public boolean isEligibleForProcessing(Clause clause, Clause atomClause , Substitution sub) {

		ArrayList<Variable> atomClauseDistinguishedVars = atomClause.getDistinguishedVariables();
		ArrayList<Variable> clauseVariables = clause.getVariables();

		if ( clauseVariables.containsAll( atomClauseDistinguishedVars ) )
			return true;
		else //one distinguished variable
			if ( atomClauseDistinguishedVars.size() == 1 ) {
				if ( findMappedVariableInClause( clause , sub , atomClauseDistinguishedVars.get( 0 ) ) ) {
					renameExtraAtom = true;
					return true;
				}
				else if ( findMappedVariableInClause( clause , sub , atomClauseDistinguishedVars.get( 0 ) ) &&
					findMappedVariableInClause( clause , sub , atomClauseDistinguishedVars.get( 1 ) ) ) {
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

		if ( clauseVariables.contains( currentVar ) )
			return true;

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

	public Term[] findRightOrderOfQuery(Clause query) {
		Set<Term> queryBodyTerms = new HashSet<Term>();
		Set<Term> queryDistVars = new HashSet<Term>(query.getDistinguishedVariables());

		for (Term origQueryTerm : query.getBody())
			queryBodyTerms.add( origQueryTerm );

		LabeledGraph<Term, Term, Term> queryGraph = new LabeledGraph<Term,Term,Term>();
		for (Term origQueryTerm : query.getBody()) {

			Term[] variablesOfTerm = origQueryTerm.getArguments();
			if (variablesOfTerm.length == 2)
				queryGraph.addEdge(variablesOfTerm[0], variablesOfTerm[1], origQueryTerm);
			else
				queryGraph.addLabel(variablesOfTerm[0], origQueryTerm);
		}
		Term[] body = new Term[queryBodyTerms.size()];
		Set<Term> rootVarsThatAreDistinct = new HashSet<Term>();
		Set<Term> rootVarsThatAreNotDistinct = new HashSet<Term>();
		Stack<Term> toVisit = new Stack<Term>();
//		for (Term vertice : queryGraph.getElements())
////			if (queryGraph.getPredecessors(vertice).isEmpty() )
//				// These lines are for starting from the rootDistinguished variables and not from any root variable
//				if (queryDistVars.contains(vertice))
//					rootVarsThatAreDistinct.add(vertice);
//				else
//					rootVarsThatAreNotDistinct.add(vertice);
////				toVisit.add(vertice);	//This is for starting from any rootVariable
//		// These lines are for starting from the rootDistinguished variables and not from any root variable
//		toVisit.addAll(rootVarsThatAreNotDistinct);
//		toVisit.addAll(rootVarsThatAreDistinct);
//
//		if (toVisit.isEmpty())
			toVisit.addAll(queryDistVars);
		Set<Term> visitedNodes = new HashSet<Term>();
		int orderedQueryIndex=0;
		Set<Term> coneptAtoms = new HashSet<Term>();
        while (!toVisit.isEmpty()) {
        	Term currentVar = toVisit.pop();
        	if (visitedNodes.contains(currentVar))
        		continue;
        	for (LabeledGraph<Term,Term,Term>.Edge edge : queryGraph.getSuccessors(currentVar))
        		if (!visitedNodes.contains(edge.getToElement())) {
	        		body[orderedQueryIndex++] = edge.getEdgeLabel();
	        		toVisit.add(edge.getToElement());
        		}
        	for (LabeledGraph<Term,Term,Term>.Edge edge : queryGraph.getPredecessors(currentVar))
        		if (!edge.getToElement().equals(currentVar) && !visitedNodes.contains(edge.getToElement())) {
	        		body[orderedQueryIndex++] = edge.getEdgeLabel();
	        		toVisit.add(edge.getToElement());
        		}
        	visitedNodes.add( currentVar );
       		coneptAtoms.addAll(queryGraph.getLabelsOfNode(currentVar));
        }
        for (Term conceptAtom : coneptAtoms)
        	body[orderedQueryIndex++] = conceptAtom;
        orderedQueryIndex=0;
        return body;
	}

	public static Clause applyPositiveInclusion(PI pi, int atomIndex, Clause clause){

		Term newAtom = null;
		Term g = clause.getBody()[atomIndex];

		if (g.getArity() == 1) {
			Variable var1 = (Variable)g.getArguments()[0];
			if (pi.m_right.equals(g.getName()))
				switch (pi.m_type) {
				case 1:
					newAtom = m_termFactory.getFunctionalTerm(pi.m_left, m_termFactory.getVariable(var1.m_index));
					break;
				case 4:
						newAtom = m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{m_termFactory.getVariable(var1.m_index), m_termFactory.getVariable(500+(localSkolemIndex))});
					break;
				case 7:
						newAtom = m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{m_termFactory.getVariable(500+(localSkolemIndex)), m_termFactory.getVariable(var1.m_index)});
					break;
				default:
					return null;
				}
			else
				return null;
		}
		// Binary atom
		else{
			Variable var1 = (Variable)g.getArguments()[0];
			Variable var2 = (Variable)g.getArguments()[1];

			if(pi.m_right.equals(g.getName())){
				if(!clause.isBound(var2))
					switch(pi.m_type){
					case 2:
						newAtom = m_termFactory.getFunctionalTerm(pi.m_left, m_termFactory.getVariable(var1.m_index));
						break;
					case 5:
							newAtom = m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{m_termFactory.getVariable(var1.m_index), m_termFactory.getVariable(500+(localSkolemIndex))});
						break;
					case 8:
							newAtom = m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{m_termFactory.getVariable(500+(localSkolemIndex)), m_termFactory.getVariable(var1.m_index)});
						break;
					case 10:
						newAtom = m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{m_termFactory.getVariable(var1.m_index), m_termFactory.getVariable(var2.m_index)});
						break;
					case 11:
						newAtom = m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{m_termFactory.getVariable(var2.m_index), m_termFactory.getVariable(var1.m_index)});
						break;
					default:
						return null;
					}
				else if(!clause.isBound(var1))
					switch(pi.m_type){
					case 3:
						newAtom = m_termFactory.getFunctionalTerm(pi.m_left, m_termFactory.getVariable(var2.m_index));
						break;
					case 6:
							newAtom = m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{m_termFactory.getVariable(var2.m_index), m_termFactory.getVariable(500+(localSkolemIndex))});
						break;
					case 9:
							newAtom = m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{m_termFactory.getVariable(500+(localSkolemIndex)), m_termFactory.getVariable(var2.m_index)});
						break;
					case 10:
						newAtom = m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{m_termFactory.getVariable(var1.m_index), m_termFactory.getVariable(var2.m_index)});
						break;
					case 11:
						newAtom = m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{m_termFactory.getVariable(var2.m_index), m_termFactory.getVariable(var1.m_index)});
						break;
					default:
						return null;
					}
				else
					switch (pi.m_type) {
					case 10:
						newAtom = m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{m_termFactory.getVariable(var1.m_index), m_termFactory.getVariable(var2.m_index)});
						break;
					case 11:
						newAtom = m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{m_termFactory.getVariable(var2.m_index), m_termFactory.getVariable(var1.m_index)});
						break;
					default:
						return null;
					}
			}
			else
				return null;
		}
		Set<Term> newBody = new LinkedHashSet<Term>();
		newBody.add(newAtom);
		// Copy the other atoms from the clause
	    for (int index=0; index < clause.getBody().length; index++)
	    	 if (index != atomIndex)
		    	 newBody.add(clause.getBody()[index].apply(Substitution.IDENTITY, m_termFactory));

	    // New body and head
	    Term[] body = new Term[newBody.size()];
	    newBody.toArray(body);
	    Term head = clause.getHead().apply(Substitution.IDENTITY, m_termFactory);

	    return new Clause(body, head);
	}

	private Substitution addSubstitution(Substitution s, Substitution sub) {

		if ( s == null )
			return sub;
		
		if ( sub == null )
			return null;
		
		Substitution subst = new Substitution();
		for ( Entry<Variable, Term> e : s.entrySet() )
			subst.put(e.getKey(), e.getValue());
		subst.putAll(sub);
		return subst;
	}

	private class ClauseExtensionCache {
		private Map<Clause,Set<Clause>> nodesToPossitive = new HashMap<Clause,Set<Clause>> ();
		private Map<Clause,Set<Clause>> nodesToNegative = new HashMap<Clause,Set<Clause>> ();
		private Map<String,Clause> clausesToTheirExtension = new HashMap<String,Clause> ();

		private Substitution isContainedIn(Clause clauseFromH1, Clause clauseFromH2) {
			Term[] body = clauseFromH1.getBody();
			Term termFromH2 = clauseFromH2.getBody()[0];
			String termString = termFromH2.toString();
			if (termFromH2.getArity() == 1) {
				for (int i = 0 ; i < body.length ; i++)
					if ( termString.equals( body[i].toString() ) )
						return new Substitution();
			}
			else if (termFromH2.getArity() == 2) {
				equalRole = null;
				for (int i = 0 ; i < body.length ; i++) {
					Substitution sub = isEqualRoleTerm(clauseFromH1, termFromH2, body[i]);
					if ( sub != null ) {
						substitutionsMap.put(clauseFromH1.m_canonicalRepresentation, addSubstitution( substitutionsMap.get(clauseFromH1.m_canonicalRepresentation ), sub ) );
						equalRole = body[i];
						return sub;
					}
				}
			}
			return null;
		}

		// Adds new term to the body of clause and creates a new clause. We also keep track of the terms of the body of the clause that are equal to term
		private Clause extendClauseWithTerm(Clause clauseFromH1, Clause clauseFromH2) {
			Clause cl = clausesToTheirExtension.get(clauseFromH1.toString()+clauseFromH2.toString());
			if (cl!=null)
				return cl;
			Term[] body = clauseFromH1.getBody();
			Term[] newBody = new Term[body.length + 1];
			Term termFromH2 = clauseFromH2.getBody()[0];

			if (termFromH2.getArity() == 1)
				for (int i = 0 ; i < body.length ; i++)
					newBody[i] = body[i];
			else if (termFromH2.getArity() == 2)
				for (int i = 0 ; i < body.length ; i++)
					newBody[i] = body[i];
			newBody[body.length] = termFromH2;
			cl = new Clause(newBody, clauseFromH1.getHead());
			clausesToTheirExtension.put(clauseFromH1.toString()+clauseFromH2.toString(), cl);
			return cl;
		}
	}
	
	public void printTree( Tree<Clause> tree) {

		System.out.println("START");
//		Queue<Node<T>> queue = new LinkedList<Node<T>>();
		Set<TreeNode<Clause>> queue = new HashSet<TreeNode<Clause>>();
		queue.add( tree.getRootElement() );
		Set<TreeNode<Clause>> alreadyAddedToQueue = new HashSet<TreeNode<Clause>>();
		Set<TreeNode<Clause>> alreadyPrinted = new HashSet<TreeNode<Clause>>();
		alreadyAddedToQueue.add( tree.getRootElement() );

		while ( !queue.isEmpty() ) {
//			Node<T> cn = queue.poll();
			TreeNode<Clause> cn = queue.iterator().next();
			queue.remove(cn);
			if ( alreadyPrinted.contains(cn) )
				continue;
//			if ( !cn.getNodeLabel().containsAUXPredicates() )
				System.out.println( cn.getNodeLabel() + "\t\t\t" + substitutionsMap.get(cn.getNodeLabel().m_canonicalRepresentation));
			alreadyPrinted.add( cn );
			Set<TreeNode<Clause>> cnChl = cn.getChildren();
			for ( TreeNode<Clause> nc : cnChl )
			{
//				if ( !nc.getNodeLabel().containsAUXPredicates() )
					System.out.println( "\t\t\t\t" + nc.getNodeLabel() + "\t\t" + substitutionsMap.get(nc.getNodeLabel().m_canonicalRepresentation));
				if ( !alreadyAddedToQueue.contains( nc ))
				{
					queue.add( nc );
					alreadyAddedToQueue.add( nc );
				}
			}
		}
		System.out.println("END Printing tree \n");
	}
}