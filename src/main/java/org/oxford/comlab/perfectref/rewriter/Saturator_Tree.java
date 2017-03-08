package org.oxford.comlab.perfectref.rewriter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import edu.ntua.image.datastructures.Tree;
import edu.ntua.image.datastructures.TreeNode;

public class Saturator_Tree {
	private TermFactory m_termFactory;
	protected ArrayList<TreeNode<Clause>> m_nodesAddedToTree;
	protected ArrayList<Clause> m_unprocessedClauses;
	private ArrayList<TreeNode<Clause>> m_unprocessedNodes;
	private Map<String,TreeNode<Clause>> m_canonicalsToDAGNodes;
//	private Variable lostVariable;

//	public Variable getLostVariable() {
//		return lostVariable;
//	}

	private int skolemIndex = 0;;

	public Saturator_Tree(TermFactory termFactory) {
		m_termFactory = termFactory;
		m_unprocessedClauses = new ArrayList<Clause>();
		m_nodesAddedToTree = new ArrayList<TreeNode<Clause>>();
		m_canonicalsToDAGNodes = new HashMap<String,TreeNode<Clause>>();
	}

	public Clause getNewQuery(PI pi, int atomIndex, Clause clause){

		Term newAtom = null;
		Term g = clause.getBody()[atomIndex];

//		lostVariable = null;

		if(g.getArity() == 1){
			Variable var1 = (Variable)g.getArguments()[0];
			if(pi.m_right.equals(g.getName()))
				switch(pi.m_type){
				case 1:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var1.m_index));
					break;
				case 4:
//					if ( clauseContainsVarLargerThan( clause , 500 ) )
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(500+(skolemIndex++))});
//					else
//						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(500)});
					break;
				case 7:
//					if (clauseContainsVarLargerThan( clause , 500 ) )
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500+(skolemIndex++)), this.m_termFactory.getVariable(var1.m_index)});
//					else
//						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500), this.m_termFactory.getVariable(var1.m_index)});
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
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var1.m_index));
//						lostVariable = var2;
						break;
					case 5:
//						if ( clauseContainsVarLargerThan( clause , 500 ) )
							newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(500+(skolemIndex++))});
//						else
//							newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(500)});
						break;
					case 8:
//						if ( clauseContainsVarLargerThan( clause , 500 ) )
							newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500+(skolemIndex++)), this.m_termFactory.getVariable(var1.m_index)});
//						else
//							newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500), this.m_termFactory.getVariable(var1.m_index)});
						break;
					case 10:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(var2.m_index)});
						break;
					case 11:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(var1.m_index)});
						break;
					default:
						return null;
					}
				else if(!clause.isBound(var1))
					switch(pi.m_type){
					case 3:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var2.m_index));
//							lostVariable = var1;
						break;
					case 6:
//							if ( clauseContainsVarLargerThan( clause, 500 ) )
							newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(500+(skolemIndex++))});
//							else
//								newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(500)});
						break;
					case 9:
//							if ( clauseContainsVarLargerThan( clause , 500 ) )
							newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500+(skolemIndex++)), this.m_termFactory.getVariable(var2.m_index)});
//							else
//								newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500), this.m_termFactory.getVariable(var2.m_index)});
						break;
					case 10:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(var2.m_index)});
						break;
					case 11:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(var1.m_index)});
						break;
					default:
						return null;
					}
				else
					switch (pi.m_type) {
					case 10:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(var2.m_index)});
						break;
					case 11:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(var1.m_index)});
						break;
					default:
						return null;
					}
			} else
				return null;
		}

		Set<Term> newBody = new LinkedHashSet<Term>();
		newBody.add(newAtom);
		// Copy the other atoms from the clause
	    for (int index=0; index < clause.getBody().length; index++)
	    	 if (index != atomIndex)
		    	 newBody.add(clause.getBody()[index].apply(Substitution.IDENTITY, this.m_termFactory));

	    // New body and head
	    Term[] body = new Term[newBody.size()];
	    newBody.toArray(body);
	    Term head = clause.getHead().apply(Substitution.IDENTITY, this.m_termFactory);

	    Clause newQuery = new Clause(body, head);

//	    // Rename variables in resolvent
//	    ArrayList<Variable> variablesNewQuery = newQuery.getVariables();
//
//	    HashMap<Variable,Integer> variableMapping = new HashMap<Variable,Integer>();
//	    for(int i=0; i < variablesNewQuery.size(); i++)
//	     	variableMapping.put(variablesNewQuery.get(i),i);
//
//	    Clause newQueryRenamed = newQuery.renameVariables(this.m_termFactory, variableMapping);
	    return newQuery;
	}

	public Clause getNewQueryForIncremental(PI pi, int atomIndex, Clause clause, int localSkolem){

		Term newAtom = null;
		Term g = clause.getBody()[atomIndex];

//		lostVariable = null;

		if(g.getArity() == 1){
			Variable var1 = (Variable)g.getArguments()[0];
			if(pi.m_right.equals(g.getName()))
				switch(pi.m_type){
				case 1:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var1.m_index));
					break;
				case 4:
//					if ( clauseContainsVarLargerThan( clause , 500 ) )
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(500+(localSkolem))});
//					else
//						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(500)});
					break;
				case 7:
//					if (clauseContainsVarLargerThan( clause , 500 ) )
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500+(localSkolem)), this.m_termFactory.getVariable(var1.m_index)});
//					else
//						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500), this.m_termFactory.getVariable(var1.m_index)});
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
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var1.m_index));
//						lostVariable = var2;
						break;
					case 5:
//						if ( clauseContainsVarLargerThan( clause , 500 ) )
							newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(500+(localSkolem))});
//						else
//							newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(500)});
						break;
					case 8:
//						if ( clauseContainsVarLargerThan( clause , 500 ) )
							newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500+(localSkolem)), this.m_termFactory.getVariable(var1.m_index)});
//						else
//							newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500), this.m_termFactory.getVariable(var1.m_index)});
						break;
					case 10:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(var2.m_index)});
						break;
					case 11:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(var1.m_index)});
						break;
					default:
						return null;
					}
				else if(!clause.isBound(var1))
					switch(pi.m_type){
					case 3:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var2.m_index));
//							lostVariable = var1;
						break;
					case 6:
//							if ( clauseContainsVarLargerThan( clause, 500 ) )
							newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(500+(localSkolem))});
//							else
//								newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(500)});
						break;
					case 9:
//							if ( clauseContainsVarLargerThan( clause , 500 ) )
							newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500+(localSkolem)), this.m_termFactory.getVariable(var2.m_index)});
//							else
//								newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500), this.m_termFactory.getVariable(var2.m_index)});
						break;
					case 10:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(var2.m_index)});
						break;
					case 11:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(var1.m_index)});
						break;
					default:
						return null;
					}
				else
					switch (pi.m_type) {
					case 10:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(var2.m_index)});
						break;
					case 11:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(var1.m_index)});
						break;
					default:
						return null;
					}
			} else
				return null;
		}

		Set<Term> newBody = new LinkedHashSet<Term>();
		newBody.add(newAtom);
		// Copy the other atoms from the clause
	    for (int index=0; index < clause.getBody().length; index++)
	    	 if (index != atomIndex)
		    	 newBody.add(clause.getBody()[index].apply(Substitution.IDENTITY, this.m_termFactory));

	    // New body and head
	    Term[] body = new Term[newBody.size()];
	    newBody.toArray(body);
	    Term head = clause.getHead().apply(Substitution.IDENTITY, this.m_termFactory);

	    Clause newQuery = new Clause(body, head);

//	    // Rename variables in resolvent
//	    ArrayList<Variable> variablesNewQuery = newQuery.getVariables();
//
//	    HashMap<Variable,Integer> variableMapping = new HashMap<Variable,Integer>();
//	    for(int i=0; i < variablesNewQuery.size(); i++)
//	     	variableMapping.put(variablesNewQuery.get(i),i);
//
//	    Clause newQueryRenamed = newQuery.renameVariables(this.m_termFactory, variableMapping);
	    return newQuery;
	}

	private boolean clauseContainsVarLargerThan(Clause clause , int max) {

		for ( Variable var : clause.getVariables() )
			if ( Integer.parseInt( var.toString().substring( 1 , var.toString().length() ) ) >= max )
				return true;
		return false;
	}

	/**
	 * Creates a new query by applying the mgu of two atoms to a given query
	 */
	private Clause getNewQuery(Substitution mgu, Clause clause){


		Set<Term> newBody = new LinkedHashSet<Term>();
       //Copy the atoms from the main premise
		/*
		 * CHECK HERE
		 *
		 * I arxiki de douleuei swsta me to paradeigma TestABC
		 */
       for (int index=0; index < clause.getBody().length; index++)
		//    	   boolean exists = false;
//    	   for (Iterator<Term> iter = newBody.iterator() ; iter.hasNext() ;)
//    		   if ( iter.next().toString().equals(clause.getBody()[index].apply(mgu, this.m_termFactory).toString()) )
//    			   exists = true;
//    		if (!exists)
		   newBody.add(clause.getBody()[index].apply(mgu, this.m_termFactory));

       //New body and head
       Term[] body = new Term[newBody.size()];
       newBody.toArray(body);
       Term head = clause.getHead().apply(mgu, this.m_termFactory);

       Clause newQuery = new Clause(body, head);

       return newQuery;

//       Substitution sub = new Substitution();

//       //Rename variables in new query
//       boolean rename = true;
//       ArrayList<Variable> variablesNewQuery = newQuery.getVariables();
//       HashMap<Variable,Integer> variableMapping = new HashMap<Variable,Integer>();
//       for(int i=0; i < variablesNewQuery.size(); i++) {
//    	   variableMapping.put(variablesNewQuery.get(i), i);
//    	   if ( ( Integer.parseInt( variablesNewQuery.get( i ).toString().substring( 1 , variablesNewQuery.get( i ).toString().length() ) ) >= 500 ) ) {
//    		   rename = false;
//    		   return newQuery;
//    	   }
////    	   if ( !( Integer.parseInt( variablesNewQuery.get( i ).toString().substring( 1 , variablesNewQuery.get( i ).toString().length() ) ) >= 500 ) )
////    		   sub.put(variablesNewQuery.get(i), new Variable( i ) );
//       }
//
//       Clause newQueryRenamed = newQuery.renameVariables(this.m_termFactory, variableMapping);
//
//       if ( newQueryRenamed.m_canonicalRepresentation.contains("degreeFrom(X1,X2) ^ headOf(X0,X2)") )
//    	   System.out.println( newQuery + "\t\t" + variableMapping );
//
//       //avenet
////       newQueryRenamed.addUnification( sub );
//
//       return newQueryRenamed;
	}

	/**
	 * Checks if a given clause is contained in m_clausesCanonicals based on its naive canonical representation
	 */
	public TreeNode<Clause> getEquivalentNodeAlreadyInDAG(TreeNode<Clause> newNode) {
		/**
		 * Option 1
		 */
//		Node<Clause> nodeInTree = m_canonicalsToDAGNodes.get(newNode.getNodeLabel().m_canonicalRepresentation);
//		if( nodeInTree !=null )
//			return nodeInTree;

		/**
		 * Option 2
		 */
		TreeNode<Clause> nodeInTree = m_canonicalsToDAGNodes.get(newNode.getNodeLabel().m_canonicalRepresentation);
		if( nodeInTree !=null )
			return nodeInTree;
		for (TreeNode<Clause> nodeInRewritingTree : m_nodesAddedToTree)
			if (nodeInRewritingTree.getNodeLabel().isEquivalentUpToVariableRenaming(newNode.getNodeLabel()))
				return nodeInRewritingTree;

		/**
		 * Option 3
		 */
//		for (Node<Clause> nodeInRewritingTree : m_nodesAddedToTree)
//		if (nodeInRewritingTree.getNodeLabel().isEquivalentUpToVariableRenaming(newNode.getNodeLabel()))
//			return nodeInRewritingTree;
		return null;
	}


	/**
	 * Η συνάρτηση αυτή δεν περιέχει όλους τους κανόνες που υπάρχουν στην getNewQuery επειδή όταν μας δίνεται ένα άτομο R(x,y) σαν extraAtom τότε μας ενδιαφέρουν να υπάρχουν και οι 2 μεταβλητές.
	 * Η συνάρτηση αυτή στην refine χρησιμοποιείται σε συνδυασμό με τον έλγχο για το εάν το clause στο οποίο πάμε να κάνουμε refine περιέχει κάποια από τις μεταβλητές που έχει το άτομο (clause)
	 * που παράγεται από αυτή τη συνάρτηση.
	 * @param pi
	 * @param clause
	 * @return
	 */
	public Clause getSubsumees(PI pi , Clause clause ){

		Term newAtom = null;
		Term g = clause.getBody()[0];

		int gArity = g.getArity();
		String name = g.getName();
		if(gArity == 1){
			Variable var1 = (Variable)g.getArguments()[0];
			if(pi.m_right.equals( name ))
				switch(pi.m_type){
				case 1:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var1.m_index));
					break;
				case 4:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(50000)});
					break;
				case 7:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(50000), this.m_termFactory.getVariable(var1.m_index)});
					break;
				default:
					return null;
				}
			else
				return null;
		}
		else{
			Variable var1 = (Variable)g.getArguments()[0];
			Variable var2 = (Variable)g.getArguments()[1];

			if(pi.m_right.equals( name ))
				//			if(!clause.isBound(var2)){
				switch(pi.m_type){
				case 2:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var1.m_index));
					break;
				case 3:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var2.m_index));
					break;
				case 5:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(50000)});
					break;
				case 6:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(50000)});
					break;
				case 8:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(50000), this.m_termFactory.getVariable(var1.m_index)});
					break;
				case 9:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(50000), this.m_termFactory.getVariable(var2.m_index)});
					break;
				case 10:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(var2.m_index)});
					break;
				case 11:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(var1.m_index)});
					break;
				default:
					return null;
//				}
}
			else
				return null;
		}
		Term [] body = new Term[1];
		body[0] = newAtom;
	    return new Clause ( body, clause.getHead() );
	}

	public Tree<Clause> saturate(ArrayList<PI> pis, Clause query) {

		m_unprocessedNodes = new ArrayList<TreeNode<Clause>>();
		TreeNode<Clause> givenNode;

		TreeNode<Clause> rootElement = new TreeNode<Clause>( query );
		Tree<Clause> rewritingDAG = new Tree<Clause>(rootElement) ;
		m_unprocessedNodes.add(rootElement);
		while (!m_unprocessedNodes.isEmpty()) {

			givenNode = m_unprocessedNodes.remove( 0 );
			Clause givenClause = givenNode.getNodeLabel();
//			System.out.println( "m_nodesAddedToTree contains " + givenNode.getNodeLabel() + " is " + m_nodesAddedToTree.contains( givenNode ) );
			m_nodesAddedToTree.add(givenNode);

			for (int i = 0; i < givenClause.getBody().length; i++)
				for (PI pi: pis) {
					Clause newQuery = getNewQuery(pi, i, givenClause);
					if (newQuery!=null) {

						TreeNode<Clause> newNode = new TreeNode<Clause>( newQuery );
						TreeNode<Clause> nodeInRewritingDAG = getEquivalentNodeAlreadyInDAG(newNode);
						if (nodeInRewritingDAG==null) {
							for ( Substitution s : givenNode.getNodeLabel().getUnifications() )
								newNode.getNodeLabel().addUnification( s );
							givenNode.addChild(newNode);
							m_unprocessedNodes.add(newNode);
							m_nodesAddedToTree.add(newNode);
							m_canonicalsToDAGNodes.put(newQuery.m_canonicalRepresentation, newNode);
						}
						//if commented on june 8th
						else //if (!nodeInRewritingDAG.getSubTree().contains(givenNode))
							givenNode.addChild( nodeInRewritingDAG );
					}
				}
			for (int i = 0; i < givenClause.getBody().length - 1; i++)
				for (int j = i+1; j < givenClause.getBody().length; j++) {
					Substitution unifier = Substitution.mostGeneralUnifier(givenClause.getBody()[i], givenClause.getBody()[j], this.m_termFactory);
//					System.out.println( "GivenClause = " + givenClause + "\t\tUnifier = " + unifier + "\t\t" + givenClause.getBody()[i] + "\t\t" + givenClause.getBody()[j]);
			        if (unifier!=null) {
						Clause newQuery = getNewQuery(unifier, givenClause);

						TreeNode<Clause> newNode = new TreeNode<Clause>( newQuery );
						TreeNode<Clause> nodeInRewritingDAG = getEquivalentNodeAlreadyInDAG(newNode);
						if(nodeInRewritingDAG==null) {
							for ( Substitution s : givenNode.getNodeLabel().getUnifications() )
								newNode.getNodeLabel().addUnification( s );
							for ( Entry<Variable,Term> s : unifier.entrySet() ) {
//								if ( ! ( Integer.parseInt( s.getKey().toString().substring( 1 , s.getKey().toString().length() ) ) >= 500 || Integer.parseInt( s.getValue().toString().substring( 1 , s.getValue().toString().length() ) ) >= 500 ) ) {
									Substitution ns = new Substitution();
									ns.put( s.getKey(), s.getValue() );
									newNode.getNodeLabel().addUnification( ns );
								}
							givenNode.addChild( newNode );
							m_unprocessedNodes.add( newNode );
							m_nodesAddedToTree.add( newNode );
							m_canonicalsToDAGNodes.put(newQuery.m_canonicalRepresentation, newNode);
						}
						//if commented on june 8th
						else //if (!nodeInRewritingDAG.getSubTree().contains(givenNode))
							givenNode.addChild( nodeInRewritingDAG );
					}
				}
		}
		return rewritingDAG;
	}

}