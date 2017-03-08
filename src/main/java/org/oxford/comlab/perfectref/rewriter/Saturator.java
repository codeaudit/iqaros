package org.oxford.comlab.perfectref.rewriter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.Map.Entry;

import org.apache.log4j.Logger;
import org.apache.log4j.PropertyConfigurator;

import edu.ntua.image.datastructures.Tree;
import edu.ntua.image.datastructures.TreeNode;

@SuppressWarnings("unused")

public class Saturator {
	protected static Logger	logger = Logger.getLogger( Saturator.class );

	private TermFactory m_termFactory;
	protected ArrayList<String> m_clausesCanonicals;
	protected ArrayList<Clause> m_workedOffClauses;
	protected ArrayList<Clause> m_unprocessedClauses;
	private ArrayList<TreeNode<Clause>> m_unprocessedNodes;


	public Saturator(TermFactory termFactory) {
		m_termFactory = termFactory;
		m_workedOffClauses = new ArrayList<Clause>();
		m_unprocessedClauses = new ArrayList<Clause>();
		m_clausesCanonicals = new ArrayList<String>();

		PropertyConfigurator.configure("./logger.properties");
	}

	public TermFactory getTermFactory(){
		return this.m_termFactory;
	}

	// Saturates a set of clauses
	public ArrayList<Clause> saturate(ArrayList<PI> pis, Clause query) {

		long start = System.currentTimeMillis();

//		System.out.println( "Rewriting query is: " + query + "\n");
		logger.info( "Rewriting query is: " + query + "\n");

		int inferences = 0;
		this.m_unprocessedClauses.add(query);

		while (!m_unprocessedClauses.isEmpty()) {
			Clause givenClause = m_unprocessedClauses.remove(0);

			/*if(m_workedOffClauses.size()%100 == 0){
				System.out.println(m_workedOffClauses.size());
			}*/

			m_workedOffClauses.add(givenClause);
			m_clausesCanonicals.add(givenClause.m_canonicalRepresentation);

			for(int i = 0; i < givenClause.getBody().length; i++)
				for(PI pi: pis){
					Clause newQuery = getNewQuery(pi, i, givenClause);
					if (newQuery!= null){
//						System.out.println("From \t" + givenClause + "\t\tis produced\t\t" + newQuery );
						inferences++;
						if(!isRedundant(newQuery)) {
//							for ( Substitution s : givenClause.getUnifications() )
//								newQuery.addUnification( s );
							m_unprocessedClauses.add(newQuery);
							m_clausesCanonicals.add(newQuery.m_canonicalRepresentation);
						}
					}
				}

			for(int i = 0; i < givenClause.getBody().length - 1; i++)
				for(int j = i+1; j < givenClause.getBody().length; j++){
//					/**
//					 * optimised condensation
//					 */
//		        	Term te1 = givenClause.getBody()[i];
//		        	Term te2 = givenClause.getBody()[j];
////		        	boolean shouldCondensate=false;
//		        	if( (te1.getArguments().length==2 && te2.getArguments().length==1) || (te2.getArguments().length==2 && te1.getArguments().length==1))
//		        		continue;
//		        	if( te1.getArguments().length==2 && te2.getArguments().length==2) {
//		        		if( !te1.getArguments()[0].equals(te2.getArguments()[0]) && !te1.getArguments()[1].equals(te2.getArguments()[1]) )
//		        			continue;
//		        	}
//		        	/** end of optimised condensation */
					Substitution unifier = Substitution.mostGeneralUnifier(givenClause.getBody()[i], givenClause.getBody()[j], this.m_termFactory);
			        if (unifier != null) {
//			        	System.out.println(shouldCondensate);
//						System.out.println( givenClause.getBody()[j] + " " + unifier );
			        	inferences++;
						Clause newQuery = getNewQuery(unifier, givenClause);
						if (!isRedundant(newQuery)) {
//							System.out.println("\t\tFrom \t" + givenClause + "\t\tis produced\t\t" + newQuery );
//							for ( Substitution s : givenClause.getUnifications() )
//								newQuery.addUnification( s );
//							for ( Entry<Variable,Term> s : unifier.entrySet() ) {
////								if ( ! ( Integer.parseInt( s.getKey().toString().substring( 1 , s.getKey().toString().length() ) ) >= 500 || Integer.parseInt( s.getValue().toString().substring( 1 , s.getValue().toString().length() ) ) >= 500 ) ) {
//									Substitution ns = new Substitution();
//									ns.put( s.getKey(), s.getValue() );
//									newQuery.addUnification( ns );
//								}
							m_unprocessedClauses.add(newQuery);
							m_clausesCanonicals.add(newQuery.m_canonicalRepresentation);
						}
					}
				}
		}

//		System.out.println("Inferences: " + inferences);

		m_workedOffClauses = pruneAUX(); //Prune the AUX

		long endBefSub = System.currentTimeMillis();
//		System.out.println( "Size of UCQ before subsumption = " + m_workedOffClauses.size() + " in " + ( endBefSub - start ) + "ms");
		logger.info( "Size of UCQ before subsumption = " + m_workedOffClauses.size() + " in " + ( endBefSub - start ) + "ms");

//		m_workedOffClauses = subsumptionCheck(); //A posteriori containment check

//		long end = System.currentTimeMillis();

//		System.out.println( "Subsumption produced UCQ size =" + m_workedOffClauses.size() + " in " + ( end - endBefSub ) + "ms");
//		System.out.println( "OVERALL time is " + ( end - start ) + "ms\n");
//
//		logger.info( "Subsumption produced UCQ size =" + m_workedOffClauses.size() + " in " + ( end - endBefSub ) + "ms");
//		logger.info( "OVERALL time is " + ( end - start ) + "ms\n\n");

		return m_workedOffClauses;
	}

	public Clause getNewQuery(PI pi, int atomIndex, Clause clause){

		Term newAtom = null;
		Term g = clause.getBody()[atomIndex];

		//Unary atom
		if(g.getArity() == 1){
			Variable var1 = (Variable)g.getArguments()[0];
			if(pi.m_right.equals(g.getName()))
				switch(pi.m_type){
				case 1:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var1.m_index));
					break;
				case 4:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(500)});
					break;
				case 7:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500), this.m_termFactory.getVariable(var1.m_index)});
					break;
				default:
					return null;
				}
			else
				return null;
		}
		//Binary atom
		else{
			Variable var1 = (Variable)g.getArguments()[0];
			Variable var2 = (Variable)g.getArguments()[1];

			if(pi.m_right.equals(g.getName())){
				if(!clause.isBound(var2))
					switch(pi.m_type){
					case 2:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var1.m_index));
						break;
					case 5:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(500)});
						break;
					case 8:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500), this.m_termFactory.getVariable(var1.m_index)});
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
						break;
					case 6:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(500)});
						break;
					case 9:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500), this.m_termFactory.getVariable(var2.m_index)});
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
					switch(pi.m_type){
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
		//Copy the other atoms from the clause
	    for (int index=0; index < clause.getBody().length; index++)
			if (index != atomIndex)
				newBody.add(clause.getBody()[index].apply(Substitution.IDENTITY, this.m_termFactory));

	    //New body and head
	    Term[] body = new Term[newBody.size()];
	    newBody.toArray(body);
	    Term head = clause.getHead().apply(Substitution.IDENTITY, this.m_termFactory);

	    Clause newQuery = new Clause(body, head);
	    return newQuery;

	    //Rename variables in resolvent
//	    ArrayList<Variable> variablesNewQuery = newQuery.getVariables();
//
//	    HashMap<Variable,Integer> variableMapping = new HashMap<Variable,Integer>();
//	    for(int i=0; i < variablesNewQuery.size(); i++)
//			variableMapping.put(variablesNewQuery.get(i),i);
//	    Clause newQueryRenamed = newQuery.renameVariables(this.m_termFactory, variableMapping);
//
//	    return newQueryRenamed;
	}

	public Clause getNewQueryNoRename(PI pi, int atomIndex, Clause clause){

		Term newAtom = null;
		Term g = clause.getBody()[atomIndex];

		//Unary atom
		if(g.getArity() == 1){
			Variable var1 = (Variable)g.getArguments()[0];
			if(pi.m_right.equals(g.getName()))
				switch(pi.m_type){
				case 1:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var1.m_index));
					break;
				case 4:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(500)});
					break;
				case 7:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500), this.m_termFactory.getVariable(var1.m_index)});
					break;
				default:
					return null;
				}
			else
				return null;
		}
		//Binary atom
		else{
			Variable var1 = (Variable)g.getArguments()[0];
			Variable var2 = (Variable)g.getArguments()[1];

			if(pi.m_right.equals(g.getName())){
				if(!clause.isBound(var2))
					switch(pi.m_type){
					case 2:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var1.m_index));
						break;
					case 5:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(500)});
						break;
					case 8:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500), this.m_termFactory.getVariable(var1.m_index)});
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
						break;
					case 6:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(500)});
						break;
					case 9:
						newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(500), this.m_termFactory.getVariable(var2.m_index)});
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
					switch(pi.m_type){
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
		//Copy the other atoms from the clause
	    for (int index=0; index < clause.getBody().length; index++)
			if (index != atomIndex)
				newBody.add(clause.getBody()[index].apply(Substitution.IDENTITY, this.m_termFactory));

	    //New body and head
	    Term[] body = new Term[newBody.size()];
	    newBody.toArray(body);
	    Term head = clause.getHead().apply(Substitution.IDENTITY, this.m_termFactory);

	    return new Clause(body, head);
	}

	/**
	 * Creates a new query by applying the mgu of two atoms to a given query
	 * @param mgu
	 * @param clause
	 * @return
	 */
	private Clause getNewQuery(Substitution mgu, Clause clause){

		Set<Term> newBody = new LinkedHashSet<Term>();
        //Copy the atoms from the main premise
        for (int index=0; index < clause.getBody().length; index++)
			newBody.add(clause.getBody()[index].apply(mgu, this.m_termFactory));

        //New body and head
        Term[] body = new Term[newBody.size()];
        newBody.toArray(body);
        Term head = clause.getHead().apply(mgu, this.m_termFactory);

        Clause newQuery = new Clause(body, head);
        return newQuery;
        //Rename variables in new query
//        ArrayList<Variable> variablesNewQuery = newQuery.getVariables();
//        HashMap<Variable,Integer> variableMapping = new HashMap<Variable,Integer>();
//        for(int i=0; i < variablesNewQuery.size(); i++)
//			variableMapping.put(variablesNewQuery.get(i),i);
//        Clause newQueryRenamed = newQuery.renameVariables(this.m_termFactory, variableMapping);
//
//		return newQueryRenamed;
	}

	/**
	 * Checks if a given clause is contained in m_clausesCanonicals based on its naive canonical representation
	 */
	private boolean isRedundant(Clause clause) {
		if(m_clausesCanonicals.contains(clause.m_canonicalRepresentation))
			return true;
		else{
			for(Clause unprocessedClause: this.m_unprocessedClauses)
				if(unprocessedClause.isEquivalentUpToVariableRenaming(clause))
					return true;
			for(Clause workedOffClause: this.m_workedOffClauses)
				if(workedOffClause.isEquivalentUpToVariableRenaming(clause))
					return true;
		}
		return false;
	}

	private ArrayList<Clause> subsumptionCheck() {
		ArrayList<Clause> result = new ArrayList<Clause>();
		this.m_clausesCanonicals.clear();

		boolean c1IsSubsumed;

		for (Clause c1 : this.m_workedOffClauses)
			for (Clause c2 : this.m_workedOffClauses)
				if(!c1.equals(c2) && !c1.toBeIgnored && !c2.toBeIgnored)
					if(c2.subsumes(c1)&& c1.subsumes(c2))
						if(c1.m_canonicalRepresentation.length() < c2.m_canonicalRepresentation.length())
							c2.toBeIgnored = true;
						else
							c1.toBeIgnored = true;

		for (Clause c1 : this.m_workedOffClauses)
			if(!c1.toBeIgnored){
				c1IsSubsumed = false;
				for (Clause c2 : this.m_workedOffClauses)
					if(!c2.toBeIgnored)
						if(!c1.equals(c2))
							if(c2.subsumes(c1)){
								c1IsSubsumed = true;
								break;
							}
				if(!c1IsSubsumed)
					result.add(c1);
			}

		return result;
	}

/*
 * Get rid of AUXs.
 */
private ArrayList<Clause> pruneAUX() {
	ArrayList<Clause> result = new ArrayList<Clause>();

	for(Clause c1 : this.m_workedOffClauses)
		if(!c1.containsAUXPredicates())
			result.add(c1);
	return result;
	}

/**
 * getSubsumees returns the subsumee
 * @param pi
 * @param g
 * @return
 */
	public Term getSubsumees(PI pi , Term g ){

		Term newAtom = null;

		int gArity = g.getArity();
		String name = g.getName();
		//Unary atom
		if(gArity == 1){
			Variable var1 = (Variable)g.getArguments()[0];
			if(pi.m_right.equals( name ))
				switch(pi.m_type){
				case 1:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, this.m_termFactory.getVariable(var1.m_index));
					break;
				case 4:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(5000)});
					break;
				case 7:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(5000), this.m_termFactory.getVariable(var1.m_index)});
					break;
				default:
					return null;
				}
			else
				return null;
		}
		//Binary atom
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
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var1.m_index), this.m_termFactory.getVariable(5000)});
					break;
				case 6:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(var2.m_index), this.m_termFactory.getVariable(5000)});
					break;
				case 8:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(5000), this.m_termFactory.getVariable(var1.m_index)});
					break;
				case 9:
					newAtom = this.m_termFactory.getFunctionalTerm(pi.m_left, new Term[]{this.m_termFactory.getVariable(5000), this.m_termFactory.getVariable(var2.m_index)});
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

	    return newAtom;
	}

	// Saturates a set of clauses
	public Tree<Clause> saturateRetTree(ArrayList<PI> pis, Clause query) {
		int inferences = 0;

		this.m_unprocessedNodes = new ArrayList<TreeNode<Clause>>();


		TreeNode<Clause> rootElement = new TreeNode<Clause>( query );
		Tree<Clause> tree = new Tree<Clause>(rootElement) ;

		TreeNode<Clause> givenNode;

		this.m_unprocessedNodes.add(rootElement);

		int idIndex = 1;

		while (!m_unprocessedNodes.isEmpty()) {

			givenNode = m_unprocessedNodes.remove( 0 );
			Clause givenClause = givenNode.getNodeLabel();

			m_workedOffClauses.add(givenClause);
			m_clausesCanonicals.add(givenClause.m_canonicalRepresentation);

			for(int i = 0; i < givenClause.getBody().length; i++)
				for(PI pi: pis){
					Clause newQuery = getNewQuery(pi, i, givenClause);
					if (newQuery!= null){
						inferences++;
						if(!isRedundant(newQuery)) {

							TreeNode<Clause> newNode = new TreeNode<Clause>( newQuery );
							givenNode.addChild( newNode );
							m_unprocessedNodes.add( newNode );
	//						m_unprocessedClauses.add(newQuery);
							m_clausesCanonicals.add(newQuery.m_canonicalRepresentation);
	//						System.out.println( "Clause produced from getNewQuery = \t" + newQuery );
						}
					}
				}

			for(int i = 0; i < givenClause.getBody().length - 1; i++)
				for(int j = i+1; j < givenClause.getBody().length; j++){
					Substitution unifier = Substitution.mostGeneralUnifier(givenClause.getBody()[i], givenClause.getBody()[j], this.m_termFactory);
			        if (unifier != null){
			        	inferences++;
						Clause newQuery = getNewQuery(unifier, givenClause);
	//					System.out.println( givenClause + "\t" + newQuery);
						if (!isRedundant(newQuery)) {
							TreeNode<Clause> newNode = new TreeNode<Clause>( newQuery );

							givenNode.addChild( newNode );

							m_unprocessedNodes.add( newNode );
	//						m_unprocessedClauses.add(newQuery);
							m_clausesCanonicals.add(newQuery.m_canonicalRepresentation);
						}
					}
				}
		}

	//	System.out.println("Inferences: " + inferences);

		//m_workedOffClauses = pruneAUX(); //Prune the AUX

		//m_workedOffClauses = subsumptionCheck(); //A posteriori containment check

		return tree;
	}

}