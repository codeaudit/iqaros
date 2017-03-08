package org.oxford.comlab.perfectref.optimizer;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeSet;

import org.apache.log4j.Logger;
import org.oxford.comlab.perfectref.rewriter.Clause;
import org.oxford.comlab.perfectref.rewriter.Substitution;
import org.oxford.comlab.perfectref.rewriter.Term;
import org.oxford.comlab.perfectref.rewriter.TermFactory;
import org.oxford.comlab.perfectref.rewriter.Variable;


public class Optimizer {

	private TermFactory m_termFactory;

	protected static Logger	logger = Logger.getLogger( Optimizer.class );

	public Optimizer(TermFactory termFactory){
		this.m_termFactory = termFactory;
	}

	/**
	 * Prunes a set of clauses based on the dependency graph from a specific predicate
	 * @return
	 */
	public ArrayList<Clause> pruneWithDependencyGraph(String pred, ArrayList<Clause> clauses){
		ArrayList<Clause> result = new ArrayList<Clause>();

		ArrayList<String> predicatesToProcess = new ArrayList<String>();
		HashSet<String> reachablePredicates = new HashSet<String>();

		predicatesToProcess.add(pred);
		while(predicatesToProcess.size() > 0){
			String p = predicatesToProcess.get(0);
			predicatesToProcess.remove(p);

			if(!reachablePredicates.contains(p)){
				reachablePredicates.add(p);
				predicatesToProcess.addAll(getDirectReachablePredicates(p, clauses));
			}
		}

		//Keep clauses with reachable heads only
		for(Clause c : clauses)
			if(reachablePredicates.contains(c.getHead().getName()))
				result.add(c);
		return result;
	}

	private ArrayList<String> getDirectReachablePredicates(String p, ArrayList<Clause> clauses){
		ArrayList<String> result = new ArrayList<String>();

		for(Clause c : clauses)
			if(p.equals(c.getHead().getName()))
				for(Term t: c.getBody())
					result.add(t.getName());
		return result;
	}

	public Set<Clause> querySubsumptionCheck(Set<Clause> checked, Set<Clause> notChecked) {
		Set<Clause> result = new HashSet<Clause>();

		boolean subsumed = false;

		//Identify equivalent clauses
		for (Clause c1 : notChecked ) {
			subsumed = false;
			for (Clause c2 : checked )
				if ( c2.subsumes( c1 ) )
				{
					subsumed = true;
					break;
				}
			if ( !subsumed )
				result.add( c1 );
		}
		result.addAll( checked );
		return result;
	}

	/**
	 * @author gstoil
	 */
	public ArrayList<Clause> querySubsumptionCheck(ArrayList<Clause> clauses) {
		ArrayList<Clause> result = new ArrayList<Clause>(clauses);
		TreeSet<Clause> clausesOrdered = new TreeSet<Clause>(clauses);
		Set<Clause> redundant = new HashSet<Clause>();
		for (Clause c1 : clausesOrdered){
			if (redundant.contains(c1))
				continue;
			for (Clause c2 : clausesOrdered) {
				if (redundant.contains(c2) || c1.equals(c2))
						continue;
				if (c1.subsumes(c2)) {
					result.remove(c2);
					redundant.add(c2);
					c2.setSubsumer(c1);
				}
				else if (c2.subsumes(c1)) {
					redundant.add(c1);
					result.remove(c1);
					c1.setSubsumer(c2);
					break;
				}
			}
		}
		return result;
	}

	public ArrayList<Clause> querySubsumptionCheckWithRestriction(ArrayList<Clause> clauses, Set<Clause> possibleNonRedundantClauses) {
//		logger.debug( possibleNonRedundantClauses.size() + " possible non-redundant clauses that are going to be skipped" );
		if (possibleNonRedundantClauses == null)
			return querySubsumptionCheck(clauses);

		ArrayList<Clause> result = new ArrayList<Clause>(clauses);
		Set<Clause> toBeTested = new HashSet<Clause>(clauses);
		toBeTested.removeAll(possibleNonRedundantClauses);
		if(!toBeTested.isEmpty()) {
			TreeSet<Clause> clausesOrdered = new TreeSet<Clause>(clauses);
			Set<Clause> redundant = new HashSet<Clause>();

			for (Clause c1 : toBeTested)
				for (Clause c2 : clausesOrdered) {
					if (redundant.contains(c2) || c1.equals(c2))
						continue;
					if (c2.subsumes(c1)) {
						redundant.add(c1);
						result.remove(c1);
						c1.setSubsumer(c2);
						break;
					}
					else if (c1.subsumes(c2)) {
						result.remove(c2);
						redundant.add(c2);
						c2.setSubsumer(c1);
					}
				}
		}
		return result;
	}

	public Set<Clause> pruneAUX(Set<Clause> clauses){
		HashSet<String> IDBPredicates = new HashSet<String>();
		HashSet<String> EDBPredicates = new HashSet<String>();
		Set<Clause> result = new HashSet<Clause>();

		// Compute the IDB predicates
   	for(Clause c : clauses)
		IDBPredicates.add(c.getHead().getName());

   	// Compute the EDB predicates
   	for(Clause c : clauses)
		for(Term t: c.getBody())
   			if(!IDBPredicates.contains(t.getName()))
				EDBPredicates.add(t.getName());

   	//Prune clauses with AUX EDB predicates
		for(Clause c : clauses){
			boolean isToBePruned = false;
			for(Term t: c.getBody()){
				if(t.getName().contains("AUX-"))
					if(EDBPredicates.contains(t.getName())){
						isToBePruned = true;
						break;
					}
				try{
					//Auxiliary symbols introduced in the normalization (HermiT)
					Integer.parseInt(t.getName());
					if(EDBPredicates.contains(t.getName())){
						isToBePruned = true;
						break;
					}
				}
				catch(NumberFormatException e){}
			}

			if(!isToBePruned)
				result.add(c);
		}

		return result;
	}


	public ArrayList<Clause> pruneAUX(ArrayList<Clause> clauses){
		HashSet<String> IDBPredicates = new HashSet<String>();
		HashSet<String> EDBPredicates = new HashSet<String>();
		ArrayList<Clause> result = new ArrayList<Clause>();

		// Compute the IDB predicates
   	for(Clause c : clauses)
		IDBPredicates.add(c.getHead().getName());

   	// Compute the EDB predicates
   	for(Clause c : clauses)
		for(Term t: c.getBody())
   			if(!IDBPredicates.contains(t.getName()))
				EDBPredicates.add(t.getName());

   	//Prune clauses with AUX EDB predicates
		for(Clause c : clauses){
			boolean isToBePruned = false;
			for(Term t: c.getBody()){
				if(t.getName().contains("AUX-"))
					if(EDBPredicates.contains(t.getName())){
						isToBePruned = true;
						break;
					}
				try{
					//Auxiliary symbols introduced in the normalization (HermiT)
					Integer.parseInt(t.getName());
					if(EDBPredicates.contains(t.getName())){
						isToBePruned = true;
						break;
					}
				}
				catch(NumberFormatException e){}
			}

			if(!isToBePruned)
				result.add(c);
		}

		return result;
	}
	public Set<Clause> condensate(Set<Clause> clauses){

		Set<Clause> result = new HashSet<Clause>();

		for(Clause c:clauses)
			result.add(condensate(c));

		return result;
	}

	public ArrayList<Clause> condensate(ArrayList<Clause> clauses){

		ArrayList<Clause> result = new ArrayList<Clause>();

		for(Clause c:clauses)
			result.add(condensate(c));

		return result;
	}

	public Clause condensate(Clause clause){

		ArrayList<Clause> unprocessed = new ArrayList<Clause>();
		ArrayList<Clause> condensations = new ArrayList<Clause>();

		unprocessed.add(clause);

		while(!unprocessed.isEmpty()){
			Clause givenClause = unprocessed.remove(0);
			condensations.add(givenClause);
			for(int i = 0; i < givenClause.getBody().length - 1; i++)
				for(int j = i+1; j < givenClause.getBody().length; j++){
					Substitution unifier = Substitution.mostGeneralUnifier(givenClause.getBody()[i], givenClause.getBody()[j], m_termFactory);
					if (unifier != null){
						Clause newQuery = getNewQuery(unifier, givenClause);

						boolean isRedundant = false;
						for(Clause unprocessedClause: unprocessed)
							if(unprocessedClause.isEquivalentUpToVariableRenaming(newQuery))
								isRedundant = true;

						if(!isRedundant)
							for(Clause workedOffClause: condensations)
								if(workedOffClause.isEquivalentUpToVariableRenaming(newQuery))
									isRedundant = true;

						if(!isRedundant)
							unprocessed.add(newQuery);
	                }
				}
		}

		Collections.sort(condensations, new Comparator<Clause>(){
			public int compare(Clause c1, Clause c2){
			    return (new Integer(c1.getBody().length)).compareTo(new Integer(c2.getBody().length));
			}
		});

		for(Clause c: condensations)
			if(c.subsumes(clause))
				return c;

		return clause;

	}

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

       //Rename variables in new query
       ArrayList<Variable> variablesNewQuery = newQuery.getVariables();
       HashMap<Variable,Integer> variableMapping = new
       HashMap<Variable,Integer>();

       for(int i=0; i < variablesNewQuery.size(); i++)
		variableMapping.put(variablesNewQuery.get(i),i);

       Clause newQueryRenamed = newQuery.renameVariables(this.m_termFactory, variableMapping);

       return newQueryRenamed;
	}
}
