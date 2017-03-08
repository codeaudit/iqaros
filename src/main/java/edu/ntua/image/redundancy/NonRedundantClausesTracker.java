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

package edu.ntua.image.redundancy;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.apache.log4j.Logger;
import org.oxford.comlab.perfectref.rewriter.Clause;
import org.oxford.comlab.perfectref.rewriter.Term;
import org.oxford.comlab.perfectref.rewriter.Variable;

import edu.ntua.image.refinement.RewritingExtensionManager;

public class NonRedundantClausesTracker extends RedundancyElimination {
	private Map<Term,Boolean> termIsContainedInSomeClause;
	private Set<Clause> tempPossiblyNonRedundant = new HashSet<Clause>();
	private Set<Clause> nonRedundantClauses = new HashSet<Clause>();
	private Set<Clause> tempNonSubsumerClausesExtended = new HashSet<Clause>();
	private Set<Clause> nonSubsumerClausesExtended = new HashSet<Clause>();
	private Map<Clause,Set<Clause>> possibleNonRedundantClauses = new HashMap<Clause,Set<Clause>>();
	private Set<Clause> activeSubsumers = new HashSet<Clause>();

	protected static Logger	logger = Logger.getLogger( NonRedundantClausesTracker.class );
	
	@Override
	public void checkAndMarkClauseAsPossiblyNonRedundant(Clause currentClause, Term extraTerm, Clause newClause) {
		if (!termIsContainedInSomeClause.containsKey(extraTerm) && currentClause.getSubsumer()==null) {
			tempPossiblyNonRedundant.add(newClause);
//			if (nonSubsumerClauses.contains(currentClause))
//				nonSubsumerClausesExtended.add(newClause);
		}
		if (nonSubsumerClauses.contains(currentClause) && !currentClause.toString().contains(extraTerm.getName()))
			nonSubsumerClausesExtended.add(newClause);
	}

	@Override
	public void checkAndMarkClauseAsNonRedundant(Clause newClause) {
		if (newClause.getSubsumer()==null)
			nonRedundantClauses.add(newClause);
	}

	@Override
	public void flush(Clause currentClause) {
		possibleNonRedundantClauses.put(currentClause,tempPossiblyNonRedundant);
		tempPossiblyNonRedundant = new HashSet<Clause> ();
	}

	@Override
	public void initialise(RewritingExtensionManager rewExtensionMngr, Set<Clause> ucqOfReducedAsRew, Set<Term> rewOfNewAtom) {

		markRedundantAndNonRedundantClauses(ucqOfReducedAsRew);

		termIsContainedInSomeClause = new HashMap<Term,Boolean>();
		for (Term subsTerm : rewOfNewAtom)
			for (Clause cl : ucqOfReducedAsRew)
				if (subsTerm.getArity()==1 && conceptAtomAppearsInQueryBody(subsTerm , cl.getBody() )) {
//				if (subsTerm.getArity()==1 && rewExtensionMngr.conceptAtomAppearsInQueryBody(subsTerm , cl.getBody() )) {
//				if (subsTerm.getArity()==1 && rewExtensionMngr.isEligibleForProcessing( cl )) {
					termIsContainedInSomeClause.put(subsTerm, true);
					break;
				}
//				else if (subsTerm.getArity()==2 && rewExtensionMngr.roleAtomAppearsInQueryBody( subsTerm , cl )) {
				else if (subsTerm.getArity()==2 && roleAtomAppearsInQueryBody( subsTerm , cl )) {
//				else if (subsTerm.getArity()==2 && rewExtensionMngr.isEligibleForProcessing( cl )) {
					termIsContainedInSomeClause.put(subsTerm, true);
					break;
				}
		for (Clause nonSubsumer : nonSubsumerClauses) {
			boolean found = false;
			for (Term subTerm :rewOfNewAtom)
				if (nonSubsumer.toString().contains(subTerm.getName())) {
					found = true;
					break;
				}
			if (!found)
				tempNonSubsumerClausesExtended.add(nonSubsumer);
		}
	}

	public boolean roleAtomAppearsInQueryBody(Term roleAtom, Clause currentQuery ) {
		for (Term bodyAtom : currentQuery.getBody())
			if (bodyAtom.getArity() == 2 && bodyAtom.getName().equals( roleAtom.getName()) )
				return true;
		return false;
	}

	public boolean conceptAtomAppearsInQueryBody(Term conceptAtom, Term[] queryBodyAtoms) {
		for (Term bodyAtom : queryBodyAtoms)
			if (bodyAtom.getName().equals(conceptAtom.getName()))
				return true;
		return false;
	}

	@Override
	public ArrayList<Clause> removeRedundantClauses(ArrayList<Clause> clauses) {
		if (nonRedundantClauses == null)
			return standardSubsumptionCheck(clauses);

		logger.debug( nonRedundantClauses.size() + " non-redundant clauses will not be tested for subsumption" );
		Set<Clause> toBeTested = new HashSet<Clause>(clauses);
		toBeTested.removeAll(nonRedundantClauses);
		
		long possibleNonRedundantThatAreNonRedundant=0;
		for (Clause keyClause : possibleNonRedundantClauses.keySet())
			if (!clauses.contains(keyClause) ) {
				toBeTested.removeAll(possibleNonRedundantClauses.get(keyClause));
				nonRedundantClauses.addAll(possibleNonRedundantClauses.get(keyClause));
				possibleNonRedundantThatAreNonRedundant+=possibleNonRedundantClauses.get(keyClause).size();
			}
		logger.debug( possibleNonRedundantThatAreNonRedundant + " possible non-redundant clauses are indeed non-redundant; wll also be excluded" );
		ArrayList<Clause> result = new ArrayList<Clause>(clauses);
		Set<Clause> redundant = new HashSet<Clause>();
		if(!toBeTested.isEmpty()) {
			clauses.removeAll(nonSubsumerClausesExtended);
			TreeSet<Clause> clausesOrdered = new TreeSet<Clause>(clauses);
			
			logger.debug( nonSubsumerClausesExtended.size() + " clauses identified as either non-subsumers or non-prime subsumers and won't be used" );
			logger.debug( "Hence, " + toBeTested.size() + " possibly redundant clauses will be tested against " +  clausesOrdered.size() + " potential subsumers");
			
			for (Clause c1 : toBeTested) {
				for (Clause c2 : clausesOrdered) {
					if (redundant.contains(c2) || c1.equals(c2) || c2.getBody().length>c1.getBody().length)
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
		}
		for (Clause c1 : toBeTested) {
			if (redundant.contains(c1))
				continue;
			for (Clause c2 : toBeTested) {
				if (c1.equals(c2))
					continue;
				if (c1.isEquivalentUpToVariableRenaming(c2)) {
					result.remove(c2);
					redundant.add(c2);
				}
			}
		}
		return result;
	}

	private void markRedundantAndNonRedundantClauses(Set<Clause> rewritingAsSet) {
		long t=System.currentTimeMillis();
		ArrayList<Clause> listOfClauses = new ArrayList<Clause>(rewritingAsSet);
		listOfClauses = pruneAUX( listOfClauses );
		standardSubsumptionCheck( listOfClauses );
		logger.debug( "Marking subsumed and non-subsumed clauses took: " + (System.currentTimeMillis()-t) );
	}

	@Override
	public boolean isClauseRedundant(Clause clause,Set<Variable> joinVars) {
		if (clause.getSubsumer()!=null)
			if (activeSubsumers.contains(clause.getSubsumer()))
				return true;
			else if (extensionOfSubsumerWillSubsume(clause,clause.getSubsumer(),joinVars))
				return true;
		return false;
	}
	
	@Override
	public boolean isClauseNonRedundant(Clause clause,Set<Variable> joinVars) {
//		if (clause.getSubsumer()==null)
		if (activeSubsumers.contains(clause.getSubsumer()))
			return false;
		return true;
	}

	private boolean extensionOfSubsumerWillSubsume(Clause currentClause,Clause subsumer,Set<Variable> joinVars) {
		if (subsumer.getVariables().containsAll(joinVars)) {
			int atomsOfSubsumerInCurrent=0;
			for (Term term1 : subsumer.getBody() )
				for (Term term2 : currentClause.getBody())
					if (term1.toString().equals(term2.toString())) {
						atomsOfSubsumerInCurrent++;
						break;
				}
			if (atomsOfSubsumerInCurrent==subsumer.getBody().length)
				return true;
		}
		return false;
	}

	@Override
	public void addActiveSubsumer(Clause clause) {
		activeSubsumers.add(clause);
	}
}
