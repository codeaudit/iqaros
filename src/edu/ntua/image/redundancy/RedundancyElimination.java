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
import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;

import org.oxford.comlab.perfectref.rewriter.Clause;
import org.oxford.comlab.perfectref.rewriter.Term;
import org.oxford.comlab.perfectref.rewriter.Variable;

import edu.ntua.image.refinement.RewritingExtensionManager;

public abstract class RedundancyElimination {
	
	protected Set<Clause> nonSubsumerClauses = new HashSet<Clause>();

	public abstract void initialise(RewritingExtensionManager rewExtensionMngr, Set<Clause> ucqOfReducedAsRew, Set<Term> rewOfNewAtom);
	public abstract void checkAndMarkClauseAsPossiblyNonRedundant(Clause currentClause, Term extraTerm, Clause newClause);
	public abstract void checkAndMarkClauseAsNonRedundant(Clause newClause);
	public abstract boolean isClauseRedundant(Clause clausem,Set<Variable> joinVars);
	public abstract boolean isClauseNonRedundant(Clause clausem,Set<Variable> joinVars);
	public abstract void addActiveSubsumer(Clause clause);
	public abstract void flush(Clause clause);
	public abstract ArrayList<Clause> removeRedundantClauses(ArrayList<Clause> clauses);

	protected ArrayList<Clause> standardSubsumptionCheck(ArrayList<Clause> clauses) {
		ArrayList<Clause> result = new ArrayList<Clause>(clauses);
		TreeSet<Clause> clausesOrdered = new TreeSet<Clause>(clauses);
		Set<Clause> redundant = new HashSet<Clause>();
		for (Clause c1 : clausesOrdered){
			if (redundant.contains(c1))
				continue;
			int index=0;
			for (Clause c2 : clausesOrdered) {
				index++;
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
			if (index==clausesOrdered.size())
				nonSubsumerClauses.add(c1);
		}
		return result;
	}
	
	/**
	 * Performs a query subsumption test
	 * @return
	 */
	public ArrayList<Clause> standardSubsumptionCheck_req(ArrayList<Clause> clauses) {
		ArrayList<Clause> result = new ArrayList<Clause>();
		
		boolean c1IsSubsumed;
		
		//Identify equivalent clauses
		for (Clause c1 : clauses) {
			for (Clause c2 : clauses) {
				if(!c1.equals(c2) && !c1.toBeIgnored && !c2.toBeIgnored) {
					if(c2.subsumes(c1) && c1.subsumes(c2)){
						if(c1.m_canonicalRepresentation.length() < c2.m_canonicalRepresentation.length()){
							c2.toBeIgnored = true;
						}else{
							c1.toBeIgnored = true;
						}
					}
				}
			}
		}
		
		//Prune subsumed clauses
		for (Clause c1 : clauses) {
			if(!c1.toBeIgnored){
				c1IsSubsumed = false;
				for (Clause c2 : clauses) {
					if(!c2.toBeIgnored){
					if(!c1.equals(c2)) {
						if(c2.subsumes(c1)){
							c1IsSubsumed = true;
							break;
						}
					}
					}
				}
				if(!c1IsSubsumed){
					result.add(c1);
				}
			}
		}
		
		return result;
	}

	public ArrayList<Clause> pruneAUX(ArrayList<Clause> clauses) {
		HashSet<String> IDBPredicates = new HashSet<String>();
		HashSet<String> EDBPredicates = new HashSet<String>();
		ArrayList<Clause> result = new ArrayList<Clause>();

		for (Clause c : clauses)
			IDBPredicates.add(c.getHead().getName());

		// Compute the EDB predicates
		for (Clause c : clauses)
			for (Term t : c.getBody())
				if (!IDBPredicates.contains(t.getName()))
					EDBPredicates.add(t.getName());

		// Prune clauses with AUX EDB predicates
		for (Clause c : clauses) {
			boolean isToBePruned = false;
			for (Term t : c.getBody()) {
				if (t.getName().contains("AUX$"))
					if (EDBPredicates.contains(t.getName())) {
						isToBePruned = true;
						break;
					}
				try {
					// Auxiliary symbols introduced in the normalization
					// (HermiT)
					Integer.parseInt(t.getName());
					if (EDBPredicates.contains(t.getName())) {
						isToBePruned = true;
						break;
					}
				} catch (NumberFormatException e) {
				}
			}

			if (!isToBePruned)
				result.add(c);
		}
		return result;
	}
}
