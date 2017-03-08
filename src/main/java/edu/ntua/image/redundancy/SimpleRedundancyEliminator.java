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
import java.util.Set;

import org.oxford.comlab.perfectref.rewriter.Clause;
import org.oxford.comlab.perfectref.rewriter.Term;
import org.oxford.comlab.perfectref.rewriter.Variable;

import edu.ntua.image.refinement.RewritingExtensionManager;

public class SimpleRedundancyEliminator extends RedundancyElimination {

	@Override
	public void checkAndMarkClauseAsPossiblyNonRedundant(Clause currentClause, Term extraTerm, Clause newClause) { }

	@Override
	public void checkAndMarkClauseAsNonRedundant(Clause newClause) { }

	@Override
	public void initialise(RewritingExtensionManager rewExtensionMngr, Set<Clause> ucqOfReducedAsRew, Set<Term> rewOfNewAtom) { }

	@Override
	public void flush(Clause clause) { }

	@Override
	public ArrayList<Clause> removeRedundantClauses(ArrayList<Clause> clauses) {
		return standardSubsumptionCheck(clauses);
	}

	@Override
	public void addActiveSubsumer(Clause clause) { }

	@Override
	public boolean isClauseRedundant(Clause clausem, Set<Variable> joinVars) {
		return false;
	}
	
	@Override
	public boolean isClauseNonRedundant(Clause clausem, Set<Variable> joinVars) {
		return true;
	}
}
