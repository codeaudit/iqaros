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

package edu.ntua.image;

public class Configuration {
	public RedundancyEliminationStrategy redundancyElimination = RedundancyEliminationStrategy.Restricted_Subsumption;

	 /**
     * Determines whether the nonredundant optimisation is to be used. Care should be taken in that
     * this optimisation might not return a minimal UCQ wrt subsumption redundancy elimination
     */
    public static enum RedundancyEliminationStrategy {

    	/** Applies the standard subsumption elimination algorithm after finishing computing a UCQ. */
    	Full_Subsumption,

        /** Identifies a set of possible nonredundant clauses and it does not apply subsumption over these clauses, but only
         * over those that are not guessed not to be redundant. */
    	Restricted_Subsumption
    }
}
