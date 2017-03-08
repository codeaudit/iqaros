package org.oxford.comlab.perfectref.rewriter;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

public class Clause implements Comparable<Clause> {

	private Clause isSubsumedBy = null;

	public Set<Substitution> unifications = new HashSet<Substitution>();



	public Set<Substitution> getUnifications() {
		return unifications;
	}

	public void addUnification( Substitution unification ) {
//		this.unifications.add( unification );
		for ( Entry<Variable,Term> s : unification.entrySet() )
			if ( !s.getKey().toString().equals(s.getValue().toString()) )
			{
				Substitution s1 = new Substitution();
				s1.put(s.getKey(), s.getValue());
				this.unifications.add( s1 );
//				Substitution s2 = new Substitution();
//				s2.put((Variable) s.getValue(), s.getKey());
//				this.unifications.add( s2 );

			}
	}

//	//added 30-6-2011
//	/*
//	 * This is used in cases where R(0,1),S(0,1) is the query with S being the extraAtom
//	 * If R(0,1) gives A(0), then A(0), S(0,1) is not a valid query
//	 */
//	private Set<Variable> lostVars = new HashSet<Variable>();
//
//	public void addLostVars( Variable lostVar ) {
//		this.lostVars.add( lostVar );
//	}
//
//	public void addLostVars( Set<Variable> lostVarsSet ) {
//		for ( Variable v: lostVarsSet)
//			this.lostVars.add( v );
//	}
//
//	public Set<Variable> getLostVars() {
//		return this.lostVars;
//	}

	public static final Map<Variable,Term> EMPTY_SUBSTITUTION=Collections.emptyMap();
    private final Term[] m_body;
    private final Term m_head;
    public final String m_canonicalRepresentation;
    public boolean toBeIgnored = false;

    public boolean[] m_selectedBody;
    public boolean m_selectedHead;
    public char m_type;

	public boolean subsumes;


    public Clause getSubsumer(){
    	return isSubsumedBy;
    }

    public void setSubsumer(Clause subsumer){
    	isSubsumedBy=subsumer;
    }

    public Clause(Term[] body, Term head) {
        this.m_body = body;
        this.m_head = head;
        this.m_selectedBody = new boolean[m_body.length];
        this.m_selectedHead = false;
        this.m_canonicalRepresentation = this.computeCanonicalRepresentation();
        this.m_type = '\0';
        isSubsumedBy=null;
    }

    public Term[] getBody() {
        return m_body;
    }

    public Term getHead() {
        return m_head;
    }

    /**
     * Returns an ArrayList<Variable> containing all the variables occurring in the clause
     * (no repetitions) in the order of occurrence from left to right (head first)
     *
     * @return
     */
    public ArrayList<Variable> getVariables(){
    	ArrayList<Variable> result = new ArrayList<Variable>();

    	//Get the variables of the head
    	for(int i=0; i < this.m_head.getArguments().length; i++){
    		Term t = this.m_head.getArguments()[i].getVariableOrConstant();
    		if((t instanceof Variable) &&
    		   !(result.contains(t)))
				result.add((Variable)t);
    	}

    	//Get the variables of the body
    	for(int j=0; j < this.m_body.length; j++)
			for(int i=0; i < this.m_body[j].getArguments().length; i++){
        		Term t = this.m_body[j].getArguments()[i].getVariableOrConstant();
        		if((t instanceof Variable) &&
   	    		   !(result.contains(t)))
					result.add((Variable)t);
        	}

    	return result;
    }

    public ArrayList<Variable> getDistinguishedVariables(){
    	ArrayList<Variable> result = new ArrayList<Variable>();

    	//Get the variables of the head
    	for(int i=0; i < this.m_head.getArguments().length; i++){
    		Term t = this.m_head.getArguments()[i].getVariableOrConstant();
    		if((t instanceof Variable) &&
    		   !(result.contains(t)))
				result.add((Variable)t);
    	}

    	Collections.sort(result, new Comparator<Variable>(){
			public int compare(Variable v1, Variable v2){
				if(v1.m_index < v2.m_index)
					return -1;
				else if(v1.m_index == v2.m_index)
					return 0;
				else
					return 1;
			}
		});


    	return result;
    }

    /**
     * Determines if the variable var is bound (occurs more than once) in this clause
     * @param varIndex
     * @return
     */
    public boolean isBound(Variable var){
        ArrayList<Variable> variables = new ArrayList<Variable>();

    	//Get the variables of the head with repetitions
    	for(int i=0; i < this.m_head.getArguments().length; i++){
    		Term t = this.m_head.getArguments()[i].getVariableOrConstant();
    		if(t instanceof Variable)
				variables.add((Variable)t);
    	}

    	//Get the variables of the body with repetitions
    	for(int j=0; j < this.m_body.length; j++)
			for(int i=0; i < this.m_body[j].getArguments().length; i++){
        		Term t = this.m_body[j].getArguments()[i].getVariableOrConstant();
        		if(t instanceof Variable)
					variables.add((Variable)t);
        	}

    	//Count the occurrences
    	int i=0;
    	for(Variable v: variables)
			if(v.equals(var))
				i++;
    	return i > 1;
    }

    /**
     * Renames the variables of the clause via offset
     * @param termFactory
     * @param offset
     * @return
     */
    public Clause renameVariables(TermFactory termFactory, int offset) {

    	Term headRenamed = m_head.offsetVariables(termFactory,offset);

    	Term[] bodyRenamed = new Term[m_body.length];
        for(int index = 0; index < m_body.length; index++)
            bodyRenamed[index] = m_body[index].offsetVariables(termFactory,offset);

        Clause clauseRenamed = new Clause(bodyRenamed,headRenamed);
        clauseRenamed.setSelectedBody(this.m_selectedBody);
        clauseRenamed.setSelectedHead(this.m_selectedHead);

        return clauseRenamed;
    }

    /**
     * avenet 24/01/2011
     * Renames the variables of the clause via mapping
     * @param termFactory
     * @param mapping
     * @return
     */
    public Clause renameVariables(TermFactory termFactory, HashMap<Variable,Integer> mapping) {
    	Term headRenamed = m_head.renameVariables(termFactory, mapping);

    	Term[] bodyRenamed = new Term[m_body.length];
        for(int index = 0; index < m_body.length; index++)
			bodyRenamed[index] = m_body[index].renameVariables(termFactory, mapping);

        Clause clauseRenamed = new Clause(bodyRenamed,headRenamed);
        clauseRenamed.setSelectedBody(this.m_selectedBody);
        clauseRenamed.setSelectedHead(this.m_selectedHead);

        return clauseRenamed;
    }



    /**
     * avenet 24/01/2011
     * Renames the variables of the clause via mapping
     * @param termFactory
     * @param mapping
     * @return
     */
    public Clause renameVariablesOriginal(TermFactory termFactory, HashMap<Variable,Integer> mapping) {
    	Term headRenamed = m_head.renameVariables(termFactory, mapping);

    	Term[] bodyRenamed = new Term[m_body.length];
        for(int index = 0; index < m_body.length; index++)
			bodyRenamed[index] = m_body[index].renameVariables(termFactory, mapping);

        Clause clauseRenamed = new Clause(bodyRenamed,headRenamed);
        clauseRenamed.setSelectedBody(this.m_selectedBody);
        clauseRenamed.setSelectedHead(this.m_selectedHead);

        return clauseRenamed;
    }


    public void setSelectedBody(boolean[] selectedBody){
    	this.m_selectedBody = selectedBody;
    }

    public void setSelectedHead(boolean selectedHead){
    	this.m_selectedHead = selectedHead;
    }

    public boolean containsFunctionalTerms(){
    	if(this.m_head.getDepth()-1 > 0)
			return true;
    	for(int i=0; i<m_body.length; i++)
			if(this.m_body[i].getDepth()-1 > 0)
				return true;
    	return false;
    }

	public boolean isQueryClause(){
		if(m_head.getName().equals("Q"))
			return true;
		return false;
	}

	public boolean containsEqualityHead(){
		if(m_head.getName().equals("="))
			return true;
		return false;
	}

	public boolean containsOAtoms(){
		if(m_head.getName().equals("$"))
			return true;
    	for(int i=0; i<m_body.length; i++)
			if(m_body[i].getName().equals("$"))
				return true;
		return false;
	}

	public boolean containsEqualityBodyAtoms(){
    	for(int i=0; i<m_body.length; i++)
			if(m_body[i].getName().equals("="))
				return true;
		return false;
	}

	public boolean containsBinaryBodyAtoms(){
    	for(int i=0; i<m_body.length; i++)
			if(m_body[i].getArity() == 2)
				return true;
		return false;
	}

	public boolean containsAUXPredicates(){
		for(int i=0; i < m_body.length; i++){
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

	public boolean hasGroundHead(){
		for(int j=0; j<m_head.getArity(); j++)
			if((m_head.getArgument(j).getVariableOrConstant() instanceof Variable) ||
			   (m_head.getArgument(j).getVariableOrConstant() instanceof FunctionalTerm &&
					   (m_head.getArgument(j).getDepth() > 0)))
				return false;
		return true;
	}

	public boolean hasGroundBody()
	{
		for(int i=0; i<m_body.length; i++)
			for(int j=0; j<m_body[i].getArity(); j++)
				if(m_body[i].getArgument(j).getVariableOrConstant() instanceof Variable ||
				  (m_body[i].getArgument(j).getVariableOrConstant() instanceof FunctionalTerm &&
						  (m_body[i].getArgument(j).getDepth() > 0)))
					return false;
		return true;
	}

	public boolean isGround(){
		return this.hasGroundHead() && this.hasGroundBody();
	}

	public boolean isTautology() {
        for (int i=0;i<m_body.length;i++)
			if(m_body[i].toString().equals(this.m_head.toString()))
				return true;
        return false;
    }

	@Override
	public String toString() {

		StringBuffer buffer = new StringBuffer();
        toString(buffer);
        return buffer.toString();
    }

    private void toString(StringBuffer buffer) {

    	m_head.toString(buffer);

    	if(m_body.length > 0){
        	buffer.append("  <-  ");
            for (int index=0;index<m_body.length;index++) {
                if (index!=0)
                    buffer.append(" ^ ");
                m_body[index].toString(buffer);
            }
        }
    }

    private String computeCanonicalRepresentation(){
    	Arrays.sort(this.m_body, new Comparator<Term>(){
    		public int compare(Term t1, Term t2){
    			return ((FunctionalTerm)t1).getFunctionalPrefix().compareTo(((FunctionalTerm)t2).getFunctionalPrefix());
    		}
        });
    	return this.toString();
    }

    /**
	 * Performs basic preliminary tests in order to check whether this can subsume a given clause
	 * @param that
	 * @return
	 */
    private boolean canSubsume(Clause that){
    	if(this.getHead().getName().equals(that.getHead().getName()) &&
                this.getHead().getArity() == that.getHead().getArity() &&
                this.hasSubsetOfBodyAtoms(that))
			return true;
         	return false;
    }

    /**
	 * Performs basic preliminary tests in order to check whether this can be equivalent to that up to variable renaming
	 * @param that
	 * @return
	 */
    private boolean canbeEquivalent(Clause that){
    	if(this.getHead().getName().equals(that.getHead().getName()) &&
         	   this.getHead().getArity() == that.getHead().getArity() &&
         	   this.getBody().length == that.getBody().length &&
         	   this.hasSameBodyAtoms(that))
			return true;
         	return false;
    }

    /**
     * Decides if the body atoms of this are the same as the body atoms of that
     * @param that
     * @return
     */
    private boolean hasSameBodyAtoms(Clause that){

    	for(int i=0; i<this.m_body.length; i++)
			if(!(this.m_body[i].getArity() == that.m_body[i].getArity() &&
    		   this.m_body[i].getName().equals(that.m_body[i].getName())))
				return false;
    	return true;
    }

    /**
     * Decides if the set of body atoms of this is a subset of the set of body atoms of that
     * @param that
     * @return
     */
    private boolean hasSubsetOfBodyAtoms(Clause that){
    	HashSet<String> superset = new HashSet<String>();

    	for(int i=0; i<that.m_body.length; i++)
			superset.add(that.m_body[i].getName());

    	for(int i=0; i<this.m_body.length; i++)
			if(!superset.contains(this.m_body[i].getName()))
				return false;

    	return true;
    }

    /**
	 * Decides if this is equivalent to that up to variable renaming
	 * @param that
	 * @return
	 */
    public boolean isEquivalentUpToVariableRenaming(Clause rule) {
    	if(!canbeEquivalent(rule))
			return false;

        Clause ruleCore=rule;
        Term[][] subsumingAtoms=new Term[][] { new Term[]{m_head},m_body };
        Map<String,AtomIndexNode> subsumedHeadAtomsIndex=ruleCore.getHeadAtomIndex();
        Map<String,AtomIndexNode> subsumedBodyAtomsIndex=ruleCore.getBodyAtomIndex();
        if (subsumedHeadAtomsIndex==null || subsumedBodyAtomsIndex==null)
			return false;
		else
			return match(subsumingAtoms,subsumedHeadAtomsIndex,subsumedBodyAtomsIndex,EMPTY_SUBSTITUTION,0,0);
    }

    /**
	 * Decides if this subsumes a given clause
	 * @param that
	 * @return
	 */
    public boolean subsumes(Clause rule) {
    	if(!canSubsume(rule))
			return false;
        Clause ruleCore=rule;
        Term[][] subsumingAtoms=new Term[][] { new Term[]{m_head},m_body };
        Map<String,AtomIndexNode> subsumedHeadAtomsIndex=ruleCore.getHeadAtomIndex();
        Map<String,AtomIndexNode> subsumedBodyAtomsIndex=ruleCore.getBodyAtomIndex();
        if (subsumedHeadAtomsIndex==null || subsumedBodyAtomsIndex==null)
			return false;
		else
			return match(subsumingAtoms,subsumedHeadAtomsIndex,subsumedBodyAtomsIndex,EMPTY_SUBSTITUTION,0,0);
    }

    private boolean match(Term[][] subsumingAtoms, Map<String,AtomIndexNode> subsumedHeadAtomsIndex, Map<String,AtomIndexNode> subsumedBodyAtomsIndex,Map<Variable,Term> substitution,int headBodyIndex,int matchAtomIndex) {
        Term[] activeSubsumingAtoms=subsumingAtoms[headBodyIndex];
        if (matchAtomIndex==activeSubsumingAtoms.length) {
            if (headBodyIndex==0)
				return match(subsumingAtoms,subsumedHeadAtomsIndex,subsumedBodyAtomsIndex,substitution,1,0);
			else
				return true;
        }
        else {
            Term subsumingFormula=activeSubsumingAtoms[matchAtomIndex];
            if (!(subsumingFormula instanceof Term))
                return false;
            Term subsumingAtom=subsumingFormula;
            Map<String,AtomIndexNode> subsumedAtomsIndex;
            if (headBodyIndex==0)
                subsumedAtomsIndex=subsumedHeadAtomsIndex;
            else
                subsumedAtomsIndex=subsumedBodyAtomsIndex;
            String subsumingAtomPredicate=subsumingAtom.getName();
            AtomIndexNode candidates=subsumedAtomsIndex.get(subsumingAtomPredicate);
            while (candidates!=null) {
                Map<Variable,Term> matchedSubstitution=matchAtoms(subsumingAtom,candidates.m_literal,substitution);
                if (matchedSubstitution!=null) {
                    boolean result=match(subsumingAtoms,subsumedHeadAtomsIndex,subsumedBodyAtomsIndex,matchedSubstitution,headBodyIndex,matchAtomIndex+1);
                    if (result)
						return result;
                }
                candidates=candidates.m_next;
            }
            return false;
        }
    }

    private Map<String,AtomIndexNode> getHeadAtomIndex() {
        return buildAtomIndex(new Term[]{m_head});
    }

    private Map<String,AtomIndexNode> getBodyAtomIndex() {
        return buildAtomIndex(m_body);
    }

    private Map<String,AtomIndexNode> buildAtomIndex(Term[] atoms) {
        Map<String,AtomIndexNode> atomIndex=new HashMap<String,AtomIndexNode>();
        for (Term atom : atoms)
			atomIndex.put(atom.getName(),new AtomIndexNode(atom,atomIndex.get(atom.getName())));
        return atomIndex;
    }

    private Map<Variable,Term> matchAtoms(Term subsumingAtom,Term subsumedAtom,Map<Variable,Term> substitution) {
        boolean substitutionCopied=false;
        for (int argumentIndex=0;argumentIndex<subsumingAtom.getArity();argumentIndex++) {
            Term subsumingArgument=subsumingAtom.getArgument(argumentIndex);
            Term subsumedArgument=subsumedAtom.getArgument(argumentIndex);
            if (subsumingArgument instanceof Variable) {
                Term existingBinding=substitution.get(subsumingArgument);
                if (existingBinding==null) {
                    if (!substitutionCopied) {
                        substitution=new HashMap<Variable,Term>(substitution);
                        substitutionCopied=true;
                    }
                    substitution.put((Variable)subsumingArgument,subsumedArgument);
                }
            }
            Term subsumingArgumentSubstitutionApplied=applySubstitution(subsumingAtom.getArgument(argumentIndex),substitution);
            if (!subsumingArgumentSubstitutionApplied.equals(subsumedArgument))
                return null;
        }
        return substitution;
    }

    private Term applySubstitution(Term term,Map<Variable,Term> substitution) {
        if (term instanceof Variable) {
            Term replacement=substitution.get(term);
            if (replacement!=null)
                return replacement;
        }
        return term;
    }

    private static class AtomIndexNode {
        private final Term m_literal;
        private final AtomIndexNode m_next;

        public AtomIndexNode(Term literal,AtomIndexNode next) {
            m_literal=literal;
            m_next=next;
        }
    }

	//@Override
	public int compareTo(Clause otherClause) {
		return otherClause.getBody().length>getBody().length ? -1 : 1;
	}
}