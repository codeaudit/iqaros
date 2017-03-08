package org.oxford.comlab.perfectref.rewriter;

import java.util.HashMap;

public class Variable extends Term {
    public int m_index;


//    changed from protected
//    27/6/2011

    public Variable(int index) {
        m_index=index;
    }

    @Override
	public String getName() {
        return "X"+m_index;
    }

    @Override
	public int getArity() {
        return 0;
    }

    @Override
	public Term getArgument(int argumentIndex) {
        throw new IndexOutOfBoundsException();
    }

    @Override
	public Term[] getArguments() {
        throw new IndexOutOfBoundsException();
    }

    @Override
	public boolean contains(Term term) {
        return equals(term);
    }

    @Override
	public Term apply(Substitution substitution,TermFactory termFactory) {
        Term result=substitution.get(this);
        if (result!=null)
            return result;
        else
            return this;
    }

    @Override
	public Term offsetVariables(TermFactory termFactory,int offset) {
        return termFactory.getVariable(m_index+offset);
    }

    @Override
	public Term renameVariables(TermFactory termFactory, HashMap<Variable, Integer> mapping) {
        return termFactory.getVariable(mapping.get(this));
    }

    @Override
	public int getMinVariableIndex() {
        return m_index;
    }

    @Override
	public void toString(StringBuffer buffer) {
        buffer.append(getName());
    }

    @Override
	public int getDepth()
    {
    	return 0;
    }

    @Override
	public Term getVariableOrConstant()
    {
    	return this;
    }

    @Override
	public String getFunctionalPrefix()
    {
    	return "";
    }

    public void setIndex(int index)
    {
    	this.m_index = index;
    }

    @Override
	public boolean equals(Object that){
    	if(that instanceof Variable)
			return this.getName().equals(((Variable)that).getName());
    	return false;
    }

    @Override
	public int hashCode(){
    	return this.m_index;
    }
}
