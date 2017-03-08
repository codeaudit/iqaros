package org.oxford.comlab.perfectref.rewriter;

import java.util.Arrays;
import java.util.HashMap;

public class FunctionalTerm extends Term{
    protected final String m_name;
    protected Term[] m_arguments;

    protected FunctionalTerm(String name,Term[] arguments) {
        m_name=name;
        m_arguments=arguments;
    }

    @Override
	public String getName() {
        return m_name;
    }

    @Override
	public int getArity() {
        return m_arguments.length;
    }

    @Override
	public Term getArgument(int argumentIndex) {
    	return m_arguments[argumentIndex];
    }

    @Override
	public Term[] getArguments(){
    	return m_arguments;
    }

    @Override
	public boolean contains(Term term) {
        if (equals(term))
            return true;
        for (int index=m_arguments.length-1;index>=0;--index)
            if (m_arguments[index].contains(term))
                return true;
       return false;
    }

    @Override
	public Term apply(Substitution substitution,TermFactory termFactory) {
        if (m_arguments.length==0 || substitution.isEmpty())
            return this;
        else {
            Term[] arguments=new Term[m_arguments.length];
            for (int index=m_arguments.length-1;index>=0;--index)
                arguments[index]=m_arguments[index].apply(substitution,termFactory);
            return termFactory.getFunctionalTerm(m_name,arguments);
        }
    }

    @Override
	public Term offsetVariables(TermFactory termFactory,int offset) {
        if (m_arguments.length==0)
            return this;
        else {
            Term[] arguments=new Term[m_arguments.length];
            for (int index=m_arguments.length-1;index>=0;--index)
                arguments[index]=m_arguments[index].offsetVariables(termFactory,offset);
            return termFactory.getFunctionalTerm(m_name,arguments);
        }
    }

    @Override
	public Term renameVariables(TermFactory termFactory, HashMap<Variable, Integer> mapping) {
        if (m_arguments.length==0)
            return this;
        else {
            Term[] arguments=new Term[m_arguments.length];
            for (int index=m_arguments.length-1;index>=0;--index)
                arguments[index]=m_arguments[index].renameVariables(termFactory, mapping);
            return termFactory.getFunctionalTerm(m_name,arguments);
        }
    }

    @Override
	public int getMinVariableIndex() {
        int minVariableIndex=Integer.MAX_VALUE;
        for (int index=m_arguments.length-1;index>=0;--index)
            minVariableIndex=Math.min(minVariableIndex,m_arguments[index].getMinVariableIndex());
        return minVariableIndex;
    }

    @Override
	public void toString(StringBuffer buffer) {
        buffer.append(getName());
        if (m_arguments.length>0) {
            buffer.append('(');
            for (int index=0;index<m_arguments.length;index++) {
                if (index!=0)
                    buffer.append(',');
                m_arguments[index].toString(buffer);
            }
            buffer.append(')');
        }
    }

    @Override
	public int getDepth(){
    	return getDepth(this);
    }

    private int getDepth(Term t){
    	if(t.getArity() == 0)
    		return 0;
    	else
    	{
    		int[] depths = new int[t.getArity()];
    		for(int i=0; i < t.getArity(); i++)
    			depths[i] = getDepth(t.getArgument(i));
    		Arrays.sort(depths);
    		return 1 + depths[t.getArity()-1];
    	}
    }

    @Override
	public Term getVariableOrConstant(){
    	if(this.getArity() == 0)
    		return this;
    	else
    		return this.m_arguments[0].getVariableOrConstant(); //All functional terms have at most one element
    }

    @Override
	public String getFunctionalPrefix()
    {
    	if(this.getArity() == 0)
			return this.m_name;
		else{
    		String arguments = "";
    		for(int i=0; i<this.m_arguments.length; i++)
				arguments += this.m_arguments[i].getFunctionalPrefix();
    		return this.m_name + arguments;
    	}
    }

    @Override
	public boolean equals(Object obj) {
    	if (obj instanceof FunctionalTerm) {
    		FunctionalTerm o = (FunctionalTerm)obj;

    		if ( this.getArity() != o.getArity() )
    			return false;
    		for(int i=0; i<this.m_arguments.length; i++)
				if (!this.m_arguments[i].equals(o.m_arguments[i]))
    				return false;
    		return m_name.equals(o.m_name);
    	}
    	return false;
    }

    @Override
	public int hashCode() {

    	int v = 0;

    	for(int i=0; i<this.m_arguments.length; i++)
    		v += this.m_arguments[i].hashCode();
    	v += m_name.hashCode();
    	return v;
    }
}
