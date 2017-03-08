package org.oxford.comlab.perfectref.rewriter;

/**
 * Represents a DL-liteR axiom:
 *
 *  1: A     -> B
 *  2: A     -> \E P
 *  3: A     -> \E P-
 *  4: \E P  -> A
 *  5: \E P  -> \E S
 *  6: \E P  -> \E S-
 *  7: \E P- -> A
 *  8: \E P- -> \E S
 *  9: \E P- -> \E S-
 * 10: P     -> S    , P- -> S-
 * 11: P     -> S-   , P- -> S
 *
 * @author hecp
 *
 */
public class PI {
	public final int m_type;
    public final String m_left;
    public final String m_right;

    public PI(int type, String left, String right){
    	this.m_type = type;
    	this.m_left = left;
    	this.m_right = right;
    }
}
