package edu.mit.csail.sdg.alloy4compiler.ast;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;

public class IntSubsetScope extends CommandScope {

    public final IntScope intScope; 
    
    public IntSubsetScope(Pos pos, Sig sig, IntScope intScope) throws ErrorSyntax, Err {
        super(pos, sig, false, bw(intScope), bw(intScope), 1, false);
        this.intScope = intScope;
    }

    private static int bw(IntScope intScope) {
        return intScope.bitwidth != null ? intScope.bitwidth : -1;
    }
    
    public CommandScope change(Sig newSig) throws Err           { return new IntSubsetScope(pos, newSig, intScope); }
    public CommandScope change(IntScope newIntScope) throws Err { return new IntSubsetScope(pos, sig, newIntScope); }

    public String toString() {
        return intScope.toString() + " " + sig.label;
    }
    
}
