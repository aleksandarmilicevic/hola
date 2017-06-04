/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4compiler.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;

/** Immutable; reresents a scope in a "run" or "check" command.
 *
 * <p> <b>Invariant:</b>  sig != null
 * <p> <b>Invariant:</b>  endingScope >= startingScope >= 0
 * <p> <b>Invariant:</b>  increment > 0
 */

public class CommandScope {

    /** The position in the original source file where this scope was declared; can be Pos.UNKNOWN if unknown. */
    public final Pos pos;

    /** The sig whose scope is being given by this CommandScope object. */
    public final Sig sig;

    /** True iff the scope is an exact scope. */
    private final boolean isExact;
    
    /** True iff the scope was specified (syntactically) as a range (as opposed to a single integer). */
    private final boolean isRange;

    /** The starting scope. */
    private final int startingScope;

    /** The ending scope; if this sig is not a growing sig, then this.startingScope==this.endingScope. */
    private final int endingScope;

    /** The scope increment; if this sig is not a growing sig, then this.increment is ignored. */
    private final int increment;

    /** Construct a new CommandScope object.
     * @param sig - the sig for this scope
     * @param isExact - true iff the scope is intended to be exact
     * @param scope - the scope
     * @throws ErrorSyntax if scope is less than zero
     */
    public CommandScope(Sig sig, boolean isExact, int scope) throws ErrorSyntax { this(null, sig, isExact, scope, scope, 1, false); }

    /** Construct a new CommandScope object.
     * @param pos - the position where this scope is given
     * @param sig - the sig for this scope
     * @param isExact - true iff the scope is intended to be exact
     * @param startingScope - the starting scope
     * @param endingScope - the ending scope (if this sig is not intended to be growable, then startingScope should equal endingScope)
     * @param increment - the scope increment (if this sig is not intended to be growable, then this field is ignored)
     * @throws ErrorSyntax if startingScope is less than zero
     * @throws ErrorSyntax if endingScope is less than startingScope
     * @throws ErrorSyntax if increment is less than one
     */
    public CommandScope(Pos pos, Sig sig, boolean isExact, int startingScope, int endingScope, int increment) throws ErrorSyntax { 
        this(pos, sig, isExact, startingScope, endingScope, increment, false); 
    }
    public CommandScope(Pos pos, Sig sig, boolean isExact, int startingScope, int endingScope, int increment, boolean isRange) throws ErrorSyntax {
        if (pos == null) pos = Pos.UNKNOWN;
        if (sig == null) throw new NullPointerException();
//        if (startingScope < 0) throw new ErrorSyntax(pos, "Sig "+sig+" cannot have a negative starting scope ("+startingScope+")");
//        if (endingScope < 0) throw new ErrorSyntax(pos, "Sig "+sig+" cannot have a negative ending scope ("+endingScope+")");
        if (endingScope < startingScope) throw new ErrorSyntax(pos, "Sig "+sig+" cannot have an ending scope ("+endingScope+") smaller than its starting scope ("+startingScope+")");
        if (startingScope == endingScope) increment = 1;
        if (increment < 1) throw new ErrorSyntax(pos, "Sig "+sig+"'s increment value cannot be "+increment+".\nThe increment must be 1 or greater.");
        this.pos = pos;
        this.sig = sig;
        this.isExact = isExact;
        this.isRange = isRange;
        this.startingScope = startingScope;
        this.endingScope = endingScope;
        this.increment = increment;
    }
    
    public CommandScope change(Sig s) throws Err {
        return new CommandScope(pos, s, isExact, startingScope, endingScope, increment, isRange);
    }

    /** {@inheritDoc} */
    @Override public String toString() {
        String ans = (isExact() ? "exactly " : "")
          + startingScope()
          + (endingScope()!=startingScope() ? (".."+endingScope()) : "")
          + (increment() > 1 ? (":"+increment()) : "");
        String tail = Util.tail(sig.label);
        if (!"none".equals(tail))
            ans += " " + tail;
        return ans;
    }

    public List<Integer> enumerate() {
        ArrayList<Integer> ans = new ArrayList<Integer>();
        for (int i = startingScope(); i <= endingScope(); i += increment()) ans.add(i);
        return ans;
    }

    public List<String> enumerateAsString() {
        List<Integer> tmp = enumerate();
        List<String> ans = new ArrayList<String>(tmp.size());
        for (Integer i : tmp) ans.add(i.toString());
        return ans;
    }

    public int startingScope() { return startingScope; }
    public int endingScope()   { return endingScope; }
    public int increment()     { return increment; }
    public boolean isExact()   { return isExact; }
    public boolean isRange()   { return isRange; }
}
