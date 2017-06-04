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

package edu.mit.csail.sdg.alloy4compiler.translator;

import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.NONE;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.SEQIDX;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.SIGINT;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.STRING;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.UNIV;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.IA4Reporter;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.UniqueNameGenerator;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.CommandScope;
import edu.mit.csail.sdg.alloy4compiler.ast.IntScope;
import edu.mit.csail.sdg.alloy4compiler.ast.IntScope.AtomRange;
import edu.mit.csail.sdg.alloy4compiler.ast.IntScope.AtomSet;
import edu.mit.csail.sdg.alloy4compiler.ast.IntScope.AtomsKind;
import edu.mit.csail.sdg.alloy4compiler.ast.IntSubsetScope;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.SubsetSig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.PartialInstance.Atom;

/** Immutable; this class computes the scopes for each sig and computes the bitwidth and maximum sequence length.
 *
 * <p> The scopes are determined as follows:
 *
 * <p>  "run x": every topsig is scoped to <= 3 elements.
 *
 * <p>  "run x for N": every topsig is scoped to <= N elements.
 *
 * <p>  "run x for N but N1 SIG1, N2 SIG2...":
 * <br> Every sig following "but" is constrained explicitly.
 * <br> Any topsig that is
 * <br> a) not listed, and
 * <br> b) its scope is not derived otherwise
 * <br> will be scoped to have <= N elements.
 *
 * <p>  "run x for N1 SIG1, N2 SIG2..."
 * <br> Every sig following "but" is constrained explicitly.
 * <br> Any topsig that is
 * <br> a) not listed, and
 * <br> b) its scope is not derived otherwise
 * <br> we will give an error message.
 *
 * <p> Please see ScopeComputer.java for the exact rules for deriving the missing scopes.
 */
final class ScopeComputer {

    public static final int DEFAULT_BITWIDTH = 4;

    // It calls A4Solution's constructor

    /** Stores the reporter that will receive diagnostic messages. */
    private final IA4Reporter rep;

    /** Stores the command that we're computing the scope for. */
    final Command cmd;

//    /** The integer bitwidth of this solution's model; always between 1 and 30. */
//    private int bitwidth = 4;
//    private final int minInt;
//    private final int maxInt;
//    private final int intInc;

    private final IntScope intScope;

    /** The maximum sequence length; always between 0 and (2^(bitwidth-1))-1. */
    private int maxseq = 4;

    /** The number of STRING atoms to allocate; -1 if it was not specified. */
    private int maxstring = (-1);

    /** The scope for each sig. */
    private final IdentityHashMap<PrimSig,Integer> sig2scope = new IdentityHashMap<PrimSig,Integer>();
    /** The scope for each int subset sig. */    
    private final IdentityHashMap<Sig.SubsetSig, IntSubsetScope> intsubset2scope = new IdentityHashMap<Sig.SubsetSig, IntSubsetScope>();

    /** The sig's scope is exact iff it is in exact.keySet() (the value is irrelevant). */
    private final IdentityHashMap<Sig,Sig> exact = new IdentityHashMap<Sig,Sig>();

    /** The list of atoms. */
    private final List<String> atoms = new ArrayList<String>();

    /** This UniqueNameGenerator allows each sig's atoms to be distinct strings. */
    private final UniqueNameGenerator un = new UniqueNameGenerator();

    /** Optional partial instance */
    public final PartialInstance pi;

    private final List<Pair<String, PrimSig>> newAtoms;

    /** Returns the scope for a sig (or -1 if we don't know). */
    public int sig2scope(Sig sig) {
        if (sig==SIGINT) return intScope.bitwidth != null ? intScope.bitwidth : -1;
        if (sig==SEQIDX) return maxseq;
        if (sig==STRING) return maxstring;
        Integer y = sig2scope.get(sig);
        return (y==null) ? (-1) : y;
    }
    
    public IntSubsetScope intsub2scope(SubsetSig sig) {
        return intsubset2scope.get(sig);
    }

    public List<Pair<String, PrimSig>> getNewAtoms() {
        return new ArrayList<Pair<String,PrimSig>>(newAtoms);
    }

    /** Sets the scope for a sig; returns true iff the sig's scope is changed by this call. */
    private void sig2scope(Sig sig, int newValue) throws Err {
        if (sig.builtin)                throw new ErrorSyntax(cmd.pos, "Cannot specify a scope for the builtin signature \""+sig+"\"");
        if (!(sig instanceof PrimSig))  throw new ErrorSyntax(cmd.pos, "Cannot specify a scope for a subset signature \""+sig+"\"");
        if (newValue<0)                 throw new ErrorSyntax(cmd.pos, "Cannot specify a negative scope for sig \""+sig+"\"");
        int old=sig2scope(sig);
        if (old==newValue) return;
        if (old>=0)        throw new ErrorSyntax(cmd.pos, "Sig \""+sig+"\" already has a scope of "+old+", so we cannot set it to be "+newValue);
        sig2scope.put((PrimSig)sig, newValue);
        rep.scope("Sig "+sig+" scope <= "+newValue+"\n");
    }

    /** Returns whether the scope of a sig is exact or not. */
    public boolean isExact(Sig sig) {
        return sig==SIGINT || sig==SEQIDX || sig==STRING || ((sig instanceof PrimSig) && exact.containsKey(sig));
    }

    /** Make the given sig "exact". */
    private void makeExact(Pos pos, Sig sig) throws Err {
        if (!(sig instanceof PrimSig)) throw new ErrorSyntax(pos, "Cannot specify a scope for a subset signature \""+sig+"\"");
        exact.put(sig, sig);
    }

    //===========================================================================================================================//

    /** If A is abstract, unscoped, and all children are scoped, then set A's scope to be the sum;
     * if A is abstract, scoped, and every child except one is scoped, then set that child's scope to be the difference.
     */
    private boolean derive_abstract_scope (Iterable<Sig> sigs) throws Err {
       boolean changed=false;
       again:
       for(Sig s:sigs) if (!s.builtin && (s instanceof PrimSig) && s.isAbstract!=null) {
          SafeList<PrimSig> subs = ((PrimSig)s).children();
          if (subs.size()==0) continue;
          Sig missing=null;
          int sum=0;
          for(Sig c:subs) {
             int cn = sig2scope(c);
             if (cn<0) { if (missing==null) { missing=c; continue; } else { continue again; } }
             sum=sum+cn;
             if (sum<0) throw new ErrorSyntax(cmd.pos, "The number of atoms exceeds the internal limit of "+Integer.MAX_VALUE);
          }
          int sn = sig2scope(s);
          if (sn<0) {
             if (missing!=null) continue;
             sig2scope(s, sum);
             changed=true;
          } else if (missing!=null) {
             sig2scope(missing, (sn<sum) ? 0 : sn-sum);
             changed=true;
          }
       }
       return changed;
    }

    //===========================================================================================================================//

    /** If A is toplevel, and we haven't been able to derive its scope yet, then let it get the "overall" scope. */
    private boolean derive_overall_scope (Iterable<Sig> sigs) throws Err {
        boolean changed=false;
        final int overall = (cmd.overall<0 && cmd.scope.size()==0) ? 3 : cmd.overall;
        for(Sig s:sigs) if (!s.builtin && s.isTopLevel() && sig2scope(s)<0) {
            if (s.isEnum!=null) { sig2scope(s, 0); continue; } // enum without children should get the empty set
            if (overall<0) throw new ErrorSyntax(cmd.pos, "You must specify a scope for sig \""+s+"\"");
            sig2scope(s, overall);
            changed=true;
        }
        return changed;
    }

    //===========================================================================================================================//

    /** If A has an upper bound in the partial instance, use that as a scope */
    private boolean derive_partial_instance_scope (Iterable<Sig> sigs) throws Err {
        boolean changed=false;
        for(Sig s:sigs) if (!s.builtin) {
            String sigName = s.shortLabel();
            int currentScope = sig2scope(s);
            List<Atom> sigUpper = pi.sigUpper(sigName);
            int piNumAtoms = pi.atomsForType(sigName).size();
            if (sigUpper != null) {
                int piMaxAtoms = Math.max(piNumAtoms, sigUpper.size());
                if (currentScope != piMaxAtoms) {
                    sig2scope(s, piMaxAtoms);
                    changed = true;
                }
            } else if (piNumAtoms > 0 && piNumAtoms > currentScope) {
                sig2scope(s, piNumAtoms);
                changed = true;
            }
        }
        return changed;
    }

    //===========================================================================================================================//

    /** If A is not toplevel, and we haven't been able to derive its scope yet, then give it its parent's scope. */
    private boolean derive_scope_from_parent (Iterable<Sig> sigs) throws Err {
        boolean changed=false;
        Sig trouble=null;
        for(Sig s:sigs) if (!s.builtin && !s.isTopLevel() && sig2scope(s)<0 && (s instanceof PrimSig)) {
           PrimSig p = ((PrimSig)s).parent;
           int pb = sig2scope(p);
           if (pb>=0) {sig2scope(s,pb); changed=true;} else {trouble=s;}
        }
        if (changed) return true;
        if (trouble==null) return false;
        throw new ErrorSyntax(cmd.pos,"You must specify a scope for sig \""+trouble+"\"");
    }

    //===========================================================================================================================//

    /** Computes the number of atoms needed for each sig (and add these atoms to this.atoms) */
    private int computeLowerBound(final PrimSig sig) throws Err {
        if (sig.builtin) return 0;
        int n=sig2scope(sig), lower=0;
        boolean isExact = isExact(sig);
        // First, figure out what atoms *MUST* be in this sig
        for(PrimSig c:sig.children()) lower = lower + computeLowerBound(c);
        // Bump up the scope if the sum of children exceed the scope for this sig
        if (n<lower) {
           if (isExact)
               rep.scope("Sig "+sig+" scope raised from =="+n+" to be =="+lower+"\n");
           else
              rep.scope("Sig "+sig+" scope raised from <="+n+" to be <="+lower+"\n");
           n=lower;
           sig2scope.put(sig, n);
        }

        String sigName = sig.shortLabel();

//        //[PI]
        List<Atom> piAtoms = pi.atomsForType(sigName);

        // Add special overrides for "exactly" sigs
        if (!isExact && cmd.additionalExactScopes.contains(sig)) {
            isExact=true; rep.scope("Sig "+sig+" forced to have exactly "+n+" atoms.\n"); makeExact(Pos.UNKNOWN, sig);
        }
        // Create atoms
        //TODO: what if it's not topLevel but also not abstract???
        if (n>lower && (isExact || sig.isTopLevel())) {
            // Figure out how many new atoms to make
            n = n-lower;
            // Pick a name for them TODO [PI]: check
            String piAtomName = isPiSig(sig);
            if (piAtomName != null) {
                assert n == 1;
                atoms.add(piAtomName);
                lower++;
            } else {
                String name = un.make(sigName);
                // Now, generate each atom using the format "SIGNAME$INDEX"
                for (int i = 0; i < n; i++) {
                    String x;
                    if (i < sig.atomSigs().size()) {
                        x = sig.atomSigs().get(i).shortLabel();
                    } else {
                        x = name + '$' + i; //(i < piAtoms.size()) ? piAtoms.get(i).toString() :
                        if (atoms.contains(x)) x = name + '$' + (i + piAtoms.size());
                        newAtoms.add(new Pair<String, PrimSig>(x, sig));
                    }
                    atoms.add(x);
                    lower++;
                }
            }
        }
        return lower;
    }

    private String isPiSig(PrimSig sig) {
        if (sig.isAtom != null) { return sig.shortLabel(); }
        if (sig.isOne == null) return null;
        String[] arr = sig.shortLabel().split("__");
        if (arr.length < 3) return null;
        if (!"PI".equalsIgnoreCase(arr[0])) return null;
        return sig.parent.shortLabel() + '$' + arr[arr.length-1];
    }

    //===========================================================================================================================//

    /** Compute the scopes, based on the settings in the "cmd", then log messages to the reporter.
     * @param pi */
    private ScopeComputer(IA4Reporter rep, Iterable<Sig> sigs, Command command, PartialInstance pi) throws Err {
        this.rep = rep;
        this.pi = pi == null ? new PartialInstance() : pi;
        this.cmd = resolveIntScopes(pi, sigs, command);
        this.intScope = cmd.intScope;
        this.newAtoms = new ArrayList<Pair<String,PrimSig>>();

        // Process each sig listed in the command
        for(CommandScope sigScope:cmd.scope) {
            Sig s = sigScope.sig;
            IntSubsetScope intSubScope = null;
            SubsetSig ss = (s instanceof SubsetSig) ? (SubsetSig)s : null;
            int scope = sigScope.startingScope();
            boolean exact = sigScope.isExact();
            if (sigScope instanceof IntSubsetScope) {
                intSubScope = (IntSubsetScope) sigScope;
                if (!s.isIntSubsetSig()) throw new ErrorSyntax(sigScope.pos, "Cannot specify int scope on a sig that is not an Int subset sig");
            }
            if (s==UNIV) throw new ErrorSyntax(cmd.pos, "You cannot set a scope on \"univ\".");
            if (s==SIGINT) throw new ErrorSyntax(cmd.pos,
                    "You can no longer set a scope on \"Int\". "
                    +"The number of atoms in Int is always exactly equal to 2^(i" +
                    		"nteger bitwidth).\n");
            if (s==SEQIDX) throw new ErrorSyntax(cmd.pos,
                    "You cannot set a scope on \"seq/Int\". "
                    +"To set the maximum allowed sequence length, use the seq keyword.\n");
            if (s==STRING) {
               if (maxstring>=0) throw new ErrorSyntax(cmd.pos, "Sig \"String\" already has a scope of "+maxstring+", so we cannot set it to be "+scope);
               if (!exact) throw new ErrorSyntax(cmd.pos, "Sig \"String\" must have an exact scope.");
               maxstring = scope;
               continue;
            }
            if (s==NONE) throw new ErrorSyntax(cmd.pos, "You cannot set a scope on \"none\".");
            if (s.isEnum!=null) throw new ErrorSyntax(cmd.pos, "You cannot set a scope on the enum \""+s.label+"\"");
            if (s.isOne!=null && scope!=1) throw new ErrorSyntax(cmd.pos,
                "Sig \""+s+"\" has the multiplicity of \"one\", so its scope must be 1, and cannot be "+scope);
            if (s.isLone!=null && scope>1) throw new ErrorSyntax(cmd.pos,
                "Sig \""+s+"\" has the multiplicity of \"lone\", so its scope must 0 or 1, and cannot be "+scope);
            if (s.isSome!=null && scope<1) throw new ErrorSyntax(cmd.pos,
                "Sig \""+s+"\" has the multiplicity of \"some\", so its scope must 1 or above, and cannot be "+scope);
            if (ss != null && intSubScope != null) {
                intsubset2scope.put(ss, intSubScope);
            } else {
                sig2scope(s, scope);
            }
            if (exact) makeExact(cmd.pos, s);
        }
        // Force "one" sigs to be exactly one, and "lone" to be at most one
        for(Sig s:sigs) if (s instanceof PrimSig) {
            if (s.isOne!=null) { makeExact(cmd.pos, s); sig2scope(s,1); } else if (s.isLone!=null && sig2scope(s)!=0) sig2scope(s,1);
        }
        // Derive the implicit scopes
        while(true) {
            if (derive_partial_instance_scope(sigs)) { do {} while(derive_partial_instance_scope(sigs)); continue; }
            if (derive_abstract_scope(sigs))         { do {} while(derive_abstract_scope(sigs));         continue; }
            if (derive_overall_scope(sigs))          { do {} while(derive_overall_scope(sigs));          continue; }
            if (derive_scope_from_parent(sigs))      { do {} while(derive_scope_from_parent(sigs));      continue; }
            break;
        }
        
        if (intScope.bitwidth == null || intScope.atoms == null) throw new ErrorFatal("IntScope not computed properly");

        this.sig2scope.put(SIGINT, intScope.atoms.size());
        this.sig2scope.put(SEQIDX, 0);

        int maxInt = intScope.atoms.max();
        int maxseq = cmd.maxseq;
        if (maxseq<0) {
            if (cmd.overall>=0) maxseq=cmd.overall; else maxseq=4;
            if (maxseq > maxInt) maxseq = maxInt;
        }
        if (maxseq > maxInt) maxseq = maxInt; //TODO throw new ErrorSyntax(pos, "With integer bitwidth of "+bitwidth+", you cannot have sequence length longer than "+maxInt);
        if (maxseq < 0) maxseq = 0; //throw new ErrorSyntax(pos, "The maximum sequence length cannot be negative.");
        this.maxseq = maxseq;
        sig2scope.put(SEQIDX, maxseq);

        // Generate the atoms and the universe
        Set<String> intAtoms = new HashSet<String>(); 
        for(Sig s:sigs) if (s.isTopLevel()) computeLowerBound((PrimSig)s);
        for (int i : intScope.enumerate()) intAtoms.add(""+i);
        for (CommandScope cs : cmd.scope) if (cs instanceof IntSubsetScope) {
            for (int i : ((IntSubsetScope) cs).intScope.enumerate()) 
                intAtoms.add(""+i);
        }
        atoms.addAll(intAtoms);
    }

    //===========================================================================================================================//

    private static Command resolveIntScopes(PartialInstance pi, Iterable<Sig> sigs, Command cmd) throws Err {
        boolean shouldUseInts = CompUtil.areIntsUsed(sigs, cmd);
        Collection<Integer> intLiterals = CompUtil.extractIntLiterals(sigs, cmd);
        IntScope newIntScope = resolveIntScope(cmd.intScope, pi, shouldUseInts, intLiterals);
        cmd = cmd.change(newIntScope);
        List<CommandScope> scope = new ArrayList<CommandScope>(cmd.scope.size());
        PartialInstance emptyPI = new PartialInstance();
        for (CommandScope cs : cmd.scope) {
            if (cs instanceof IntSubsetScope) {
                IntSubsetScope intSubsetScope = (IntSubsetScope) cs;
                scope.add(intSubsetScope.change(resolveIntScope(intSubsetScope.intScope, emptyPI, shouldUseInts, intLiterals)));
            } else if (cs.sig.isIntSubsetSig()) {
                IntSubsetScope intSubScope = (cs instanceof IntSubsetScope) 
                        ? (IntSubsetScope) cs 
                        : new IntSubsetScope(cs.pos, cs.sig, IntScope.mkBitwidth(cs.startingScope()));
                scope.add(intSubScope.change(resolveIntScope(intSubScope.intScope, emptyPI, shouldUseInts, intLiterals)));                        
            } else {
                scope.add(cs);
            }
        }
        cmd = cmd.change(ConstList.make(scope));
        return cmd;
    }
    
    private static IntScope resolveIntScope(IntScope intScope, PartialInstance pi, boolean shouldUseInts, Collection<Integer> intLiterals) throws Err {
        IntScope ans = intScope != null ? intScope : IntScope.mkEmpty();

        // 1. if atoms are not set and partial instance is given,
        //    set atoms to AtomSet with atoms from the partial instance
        int[] piInts;
        if (ans.atoms == null && pi != null && (piInts=pi.ints()) != null) {
            ans = ans.withAtoms(new IntScope.AtomSet(null, piInts));
        }
        
        int bw = ans.bitwidth != null ? ans.bitwidth : (shouldUseInts ? DEFAULT_BITWIDTH : 0);

        // 2. compute and set atoms
        if (ans.atoms == null || ans.atoms instanceof IntScope.AtomsFullBitwidth) {
            // default is FullBitwidth, but enumerate now and represent it as AtomRange
            AtomsKind atoms = bw > 0 ? new AtomRange(null, Util.min(bw), Util.max(bw), 1)
                                     : new AtomSet(null, new int[0]);
            ans = ans.withAtoms(atoms);
        } else if (ans.atoms instanceof IntScope.AtomSet) {
            // add literals if need be
            AtomSet as = (AtomSet)ans.atoms;
            if (as.includeLiterals) {
                Collection<Integer> ints = new ArrayList<Integer>(intLiterals.size() + as.ints.size());
                ints.addAll(intLiterals);
                ints.addAll(as.ints);
                ans = ans.withAtoms(new IntScope.AtomSet(null, ints));
            }
        } else if (ans.atoms instanceof IntScope.AtomLiterals) {
            // convert to AtomSet
            ans = ans.withAtoms(new IntScope.AtomSet(null, intLiterals));
        }
        
        // 3. compute bitwidth
        //   - if explicitly set, keep it; otherwise convert literals to fit the bitwidth
        if (ans.bitwidth == null) {
            ans = ans.withBitwidth(Math.max(bw, Util.minBw(ans.atoms.min(), ans.atoms.max())));
        } else {
            Collection<Integer> ints = new ArrayList<Integer>(ans.atoms.size());
            int min = Util.min(ans.bitwidth);
            int max = Util.max(ans.bitwidth);
            if (ans.atoms.min() < min || ans.atoms.max() > max) {
                int mask = ~(-1 << ans.bitwidth);
                for (int i : ans.atoms.enumerateAccending()) {
                    if (i < min || i > max) {
                        i = i & mask;
                        if (i > max) i = (i - max - 1) + min;
                        else if (i < min) i = max - (min - i - 1);
                    }
                    ints.add(i);
                }
                ans = ans.withAtoms(new IntScope.AtomSet(null, ints));
            }
        }
        
        return ans;
    }
    
    /** Computes the scopes for each sig and computes the bitwidth and maximum sequence length.
     *
     * <p> The scopes are determined as follows:
     *
     * <p>  "run x": every topsig is scoped to <= 3 elements.
     *
     * <p>  "run x for N": every topsig is scoped to <= N elements.
     *
     * <p>  "run x for N but N1 SIG1, N2 SIG2...":
     * <br> Every sig following "but" is constrained explicitly.
     * <br> Any topsig that is
     * <br> a) not listed, and
     * <br> b) its scope is not derived otherwise
     * <br> will be scoped to have <= N elements.
     *
     * <p>  "run x for N1 SIG1, N2 SIG2..."
     * <br> Every sig following "but" is constrained explicitly.
     * <br> Any topsig that is
     * <br> a) not listed, and
     * <br> b) its scope is not derived otherwise
     * <br> we will give an error message.
     *
     * <p> Please see ScopeComputer.java for the exact rules for deriving the missing scopes.
     */
    static Pair<A4Solution,ScopeComputer> compute (IA4Reporter rep, A4Options opt, Iterable<Sig> sigs, Command cmd) throws Err {
        PartialInstance pi = new PartialInstanceParser(opt.partialInstance).parse();
        ScopeComputer sc = new ScopeComputer(rep, sigs, cmd, pi);
        cmd = sc.cmd;
        Set<String> set = cmd.getAllStringConstants(sigs);
        if (sc.maxstring>=0 && set.size()>sc.maxstring) rep.scope("Sig String expanded to contain all "+set.size()+" String constant(s) referenced by this command.\n");
        for(int i=0; set.size()<sc.maxstring; i++) set.add("\"String" + i + "\"");
        sc.atoms.addAll(set);
        A4Solution sol = new A4Solution(cmd.toString(), sc.intScope, sc.maxseq, set, sc.atoms, rep, opt, cmd.expects, pi);
        return new Pair<A4Solution,ScopeComputer>(sol, sc);
    }

}
