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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.ConstantExpression;
import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.IA4Reporter;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4compiler.ast.CommandScope;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.IntSubsetScope;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.AtomSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.SubsetSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Type;
import edu.mit.csail.sdg.alloy4compiler.translator.PartialInstance.Atom;
import edu.mit.csail.sdg.alloy4compiler.translator.PartialInstance.Fix;

/** Immutable; this class assigns each sig and field to some Kodkod relation or expression, then set the bounds. */

final class BoundsComputer {

    // It calls these A4Solution methods...
    // getFactory(), query(), a2k(), addRel(), addSig(), addField(), addFormula()

    /** Stores the reporter that will receive diagnostic messages. */
    private final IA4Reporter rep;

    /** Stores the scope, bounds, and other settings necessary for performing a solve. */
    private final A4Solution sol;

    /** Stores the factory. */
    private final TupleFactory factory;

    /** Stores the computed scope for each sig. */
    private final ScopeComputer sc;

    /** Stores the upperbound for each sig. */
    private final Map<Sig,TupleSet> ub = new LinkedHashMap<Sig,TupleSet>();

    /** Stores the lowerbound for each sig. */
    private final Map<Sig,TupleSet> lb = new LinkedHashMap<Sig,TupleSet>();

    //==============================================================================================================//

    private Tuple removeAtomByName(List<Tuple> atoms, Object atom) throws Err {
       Tuple res = null;
       int i = atoms.size() - 1;
       for (; i >= 0; i--) {
           Tuple t = atoms.get(i);
           if (t.atom(0).equals(atom)) {
               res = t;
               break;
           }
       }
       if (res == null) throw new ErrorFatal("Atom '" + atom + "' not found");
       atoms.remove(i);
       return res;
    }

    //==============================================================================================================//

    /** Computes the lowerbound from bottom-up; it will also set a suitable initial value for each sig's upperbound.
     * Precondition: sig is not a builtin sig
     */
    private TupleSet computeLowerBound(List<Tuple> atoms, final PrimSig sig) throws Err {
        int n = sc.sig2scope(sig);
        TupleSet lower = factory.noneOf(1);
        for(PrimSig c:sig.children()) lower.addAll(computeLowerBound(atoms, c));
        TupleSet upper = lower.clone();
        // [PI] add atoms from the partial instance
        List<Atom> sigLower = sc.pi.sigLower(sig.shortLabel());
        if (sigLower != null)
            for (Atom piAtom : sigLower)
                if (!lower.contains(factory.tuple(piAtom.label()))) {
                    Tuple atom = removeAtomByName(atoms, piAtom.label());
                    lower.add(atom);
                    upper.add(atom);
                }
        boolean isExact = sc.isExact(sig);
        if (isExact || sig.isTopLevel()) for(n=n-upper.size(); n>0; n--) {
           Tuple atom = atoms.remove(atoms.size()-1);
           if (!(atom.atom(0).toString().startsWith(sig.shortLabelNoPI()) || sig.atomSigShortLabels().contains(atom.atom(0).toString()))) {
               throw new ErrorFatal("wrong atom removed: atom = " + atom.toString() + "; sig = " + sig.shortLabelNoPI());
           }
           // If MUST<SCOPE and s is exact, then add fresh atoms to both LOWERBOUND and UPPERBOUND.
           // If MUST<SCOPE and s is inexact but toplevel, then add fresh atoms to the UPPERBOUND.
           if (isExact) lower.add(atom);
           upper.add(atom);
        }
        lb.put(sig, lower);
        ub.put(sig, upper);
        return lower;
    }

    //==============================================================================================================//

    /** Computes the upperbound from top-down, then allocate a relation for it.
     * Precondition: sig is not a builtin sig
     */
    private void computeUpperBound(PrimSig sig) throws Err {
        //TODO: check partial instance

        // Sig's upperbound is fully computed. We recursively compute the upperbound for children...
        TupleSet x = ub.get(sig).clone();
        // We remove atoms that MUST be in a subsig
        for(PrimSig c: sig.children()) x.removeAll(lb.get(c));
        // So now X is the set of atoms that MIGHT be in this sig, but MIGHT NOT be in any particular subsig.
        // For each subsig that may need more atom, we say it could potentially get any of the atom from X.
        for(PrimSig c: sig.children()) {
           if (sc.sig2scope(c) > lb.get(c).size()) ub.get(c).addAll(x);
           computeUpperBound(c);
        }

        //[PI] remove
    }

    //==============================================================================================================//

    private void allocateAtomSig(AtomSig sig) throws Err {
        TupleSet lower = factory.setOf(sig.shortLabel());
        Relation exp = sol.addRel(sig.label, lower, lower, true);
        sol.addSig(sig, exp);
    }

    /** Allocate relations for nonbuiltin PrimSigs bottom-up. */
    private Expression allocatePrimSig(PrimSig sig) throws Err {
        for (AtomSig as: sig.atomSigs()) allocateAtomSig(as);
        // Recursively allocate all children expressions, and form the union of them
        Expression sum = null;
        for(PrimSig child:sig.children()) {
           Expression childexpr=allocatePrimSig(child);
           if (sum==null) { sum=childexpr; continue; }
           // subsigs are disjoint
           sol.addFormula(sum.intersection(childexpr).no(), child.isSubsig);
           sum = sum.union(childexpr);
        }
        TupleSet lower = lb.get(sig).clone(), upper = ub.get(sig).clone();
        if (sum == null) {
           // If sig doesn't have children, then sig should make a fresh relation for itself
           sum = sol.addRel(sig.label, lower, upper, false);
        } else if (sig.isAbstract == null) {
           // If sig has children, and sig is not abstract, then create a new relation to act as the remainder.
           for(PrimSig child:sig.children()) {
              // Remove atoms that are KNOWN to be in a subsig;
              // it's okay to mistakenly leave some atoms in, since we will never solve for the "remainder" relation directly;
              // instead, we union the remainder with the children, then solve for the combined solution.
              // (Thus, the more we can remove, the more efficient it gets, but it is not crucial for correctness)
              TupleSet childTS = sol.query(false, sol.a2k(child), false);
              lower.removeAll(childTS);
              upper.removeAll(childTS);
           }
           sum = sum.union(sol.addRel(sig.label+" remainder", lower, upper, false));
        }
        sol.addSig(sig, sum);
        return sum;
    }

    //==============================================================================================================//

    /** Allocate relations for SubsetSig top-down. */
    private Expression allocateSubsetSig(SubsetSig sig) throws Err {
        // We must not visit the same SubsetSig more than once, so if we've been here already, then return the old value right away
        Expression sum = sol.a2k(sig);
        if (sum!=null && sum!=Expression.NONE) return sum;
        // check if it is a int subset sig and whether we have a bound for it
        IntSubsetScope iss = sc.intsub2scope(sig);
        if (iss != null) {
            TupleSet ts = factory.noneOf(1);
            for (int i : iss.intScope.enumerate()) {
                ts.add(factory.tuple(""+i));
            }
            Relation r = sol.addRel(sig.label, ts, ts, false);
            sol.addSig(sig, r);
            return r;
        }
        
        // Recursively form the union of all parent expressions
        TupleSet ts = factory.noneOf(1);
        for(Sig parent:sig.parents) {
           Expression p = (parent instanceof PrimSig) ? sol.a2k(parent) : allocateSubsetSig((SubsetSig)parent);
           ts.addAll(sol.query(true, p, false));
           if (sum==null) sum=p; else sum=sum.union(p);
        }
        // If subset is exact, then just use the "sum" as is
        if (sig.exact) { sol.addSig(sig, sum); return sum; }
        // Allocate a relation for this subset sig, then bound it
        rep.bound("Sig "+sig+" in "+ts+"\n");
        Relation r = sol.addRel(sig.label, null, ts, false);
        sol.addSig(sig, r);
        // Add a constraint that it is INDEED a subset of the union of its parents
        sol.addFormula(r.in(sum), sig.isSubset);
        return r;
    }

    //==============================================================================================================//

    /** Helper method that returns the constraint that the sig has exactly "n" elements, or at most "n" elements */
    private Formula size(Sig sig, int n, boolean exact) {
        Expression a = sol.a2k(sig);
        if (n<=0) return a.no();
        if (n==1) return exact ? a.one() : a.lone();
        Formula f = exact ? Formula.TRUE : null;
        Decls d = null;
        Expression sum = null;
        while(n>0) {
           n--;
           Variable v = Variable.unary("v" + Integer.toString(TranslateAlloyToKodkod.cnt++));
           kodkod.ast.Decl dd = v.oneOf(a);
           if (d==null) d=dd; else d=dd.and(d);
           if (sum==null) sum=v; else { if (f!=null) f=v.intersection(sum).no().and(f); sum=v.union(sum); }
        }
        if (f!=null) return sum.eq(a).and(f).forSome(d); else return a.no().or(sum.eq(a).forSome(d));
    }

    //==============================================================================================================//

    /** If ex is a simple combination of Relations, then return that combination, else return null. */
    private Expression sim(Expr ex) {
        while(ex instanceof ExprUnary) {
           ExprUnary u = (ExprUnary)ex;
           if (u.op!=ExprUnary.Op.NOOP && u.op!=ExprUnary.Op.EXACTLYOF) break;
           ex = u.sub;
        }
        if (ex instanceof ExprBinary) {
           ExprBinary b = (ExprBinary)ex;
           if (b.op==ExprBinary.Op.ARROW || b.op==ExprBinary.Op.PLUS || b.op==ExprBinary.Op.JOIN) {
              Expression left = sim(b.left);  if (left==null) return null;
              Expression right = sim(b.right); if (right==null) return null;
              if (b.op==ExprBinary.Op.ARROW) return left.product(right);
              if (b.op==ExprBinary.Op.PLUS) return left.union(right); else return left.join(right);
           }
        }
        if (ex instanceof ExprConstant) {
           switch(((ExprConstant)ex).op) {
              case EMPTYNESS: return Expression.NONE;
              default:        break;
           }
        }
        if (ex==Sig.NONE) return Expression.NONE;
        if (ex==Sig.SIGINT) return Expression.INTS;
        if (ex instanceof Sig) return sol.a2k((Sig)ex);
        if (ex instanceof Field) return sol.a2k((Field)ex);
        return null;
    }

    /** Computes the bounds for sigs/fields, then construct a BoundsComputer object that you can query. */
    private BoundsComputer(IA4Reporter rep, A4Solution sol, ScopeComputer sc, Iterable<Sig> sigs) throws Err {
        this.sc = sc;
        this.factory = sol.getFactory();
        this.rep = rep;
        this.sol = sol;
        // Figure out the sig bounds
        final Universe universe = factory.universe();
        final int atomN = universe.size();
        final List<Tuple> atoms = new ArrayList<Tuple>(atomN);
        for(int i=atomN-1; i>=0; i--) atoms.add(factory.tuple(universe.atom(i)));
        for(Sig s:sigs) if (!s.builtin && s.isTopLevel()) computeLowerBound(atoms, (PrimSig)s);
        for(Sig s:sigs) if (!s.builtin && s.isTopLevel()) computeUpperBound((PrimSig)s);
        // Bound the sigs
        for(Sig s:sigs) if (!s.builtin && s.isTopLevel()) allocatePrimSig((PrimSig)s);
        for(Sig s:sigs) if (s instanceof SubsetSig) allocateSubsetSig((SubsetSig)s);

        if (sol.createAtomRelations()) {
            for (Pair<String, PrimSig> p : sc.getNewAtoms()) {
                AtomSig asig = new AtomSig(p.a, p.b);
                allocateAtomSig(asig);
            }
        }

        // Bound the fields
        again:
        for(Sig s:sigs) {
           while (s.isOne!=null && s.getFieldDecls().size()==2 && s.getFields().size()==2 && s.getFacts().size()==1) {
              // Let's check whether this is a total ordering on an enum...
              Expr fact = s.getFacts().get(0).deNOP(), b1 = s.getFieldDecls().get(0).expr.deNOP(), b2 = s.getFieldDecls().get(1).expr.deNOP(), b3;
              if (!(fact instanceof ExprList) || !(b1 instanceof ExprUnary) || !(b2 instanceof ExprBinary)) break;
              ExprList list = (ExprList)fact;
              if (list.op!=ExprList.Op.TOTALORDER || list.args.size()!=3) break;
              if (((ExprUnary)b1).op!=ExprUnary.Op.SETOF) break; else b1 = ((ExprUnary)b1).sub.deNOP();
              if (((ExprBinary)b2).op!=ExprBinary.Op.ARROW) break; else { b3 = ((ExprBinary)b2).right.deNOP(); b2 = ((ExprBinary)b2).left.deNOP(); }
              if (!(b1 instanceof PrimSig) || b1!=b2 || b1!=b3) break;
              PrimSig sub = (PrimSig)b1;
              Field f1 = s.getFields().get(0), f2 = s.getFields().get(1);
              if (sub.isEnum==null || !list.args.get(0).isSame(sub) || !list.args.get(1).isSame(s.join(f1)) || !list.args.get(2).isSame(s.join(f2))) break;
              // Now, we've confirmed it is a total ordering on an enum. Let's pre-bind the relations
              TupleSet me = sol.query(true, sol.a2k(s), false), firstTS = factory.noneOf(2), lastTS = null, nextTS = factory.noneOf(3);
              if (me.size()!=1 || me.arity()!=1) break;
              int n = sub.children().size();
              for(PrimSig c: sub.children()) {
                 TupleSet TS = sol.query(true, sol.a2k(c), false);
                 if (TS.size()!=1 || TS.arity()!=1) { firstTS=factory.noneOf(2); nextTS=factory.noneOf(3); break; }
                 if (lastTS==null) { firstTS=me.product(TS); lastTS=TS; continue; }
                 nextTS.addAll(me.product(lastTS).product(TS));
                 lastTS=TS;
              }
              if (firstTS.size()!=(n>0 ? 1 : 0) || nextTS.size() != n-1) break;
              sol.addField(f1, sol.addRel(s.label+"."+f1.label, firstTS, firstTS, false));
              sol.addField(f2, sol.addRel(s.label+"."+f2.label, nextTS, nextTS, false));
              rep.bound("Field "+s.label+"."+f1.label+" == "+firstTS+"\n");
              rep.bound("Field "+s.label+"."+f2.label+" == "+nextTS+"\n");
              continue again;
           }
           for(Field f:s.getFields()) {
              Expression kkBound = sol.a2k(f.bound, true);
              boolean isOne = s.isOne!=null;
              if (isOne && f.decl().expr.mult()==ExprUnary.Op.EXACTLYOF) {
                 Expression sim = sim(f.decl().expr);
                 if (sim!=null) {
                    rep.bound("Field "+s.label+"."+f.label+" defined to be "+sim+"\n");
                    sol.addField(f, sol.a2k(s).product(sim));
                    continue;
                 }
              }
              Type t = isOne ? Sig.UNIV.type().join(f.type()) : f.type();
              //compute upper
              TupleSet ub = factory.noneOf(t.arity());
              for(List<PrimSig> p:t.fold()) {
                 TupleSet upper=null;
                 int col = 0;
                 for(PrimSig b:p) {
                    Expression kkExpr = sol.a2k(b);
                    CommandScope scope = null;
                    TupleSet tmp = null;
                    if (col > 0 && kkExpr == ConstantExpression.INTS && (scope=extractScope(f.bound, col-1)) != null) {
                        tmp = factory.setOf(scope.enumerateAsString().toArray());
                    } else if (kkExpr == ConstantExpression.INTS && kkBound != null) {
                        tmp = sol.query(true, kkBound, false);
                    } else {
                        tmp = sol.query(true, kkExpr, false);
                    }
                    if (upper==null) upper=tmp; else upper=upper.product(tmp);
                    col++;
                 }
                 ub.addAll(upper);
              }
              // compute bounds from partial instance
              TupleSet piLb = null;
              List<List<Atom>> fldLo = sc.pi.fldLower2(s.shortLabel(), f.label, ub.arity());
              if (fldLo != null) piLb = toKodkodTupleSet(fldLo, ub.arity(), sigs);

              // use only those explicitly specified in the partial instance
              List<List<Atom>> fldHi = sc.pi.fldUpper2(s.shortLabel(), f.label, ub.arity());
              if (fldHi != null) ub.retainAll(toKodkodTupleSet(fldHi, ub.arity(), sigs));
              // additionally shrink for fixes
              ArrayList<Fix> fixes = sc.pi.fixesForFld(s.shortLabel(), f.label);
              if (fixes.size() > 0) {
                 Aux[] fixAux = new Aux[fixes.size()];
                 for (int i = 0; i < fixAux.length; i++) {
                    Fix fix = fixes.get(i);
                    fixAux[i] = new Aux(fix.idx, fix.atom.toString(), toKodkodTupleSet(sc.pi.fixValue(fix), ub.arity(), sigs));
                 }
                 Collection<Tuple> tuplesToRemove = new ArrayList<Tuple>();
                 for (Tuple ubTuple: ub) {
                    for (Aux fix : fixAux) {
                       if (ubTuple.atom(fix.idx).equals(fix.atom.toString()))
                          if (!fix.ts.contains(ubTuple))
                             tuplesToRemove.add(ubTuple);
                     }
                 }
                 ub.removeAll(tuplesToRemove);
              }

              //*******************************************************************************************
              //TODO: temp testing, remove
//              final Set<String> rels = new HashSet<String>(Arrays.asList("left", "right", "then", "elsen"));
//              final Set<String> leftthen = new HashSet<String>(Arrays.asList("left", "then"));
//              final Set<String> rightelsen = new HashSet<String>(Arrays.asList("right", "elsen"));
//              if (rels.contains(f.label) && ub.size() > 0 && ub.arity() == 2) {
//                 String[] prefixes = new String[] { 
//                         "Nand", "And", "AndInv", "BvOr", "BvShl", "BvAnd", "GTE", "ITE"
//                 };
//                 Collection<Tuple> tuplesToRemove = new ArrayList<Tuple>();
//                 for (Tuple ubTuple: ub) {
//                    String lhsAtom = (String)ubTuple.atom(0);
//                    String rhsAtom = (String)ubTuple.atom(1);
//                    String[] lhsPrefixAndIndex = lhsAtom.split("\\$");
//                    String[] rhsPrefixAndIndex = rhsAtom.split("\\$");
//                    String prefix = null;
//                    for (String p : prefixes) {
//                       if (lhsPrefixAndIndex[0].endsWith(p) && rhsPrefixAndIndex[0].endsWith(p)) {
//                           prefix = p;
//                           break;
//                       }
//                    }
//                    if (prefix != null) {
//                        int lhsIdx = Integer.parseInt(lhsPrefixAndIndex[1]);
//                        int rhsIdx = Integer.parseInt(rhsPrefixAndIndex[1]);
//                        //if (lhsIdx >= rhsIdx) tuplesToRemove.add(ubTuple);
//                        if (lhsIdx >= rhsIdx) tuplesToRemove.add(ubTuple);
//                        if ((leftthen.contains(f.label) && rhsIdx > (lhsIdx*2)+1) ||
//                            (rightelsen.contains(f.label) && rhsIdx > (lhsIdx+1)*2))
//                                tuplesToRemove.add(ubTuple);
//                    }
//                 }
//                 if (tuplesToRemove.size() > 0) {
//                     int s1 = ub.size();
//                     ub.removeAll(tuplesToRemove);
//                     int s2 = ub.size();
//                     rep.bound(" *** Partial order reduction for "+s.label+"."+f.label+": "+s1+" -> "+s2+"\n");
//                 }
//              }
              //------------------

              Relation r = sol.addRel(s.label+"."+f.label, piLb, ub, s.isAtom != null);
              sol.addField(f, isOne ? sol.a2k(s).product(r) : r);
           }
        }
        // Add any additional SIZE constraints
        for(Sig s:sigs) if (!s.builtin) {
            Expression exp = sol.a2k(s);
            TupleSet upper = sol.query(true,exp,false), lower=sol.query(false,exp,false);
            final int n = sc.sig2scope(s);
            if (s.isOne!=null && (lower.size()!=1 || upper.size()!=1)) {
                rep.bound("Sig "+s+" in "+upper+" with size==1\n");
                sol.addFormula(exp.one(), s.isOne);
                continue;
            }
            if (s.isSome!=null && lower.size()<1) sol.addFormula(exp.some(), s.isSome);
            if (s.isLone!=null && upper.size()>1) sol.addFormula(exp.lone(), s.isLone);
            if (n<0) continue; // This means no scope was specified
            if (lower.size()==n && upper.size()==n && sc.isExact(s)) {
                rep.bound("Sig "+s+" == "+upper+"\n");
            }
            else if (sc.isExact(s)) {
                rep.bound("Sig "+s+" in "+upper+" with size=="+n+"\n");
                sol.addFormula(size(s,n,true), Pos.UNKNOWN);
            }
            else if (upper.size()<=n){
                rep.bound("Sig "+s+" in "+upper+"\n");
            }
            else {
                rep.bound("Sig "+s+" in "+upper+" with size<="+n+"\n");
                sol.addFormula(size(s,n,false), Pos.UNKNOWN);
            }
        }
    }

    //==============================================================================================================//
    
    private Integer exprArity(Expr e) {
        if ((e instanceof ExprVar) || (e instanceof Sig))
            return 1;
        if (e instanceof ExprUnary)
            return exprArity(((ExprUnary) e).sub);
        if (e instanceof ExprBinary) {
            Integer l = exprArity(((ExprBinary) e).left);
            if (l == null) return null;
            Integer r = exprArity(((ExprBinary) e).right);
            if (r == null) return null;
            return l + r;
        }
        return null;
    }
    private CommandScope extractScope(Expr e, int col) {
        Integer arity = exprArity(e);
        if (arity == null) return null;
        if (col >= arity) return null;
        if (e instanceof ExprUnary) {
            if (arity == 1 && col == 0)
                return ((ExprUnary) e).scope;
            else
                return extractScope(((ExprUnary) e).sub, col);
        }
        if (e instanceof ExprBinary) {
            Integer leftArity = exprArity(((ExprBinary) e).left);
            if (leftArity == null) return null;
            Integer rightArity = exprArity(((ExprBinary) e).right);
            if (rightArity == null) return null;
            if (col < leftArity)
                return extractScope(((ExprBinary) e).left, col);
            else
                return extractScope(((ExprBinary) e).right, col - leftArity);
        }
        return null;
    }

    private TupleSet toKodkodTupleSet(List<List<Atom>> piTs, int arity, Iterable<Sig> sigs) throws ErrorFatal {
        TupleSet ts = factory.noneOf(arity);
        for (List<Atom> t : piTs) {
            TupleSet tst = null;
            for (Atom a : t) {
                TupleSet curr;
                if (a.allOf) {
                    if ("Int".equals(a.label)) {
                        curr = factory.setOf((Object[])sol.intScope().enumerateAsString().toArray());
                    } else {
                        curr = ub.get(findSig(sigs, a.label));
                    }
                } else {
                    curr = factory.setOf(a.label());
                }
                if (curr == null) throw new ErrorFatal("nothing found for column " + a);
                if (tst == null) tst = curr; else tst = tst.product(curr);
            }
            ts.addAll(tst);
        }
        return ts;
    }

    private static Object findSig(Iterable<Sig> sigs, String name) throws ErrorFatal {
        for (Sig s: sigs) {
            if (s.label.equals(name) || s.label.endsWith("/" + name))
                return s;
        }
        throw new ErrorFatal(String.format("Sig %s not found", name));
    }

    /** Assign each sig and field to some Kodkod relation or expression, then set the bounds. */
    static void compute (IA4Reporter rep, A4Solution sol, ScopeComputer sc, Iterable<Sig> sigs) throws Err {
        new BoundsComputer(rep, sol, sc, sigs);
    }

    class Aux {
       public final int idx;
       public final String atom;
       public final TupleSet ts;
       public Aux(int idx, String atom, TupleSet ts) {
          this.idx = idx;
          this.atom = atom;
          this.ts = ts;
       }
    }
}
