package edu.mit.csail.sdg.alloy4compiler.ast;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4compiler.ast.Attr.AttrType;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;


public class IntScope extends CommandScope {

    public static abstract class AtomsKind {
        public final void toXML(PrintWriter out, String indent) {
            String atomsKind = getClass().getSimpleName();
            Util.encodeXMLs(out, "\n"+indent+"<atoms kind=\"", atomsKind, "\">");
            if (this instanceof AtomRange) {
                AtomRange ar = (AtomRange)this;
                out.print("\n"+indent+"  <start val=\"" + ar.start + "\"/>");
                out.print("\n"+indent+"  <end val=\""   + ar.end   + "\"/>");
                out.print("\n"+indent+"  <inc val=\""  + ar.inc   + "\"/>");
            } else if (this instanceof AtomSet) {
                for (int i : ((AtomSet)this).ints) {
                    out.print("\n"+indent+"  <int val=\"" + i + "\"/>");
                }
            }
            out.print("\n"+indent+"</atoms>");
        }
        public static AtomsKind fromXML(XMLNode node) throws Err {
            String kind = node.getAttribute("kind", null);
            if ("AtomLiterals".equals(kind)) return new AtomLiterals(null);
            if ("AtomFullBitwidth".equals(kind)) return new AtomsFullBitwidth(null);
            if ("AtomSet".equals(kind)) {
                SortedSet<Integer> ints = new TreeSet<Integer>();
                for (XMLNode intNode : node.getChildren("int"))
                    ints.add(Integer.parseInt(intNode.getAttribute("val")));
                return new AtomSet(null, ints);
            }
            if ("AtomRange".equals(kind)) {
                int start = Integer.parseInt(node.getChildren("start").iterator().next().getAttribute("val"));
                int end = Integer.parseInt(node.getChildren("end").iterator().next().getAttribute("val"));
                int inc = Integer.parseInt(node.getChildren("inc").iterator().next().getAttribute("val"));
                return new AtomRange(null, start, end, inc);
            }
            throw new ErrorFatal("Unknown atom kind: " + kind);
        }
        public static AtomsKind mergeAtoms(AtomsKind a, AtomsKind b) throws Err {
            if (a instanceof AtomsFullBitwidth && b instanceof AtomsFullBitwidth) return a;
            if (a instanceof AtomsFullBitwidth) throw new ErrorFatal(a.p, "cannot merge with AtomsFullBitwidth");
            if (b instanceof AtomsFullBitwidth) throw new ErrorFatal(b.p, "cannot merge with AtomsFullBitwidth");
            if (a instanceof AtomLiterals && b instanceof AtomLiterals) return a;
            if (a instanceof AtomLiterals && b instanceof AtomSet) return new AtomSet(a.p, ((AtomSet)b).ints, true);
            if (a instanceof AtomSet && b instanceof AtomLiterals) return new AtomSet(a.p, ((AtomSet)a).ints, true);
            if (a instanceof AtomSet && b instanceof AtomSet) {
                AtomSet aa = (AtomSet)a;
                AtomSet bb = (AtomSet)b;
                TreeSet<Integer> ts = new TreeSet<Integer>(((AtomSet)a).ints);
                ts.addAll(((AtomSet)b).ints);
                return new AtomSet(a.p, ts, aa.includeLiterals || bb.includeLiterals);
            }
            throw new ErrorFatal(a.p, "cannot merge "+a.getClass().getSimpleName()+" and "+b.getClass().getSimpleName());
        }
        public final Pos p;
        public AtomsKind(Pos p) {
            this.p = p;
        }
        abstract public AtomsKind withPos(Pos p) throws ErrorSyntax;
        /** Returns the smallest allowed integer, or 0 if no integers are allowed */
        public int min()      throws ErrorFatal   { throw new ErrorFatal("Can't query min for " + this.getClass().getSimpleName()); }
        /** Returns the largest allowed integer, or -1 if no integers are allowed. */
        public int max()      throws ErrorFatal   { throw new ErrorFatal("Can't query max for " + this.getClass().getSimpleName()); }
        public Integer size() throws ErrorFatal   { throw new ErrorFatal("Can't query size for " + this.getClass().getSimpleName()); }
        public boolean isEnumerable()             { return false; }
        public List<Integer> enumerateAccending() {
            throw new RuntimeException("Can't enumerate atoms for " + this.getClass().getSimpleName());
        }
        public AtomsKind addAtoms(AtomsKind other) throws Err { return AtomsKind.mergeAtoms(this, other); }
    }
    public static class AtomLiterals extends AtomsKind      {
        public AtomLiterals(Pos p)      { super(p); }
        public String toString()        { return "literals"; }
        public AtomsKind withPos(Pos p) { return new AtomLiterals(p); }
    }
    public static class AtomsFullBitwidth extends AtomsKind {
        public AtomsFullBitwidth(Pos p) { super(p); }
        public String toString()        { return "bitwidth"; }
        public AtomsKind withPos(Pos p) { return new AtomsFullBitwidth(p); }
    }
    public static class AtomSet extends AtomsKind {
        public final SortedSet<Integer> ints;
        public final boolean includeLiterals;
        public AtomSet(Pos p, int[] ints)                          { this(p, ints, false); }
        public AtomSet(Pos p, int[] ints, boolean includeLiterals) {
            super(p);
            TreeSet<Integer> set = new TreeSet<Integer>();
            for (int i : ints) set.add(i);
            this.ints = Collections.unmodifiableSortedSet(set);
            this.includeLiterals = includeLiterals;
        }
        public AtomSet(Pos p, SortedSet<Integer> ints)                          { this(p, ints, false); }
        public AtomSet(Pos p, SortedSet<Integer> ints, boolean includeLiterals) {
            super(p);
            this.ints = Collections.unmodifiableSortedSet(ints);
            this.includeLiterals = includeLiterals;
        }
        public AtomSet(Pos p, Collection<Integer> ints) {
            this(p, new TreeSet<Integer>(ints));
        }
        public AtomsKind withPos(Pos p) throws ErrorSyntax { 
            return new AtomSet(p, ints, includeLiterals); 
        }        
        public int min()                          { return ints.size() > 0 ? ints.first() : 0 ; }
        public int max()                          { return ints.size() > 0 ? ints.last() : -1; }
        public Integer size()                     { return ints.size(); }
        public List<Integer> enumerateAccending() { return new ArrayList<Integer>(ints); }
        public String toString() {
            StringBuilder joined = new StringBuilder();
            for (int i : ints) {
                if (joined.length() > 0) joined.append(", ");
                joined.append(i);
            }
            return "[" + joined + "]";
        }
    }
    public static class AtomRange extends AtomSet {
        public final int start, end, inc;
        private static List<Integer> range2list(int start, int end, int inc) {
            List<Integer> ans = new LinkedList<Integer>();
            ans.add(start);
            for (int i = start; i + inc < end; i += inc) ans.add(i+inc);
            ans.add(end);
            return ans;
        }
        /**
         * @requires start <= end
         * @requires inc > 0
         */
        public AtomRange(Pos p, int start, int end, int inc) throws ErrorSyntax {
            super(p, range2list(start, end, inc));
            if (inc <= 0 || end < start) throw new ErrorSyntax(p, "Invalid range");
            this.start = start;
            this.end = end;
            this.inc = inc;
        }
        public AtomsKind withPos(Pos p) throws ErrorSyntax { return new AtomRange(p, start, end, inc); }
        public int min() { return start; }
        public int max() { return end; }
        public String toString() {
            return String.format("%s..%s:%s", start, end, inc);
        }
    }

    public final Pos pos;
    public final Integer bitwidth;
    public final Integer ofBw;
    public final AtomsKind atoms;

    public static IntScope mkEmpty()                { try { return new IntScope(null, null, null, null);     } catch (Exception e) { throw new RuntimeException("no way");} }
    public static IntScope mkPos(Pos pos)           { try { return new IntScope(pos, null, null, null);      } catch (Exception e) { throw new RuntimeException("no way");} }
    public static IntScope mkBitwidth(int bitwidth) { try { return new IntScope(null, bitwidth, null, null); } catch (Exception e) { throw new RuntimeException("no way");} }
    public static IntScope mkOfBw(int bitwidth)     { try { return new IntScope(null, null, bitwidth, null); } catch (Exception e) { throw new RuntimeException("no way");} }
    public static IntScope mkAtoms(AtomsKind atoms) { try { return new IntScope(null, null, null, atoms);    } catch (Exception e) { throw new RuntimeException("no way");} }

    public IntScope(Pos pos, Integer bitwidth, Integer ofBitwidth, AtomsKind atoms) throws ErrorSyntax, Err {
        super(new PrimSig("int", AttrType.WHERE.make(pos)), false, bitwidth != null ? bitwidth : -1);
        this.pos = pos;
        this.bitwidth = bitwidth;
        this.ofBw = ofBitwidth;
        this.atoms = atoms;
    }

    public IntScope clone() {
        try {
            return new IntScope(pos, bitwidth, ofBw, atoms);
        } catch (Exception e) {
            throw new RuntimeException("Could not create IntScope", e);
        }
    }

    public String toString() {
        return String.format("{bitwidth: %s, atoms: %s}", bitwidth, atoms);
    }

    public IntScope withPos(Pos p)             throws ErrorSyntax, Err { return this.merge(IntScope.mkPos(p)); }
    public IntScope withBitwidth(int bitwidth) throws ErrorSyntax, Err { return this.merge(IntScope.mkBitwidth(bitwidth)); }
    public IntScope withAtoms(AtomsKind atoms) throws ErrorSyntax, Err { return this.merge(IntScope.mkAtoms(atoms)); }

    public IntScope merge(IntScope other) throws ErrorSyntax, Err {
        return new IntScope(
                other.pos      != null ? other.pos      : this.pos,
                other.bitwidth != null ? other.bitwidth : this.bitwidth,
                other.ofBw     != null ? other.ofBw     : this.ofBw,
                other.atoms    != null ? other.atoms    : this.atoms);
    }

    public List<Integer> enumerate()          { return atoms.enumerateAccending(); }
    public List<Integer> enumerateAccending() { return atoms.enumerateAccending(); }

    public int minInt()   throws ErrorFatal { return atoms.min(); }
    public int maxInt()   throws ErrorFatal { return atoms.max(); }
    public int bitwidth() throws ErrorFatal { if (bitwidth == null) throw new ErrorFatal("Bitwidth not computed yet"); return bitwidth; }


}
