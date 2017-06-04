package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public class PartialInstance {
    public static class Atom {
        public final String type;
        public final String label;
        public final boolean allOf;

        public Atom(String type, String label)                { this(type, label, false); }
        public Atom(String type, String label, boolean allOf) {
            this.type = type;
            this.label = label;
            this.allOf = allOf;
        }

        public String label() { return label; }

        @Override public String toString() { return label(); }
        @Override public int hashCode()    { return toString().hashCode(); }
        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null) return false;
            if (getClass() != obj.getClass()) return false;
            return toString().equals(obj.toString());
        }

        public static Atom parse(String fullName) {
            String[] arr = fullName.split("\\$");
            if (arr.length == 2) {
                return new Atom(arr[0], arr[1]);
            } else {
                assert arr.length == 1;
                try {
                    Integer.parseInt(fullName);
                    return new Atom("Int", fullName);
                } catch (NumberFormatException e) {
                    return new Atom(null, fullName, true);
                }

            }
        }
    }

    public static abstract class Rel {
        @Override public int hashCode() { return toString().hashCode(); }
        @Override public boolean equals(Object obj) {
            if (obj == null) return false;
            if (!(obj instanceof Rel)) return false;
            return toString().equals(obj.toString());
        }
    }
    public static class SigRel extends Rel {
        public final String sigName;
        public SigRel(String sigName) { this.sigName = sigName; }
        @Override public String toString() { return sigName; }
    }
    public static class FieldRel extends Rel {
        public final String sigName, fldName;
        public FieldRel(String sigName, String fldName) {
            this.sigName = sigName;
            this.fldName = fldName;
        }
        @Override public String toString() { return sigName + "." + fldName; }
    }
    public static class Fix extends Rel{
        public final Rel rel;
        public final int idx;
        public final Atom atom;
        public Fix(Rel rel, int idx, Atom atom) {
            this.rel = rel;
            this.idx = idx;
            this.atom = atom;
        }
        @Override public String toString() { return String.format("%s:%d:%s", rel, idx, atom); }
    }
    private Map<String, Atom> universe;
    private int[] ints;
    private Map<Rel, List<List<Atom>>> lowers;
    private Map<Rel, List<List<Atom>>> uppers;
    private Map<Fix, List<List<Atom>>> fixes;

    public PartialInstance() {
        universe = new HashMap<String, PartialInstance.Atom>();
        ints = null;
        lowers = new HashMap<PartialInstance.Rel, List<List<Atom>>>();
        uppers = new HashMap<PartialInstance.Rel, List<List<Atom>>>();
        fixes = new HashMap<PartialInstance.Fix, List<List<Atom>>>();
    }

    public Collection<Atom> getUniverse()         { return universe.values(); }
    public Map<Rel, List<List<Atom>>> getLowers() { return lowers; }
    public Map<Rel, List<List<Atom>>> getUppers() { return uppers; }
    public Map<Fix, List<List<Atom>>> getFixes()  { return fixes; }

    public List<Atom> atomsForType(String type) {
        List<Atom> ans = new ArrayList<PartialInstance.Atom>();
        if (type == null) return ans;
        for (Entry<String, Atom> e : universe.entrySet()) if (type.equals(e.getValue().type)) ans.add(e.getValue());
        return ans;
    }

    public int[] ints() { return ints != null ? Arrays.copyOf(ints, ints.length) : null; }

    public Atom findOrNewAtom(String label) {
        Atom a = universe.get(label);
        if (a == null) a = Atom.parse(label);
        return a;
    }

    public ArrayList<Fix> fixesFor(Rel rel) {
        ArrayList<Fix> ans = new ArrayList<PartialInstance.Fix>();
        for (Fix f: fixes.keySet()) if (f.rel.equals(rel)) ans.add(f);
        return ans;
    }

    public ArrayList<Fix> fixesForFld(String sigName, String fldName) {
        return fixesFor(new FieldRel(sigName, fldName));
    }

    public List<List<Atom>> fixValue(Fix fix) { return fixes.get(fix); }

    public List<Atom> sigLower(String sigName) { return compactUnaryTupleSet(withFixes(lowers, new SigRel(sigName))); }
    public List<Atom> sigUpper(String sigName) { return compactUnaryTupleSet(uppers.get(new SigRel(sigName))); }

    public List<List<Atom>> fldLower(String sigName, String fldName) { return withFixes(lowers, new FieldRel(sigName, fldName)); }
    public List<List<Atom>> fldUpper(String sigName, String fldName) { return uppers.get(new FieldRel(sigName, fldName)); }

//    public List<List<String>> fldLower2(String sigName, String fldName, boolean skipDomain) {
//        return mapAtomsToLabels(fldLower(sigName, fldName), skipDomain);
//    }
//    public List<List<String>> fldUpper2(String sigName, String fldName, boolean skipDomain) {
//        return mapAtomsToLabels(fldUpper(sigName, fldName), skipDomain);
//    }

    public List<List<Atom>> fldLower2(String sigName, String fldName, int arity) {
        List<List<Atom>> ts = fldLower(sigName, fldName);
        return project(ts, -arity, -1);
    }
    public List<List<Atom>> fldUpper2(String sigName, String fldName, int arity) {
        List<List<Atom>> ts = fldUpper(sigName, fldName);
        return project(ts, -arity, -1);
    }

    public void setUniverse(List<Atom> atoms)                { universe.clear(); for (Atom a : atoms) universe.put(a.label(), a); }
    public void setLower(Rel rel, List<List<Atom>> tupleSet) { lowers.put(rel, tupleSet); }
    public void setUpper(Rel rel, List<List<Atom>> tupleSet) { uppers.put(rel, tupleSet); }
    public void setInts(List<Atom> intAtoms) {
        this.ints = new int[intAtoms.size()];
        int idx = 0;
        for (Atom a: intAtoms) this.ints[idx++] = Integer.parseInt(a.label);
    }

    public void addFix(Fix fix, List<List<Atom>> tupleSet) { fixes.put(fix, tupleSet); }

    public static <E> List<List<E>> project(List<List<E>> tupleSet, int fstIdx, int lastIdx) {
        if (tupleSet == null) return null;
        List<List<E>> res = new ArrayList<List<E>>(tupleSet.size());
        for (List<E> tuple : tupleSet) {
            if (fstIdx < 0) fstIdx = tuple.size() + fstIdx;
            if (lastIdx < 0) lastIdx = tuple.size() + lastIdx;
            if (fstIdx < 0) return res;
            List<E> tt = new ArrayList<E>(lastIdx - fstIdx + 1);
            for (int i = fstIdx; i <= lastIdx; i++) { tt.add(tuple.get(i)); }
            res.add(tt);
        }
        return res;
    }

    public static List<List<String>> mapAtomsToLabels(List<List<Atom>> l, boolean skipDomain) {
        if (l == null) return null;
        List<List<String>> res = new ArrayList<List<String>>(l.size());
        for (List<Atom> t : l) {
            List<String> tLabels = new ArrayList<String>(t.size());
            for (int i = 0; i < t.size(); i++) if (i > 0 || !skipDomain) { tLabels.add(t.get(i).label()); }
            res.add(tLabels);
        }
        return res;
    }

    private List<Atom> compactUnaryTupleSet(List<List<Atom>> tupleSet) {
        if (tupleSet == null) return null;
        List<Atom> res = new ArrayList<Atom>(tupleSet.size());
        for (List<Atom> t : tupleSet) { assert t.size() == 1; res.add(t.get(0)); }
        return res;
    }

    private List<List<Atom>> withFixes(Map<Rel, List<List<Atom>>> from, Rel rel) {
        List<List<Atom>> ts = from.get(rel);
        ArrayList<Fix> relFixes = fixesFor(rel);
        if (ts == null && relFixes.size() == 0) return null;
        List<List<Atom>> ans = new ArrayList<List<Atom>>();
        if (ts != null) ans.addAll(ts);
        for (Fix f: relFixes) { ans.addAll(fixes.get(f)); }
        return ans;
    }

}
