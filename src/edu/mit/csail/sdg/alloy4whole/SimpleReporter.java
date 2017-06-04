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

package edu.mit.csail.sdg.alloy4whole;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Formula;
import kodkod.engine.hol.HOLTranslation;
import kodkod.engine.hol.HOLTranslationNew;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.util.nodes.PrettyPrinter;
import edu.mit.csail.sdg.alloy4.A4Preferences;
import edu.mit.csail.sdg.alloy4.A4Preferences.InstFormat;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstMap;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.IA4Reporter;
import edu.mit.csail.sdg.alloy4.MailBug;
import edu.mit.csail.sdg.alloy4.OurDialog;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.alloy4.WorkerEngine.WorkerCallback;
import edu.mit.csail.sdg.alloy4.WorkerEngine.WorkerTask;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4SolutionReader;
import edu.mit.csail.sdg.alloy4compiler.translator.A4SolutionWriter;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import edu.mit.csail.sdg.alloy4viz.StaticInstanceReader;
import edu.mit.csail.sdg.alloy4viz.VizGUI;

/** This helper method is used by SimpleGUI. */

final class SimpleReporter extends A4Reporter {

    public static final class SimpleCallback1 implements WorkerCallback {
        private final SimpleGUI gui;
        private final VizGUI viz;
        private final SwingLogPanel span;
        private final Set<ErrorWarning> warnings = new HashSet<ErrorWarning>();
        private final List<String> results = new ArrayList<String>();
        private final Map<String, Pair<Integer, String>> holTrPos = new HashMap<String, Pair<Integer, String>>();
        private final Map<String, Integer> seenFolTr = new HashMap<String, Integer>();
        private int len2=0, len3=0, verbosity=0;
        private final String latestName;
        private final int latestVersion;
        private String holIndent="";
        public SimpleCallback1(SimpleGUI gui, VizGUI viz, SwingLogPanel span, int verbosity, String latestName, int latestVersion) {
            this.gui=gui; this.viz=viz; this.span=span; this.verbosity=verbosity;
            this.latestName=latestName; this.latestVersion=latestVersion;
            len2 = len3 = span.getLength();
        }
        public void done() { if (viz!=null) span.setLength(len2); else span.logDivider(); span.flush(); gui.doStop(0); }
        public void fail() { span.logBold("\nAn error has occurred!\n"); span.logDivider(); span.flush(); gui.doStop(1); }
        public void callback(Object msg) {
            if (msg==null) { span.logBold("Done\n"); span.flush(); return; }
            if (msg instanceof String) { span.logBold( ((String)msg).trim() + "\n" ); span.flush(); return; }
            if (msg instanceof Throwable) {
                for(Throwable ex = (Throwable)msg; ex!=null; ex=ex.getCause()) {
                   if (ex instanceof OutOfMemoryError) {
                      span.logBold("\nFatal Error: the solver ran out of memory!\n" + "Try simplifying your model or reducing the scope,\n" + "or increase memory under the Options menu.\n");
                      return;
                   }
                   if (ex instanceof StackOverflowError) {
                      span.logBold("\nFatal Error: the solver ran out of stack space!\n" + "Try simplifying your model or reducing the scope,\n" + "or increase stack under the Options menu.\n");
                      return;
                   }
                }
            }
            if (msg instanceof Err) {
                Err ex = (Err)msg;
                String text = "fatal";
                boolean fatal = false;
                if (ex instanceof ErrorSyntax) text="syntax"; else if (ex instanceof ErrorType) text="type"; else fatal=true;
                if (ex.pos==Pos.UNKNOWN)
                    span.logBold("A "+text+" error has occurred:  ");
                else
                    span.logLink("A "+text+" error has occurred:  ", "POS: "+ex.pos.x+" "+ex.pos.y+" "+ex.pos.x2+" "+ex.pos.y2+" "+ex.pos.filename);
                if (verbosity>2) {
                    span.log("(see the "); span.logLink("stacktrace", "MSG: "+ex.dump()); span.log(")\n");
                } else {
                    span.log("\n");
                }
                span.logIndented(ex.msg.trim());
                span.log("\n");
                if (fatal && latestVersion>Version.buildNumber())
                    span.logBold(
                       "\nNote: You are running Alloy build#"+Version.buildNumber()+
                       ",\nbut the most recent is Alloy build#"+latestVersion+
                       ":\n( version "+latestName+" )\nPlease try to upgrade to the newest version,"+
                       "\nas the problem may have been fixed already.\n");
                span.flush();
                if (!fatal) gui.doVisualize("POS: "+ex.pos.x+" "+ex.pos.y+" "+ex.pos.x2+" "+ex.pos.y2+" "+ex.pos.filename);
                return;
            }
            if (msg instanceof Throwable) { Throwable ex = (Throwable)msg; span.logBold(ex.toString().trim()+"\n"); span.flush(); return; }
            if (!(msg instanceof Object[])) return;
            Object[] array = (Object[]) msg;
            if (array[0].equals("pop")) { span.setLength(len2); String x=(String)(array[1]); if (viz!=null && x.length()>0) OurDialog.alert(x); }
            if (array[0].equals("declare")) { gui.doSetLatest((String)(array[1])); }
            if (array[0].equals("S2")) { len3=len2=span.getLength(); span.logBold(""+array[1]); }
            if (array[0].equals("R3")) { span.setLength(len3); span.log(""+array[1]); }
            if (array[0].equals("link")) { span.logLink((String)(array[1]), (String)(array[2])); }
            if (array[0].equals("bold")) { span.logBold(""+array[1]); }
            if (array[0].equals("")) { span.log(""+array[1]); }
            if (array[0].equals("scope") && verbosity>0)  { span.log("   " + array[1]); }
            if (array[0].equals("bound") && verbosity>1)  { span.log("   " + array[1]); }
            if (array[0].equals("gensol") && verbosity>0) {
                span.log("   Generating the solution ");
                if (verbosity > 2) { formatLinks(array, 1); }
                span.log("...");
                gotoEnd(); }
            if (array[0].equals("hol-start"))          { logHOL(array, "started", false); }
            if (array[0].equals("hol-candidate"))      { logHOL(array, " candidate found", false); }
            if (array[0].equals("hol-verify"))         { logHOL(array, "  verifying candidate", true); holIndent(array, "   |- "); }
            if (array[0].equals("hol-verify-outcome")) {
                Pair<Integer, String> p = holTrPos.get(array[2]);
                if (p != null) {
                    if (array[4] == null) {
                        String pre = "success (";
                        String text = "#cand = " + array[5];
                        span.logAt(p.a, pre);
                        span.logBoldAt(p.a + pre.length(), text);
                        span.logAt(p.a + pre.length() + text.length(), ")");
                    } else {
                        formatLinkAt(p.a, array[4]);
                    }
                    holIndent = p.b;
                    gotoEnd(false);
                }
            }
            if (array[0].equals("hol-split"))              { logHOL(array, "solving splits", false); }
            if (array[0].equals("hol-next"))               { logHOL(array, "  searching for next candidate ", false); }
            if (array[0].equals("hol-split-choice"))       { logHOL(array, "  trying choice", true); }
            if (array[0].equals("hol-split-choice-sat"))   { Integer pos = getHOLpos(array[2]); if (pos != null){ formatLinkAt(pos, array[4]); gotoEnd(false); }}
            if (array[0].equals("hol-split-choice-unsat")) { Integer pos = getHOLpos(array[2]); if (pos != null){ span.logAt(pos, "unsat"); gotoEnd(false); }}
            if (array[0].equals("hol-fix-start"))          { logHOL(array, "solving fixpoint", false); }
            if (array[0].equals("hol-fix-unsat"))          { logHOL(array, "  no solution found", false); }
            if (array[0].equals("hol-fix-first"))          { logHOL(array, "  first solution found", false); }
            if (array[0].equals("hol-fix-inc"))            { logHOL(array, "  incrementing", true); }
            if (array[0].equals("hol-fix-inc-sat"))        { Integer pos = getHOLpos(array[2]); if (pos!=null) { formatLinkAt(pos, array[4]); gotoEnd(false); }}
            if (array[0].equals("hol-fix-inc-unsat"))      { Integer pos = getHOLpos(array[2]); if (pos!=null) { span.logAt(pos, "unsat"); gotoEnd(false); }}

            if (array[0].equals("resultCNF")) { results.add(null); span.setLength(len3); span.log("   File written to "+array[1]+"\n\n"); }
            if (array[0].equals("debug") && verbosity>2) { span.log("   "+array[1]+"\n"); len2=len3=span.getLength(); }
            if (array[0].equals("translate")) { span.log("   " + array[1]); len3 = span.getLength(); span.logBold("   Generating CNF...\n"); }
            if (array[0].equals("solve")) { span.setLength(len3); span.log("   " + array[1]); len3=span.getLength(); span.logBold("   Solving...\n"); }
            if (array[0].equals("warnings")) {
                if (warnings.size()==0) span.setLength(len2);
                else if (warnings.size()>1) span.logBold("Note: There were "+warnings.size()+" compilation warnings. Please scroll up to see them.\n\n");
                else span.logBold("Note: There was 1 compilation warning. Please scroll up to see them.\n\n");
                if (warnings.size()>0 && Boolean.FALSE.equals(array[1])) {
                   Pos e = warnings.iterator().next().pos;
                   gui.doVisualize("POS: "+e.x+" "+e.y+" "+e.x2+" "+e.y2+" "+e.filename);
                   span.logBold("Warnings often indicate errors in the model.\n"
                     +"Some warnings can affect the soundness of the analysis.\n"
                     +"To proceed despite the warnings, go to the Options menu.\n");
                }
            }
            if (array[0].equals("warning")) {
                ErrorWarning e = (ErrorWarning)(array[1]);
                if (!warnings.add(e)) return;
                Pos p=e.pos;
                span.logLink("Warning #"+warnings.size(), "POS: "+p.x+" "+p.y+" "+p.x2+" "+p.y2+" "+p.filename);
                span.log("\n"); span.logIndented(e.msg.trim()); span.log("\n\n");
            }
            if (array[0].equals("sat")) {
                boolean chk = Boolean.TRUE.equals(array[1]);
                int expects = (Integer) (array[2]);
                String filename = (String) (array[3]), formula = (String) (array[4]);
                results.add(filename);
                (new File(filename)).deleteOnExit();
                gui.doSetLatest(filename);
                span.setLength(len3);
                span.log("   ");
                span.logLink(chk ? "Counterexample" : "Instance", "XML: "+filename);
                span.log(" found. ");
                span.logLink(chk?"Assertion":"Predicate", formula); span.log(chk?" is invalid":" is consistent");
                if (expects==0) span.log(", contrary to expectation"); else if (expects==1) span.log(", as expected");
                span.log(". "+array[5]+"ms.\n\n");
            }
            if (array[0].equals("metamodel")) {
                String outf = (String) (array[1]);
                span.setLength(len2);
                (new File(outf)).deleteOnExit();
                gui.doSetLatest(outf);
                span.logLink("Metamodel", "XML: "+outf);
                span.log(" successfully generated.\n\n");
            }
            if (array[0].equals("minimizing")) {
                boolean chk = Boolean.TRUE.equals(array[1]);
                int expects = (Integer) (array[2]);
                span.setLength(len3);
                span.log(chk ? "   No counterexample found." : "   No instance found.");
                if (chk) span.log(" Assertion may be valid"); else span.log(" Predicate may be inconsistent");
                if (expects==1) span.log(", contrary to expectation"); else if (expects==0) span.log(", as expected");
                span.log(". "+array[4]+"ms.\n");
                span.logBold("   Minimizing the unsat core of "+array[3]+" entries...\n");
            }
            if (array[0].equals("unsat")) {
                boolean chk = Boolean.TRUE.equals(array[1]);
                int expects = (Integer) (array[2]);
                String formula = (String) (array[4]);
                span.setLength(len3);
                span.log(chk ? "   No counterexample found. " : "   No instance found. ");
                span.logLink(chk ? "Assertion" : "Predicate", formula);
                span.log(chk? " may be valid" : " may be inconsistent");
                if (expects==1) span.log(", contrary to expectation"); else if (expects==0) span.log(", as expected");
                if (array.length==5) { span.log(". "+array[3]+"ms.\n\n"); span.flush(); return; }
                String core = (String) (array[5]);
                int mbefore = (Integer) (array[6]), mafter = (Integer) (array[7]);
                span.log(". "+array[3]+"ms.\n");
                if (core.length()==0) { results.add(""); span.log("   No unsat core is available in this case. "+array[8]+"ms.\n\n"); span.flush(); return; }
                results.add(core);
                (new File(core)).deleteOnExit();
                span.log("   ");
                span.logLink("Core", core);
                if (mbefore<=mafter) span.log(" contains "+mafter+" top-level formulas. "+array[8]+"ms.\n\n");
                else span.log(" reduced from "+mbefore+" to "+mafter+" top-level formulas. "+array[8]+"ms.\n\n");
            }
            span.flush();
        }
        private Integer getHOLpos(Object trId) {
            Pair<Integer, String> p = holTrPos.get(trId);
            return p != null ? p.a : null;
        }

        private void logHOL(Object[] links, String msg, boolean rememberPos) {
            String trName = links[1].toString();
            String trId = links[2].toString();
            String folTrId = trId; //links[3].toString();
            Integer ord = seenFolTr.get(folTrId);
            if (ord == null) { ord = seenFolTr.size(); seenFolTr.put(trId, ord); }
            span.log("   ");
            span.log(holIndent);
            span.logPaletteBold(trName, ord.intValue());
            span.log(" " + msg + " ");
            formatLinks(links, 4);
            span.log(" ");
            gotoEnd(false);
            if (rememberPos) {
                holTrPos.put(trId, new Pair<Integer, String>(span.getLength(), holIndent));
            }
            gotoEnd(true);
        }
        private void holIndent(Object[] links, String extra) {
            String trName = links[1].toString();
            holIndent = holIndent + trName.replaceAll(".", " ") + extra;
        }
        private void gotoEnd()                                            { gotoEnd(true); }
        private void gotoEnd(boolean newline)                             { if(newline) span.log("\n"); len2=len3=span.getLength(); }
        private void formatLinks(Object[] objs, int startIdx)             { formatLinks(objs, startIdx, objs.length); }
        private void formatLinks(Object[] objs, int startIdx, int endIdx) {
            objs = Arrays.copyOfRange(objs, startIdx, endIdx);
            if (objs.length == 0) return;
            span.log("(");
            boolean fst = true;
            for (Object obj: objs) {
                if (!fst) span.log(", ");
                formatLink((LogLink) obj);
                fst = false;
            }
            span.log(")");
        }
        @SuppressWarnings("unused")
        private void formatLink(Object link)             { formatLink((LogLink)link); }
        private void formatLink(LogLink link)            { span.logLink(link.label, link.href); }
        private void formatLinkAt(int pos, Object link)  { formatLinkAt(pos, (LogLink)link); }
        private void formatLinkAt(int pos, LogLink link) { span.logLink(pos, link.label, link.href); }
    }

    private void cb(String key, HOLTranslation tr, Serializable... objs) {
        List<Serializable> sers = new ArrayList<Serializable>(objs.length + 5);
        String tab = "  "; StringBuilder idn = new StringBuilder("");
        for (int i = 0; i < tr.depth(); i++) idn.append(tab);
        sers.add(key);
        sers.add(idn + "[" + tr.getClass().getSimpleName() + "]");
        String trId = Integer.toString(System.identityHashCode(tr));
        if (tr instanceof HOLTranslationNew.OR)
           trId += "_" + Integer.toString(System.identityHashCode(((HOLTranslationNew.OR) tr).currTr()));
        else if (tr instanceof HOLTranslationNew.Some4All)
           trId += "_" + Integer.toString(System.identityHashCode(((HOLTranslationNew.Some4All) tr).convTr()));
        sers.add(trId);
        sers.add(System.identityHashCode(tr.getCurrentFOLTranslation()));
        for (int i = 0; i < objs.length; i++) sers.add(objs[i]);
        if ("hol-verify-outcome".equals(key) && objs[0] == null && tr instanceof HOLTranslationNew.Some4All) {
            sers.add(((HOLTranslationNew.Some4All)tr).numCandidates());
        }
        cb(sers.toArray(new Serializable[0]));
    }

    private void cb(Serializable... objs) {
        cb.callback(objs);
    }

    /** {@inheritDoc} */
    @Override public void resultCNF(final String filename) { cb("resultCNF", filename); }

    /** {@inheritDoc} */
    @Override public void warning(final ErrorWarning ex) { warn++; cb("warning", ex); }

    /** {@inheritDoc} */
    @Override public void scope(final String msg) { cb("scope", msg); }

    /** {@inheritDoc} */
    @Override public void bound(final String msg)     { cb("bound", msg); }
    @Override public void generatingSolution(Formula f, Bounds bounds) { cb("gensol", link("formula", f), link("bounds", bounds)); }


    public void holLoopStart(HOLTranslation tr, Formula formula, Bounds bounds) { cb("hol-start", tr, link("formula", formula), link("bounds", bounds)); }
    public void holCandidateFound(HOLTranslation tr, Instance candidate)        { cb("hol-candidate", tr, cand(candidate)); }
    public void holVerifyingCandidate(HOLTranslation tr, Instance c, Formula cf, Bounds b) { cb("hol-verify", tr, link("condition", cf), link("pi", b)); }
    public void holCandidateVerified(HOLTranslation tr, Instance candidate)                { cb("hol-verify-outcome", tr, (Serializable)null); }
    public void holCandidateNotVerified(HOLTranslation tr, Instance cnd, Instance cex)     { cb("hol-verify-outcome", tr, cex(cex)); }
    public void holFindingNextCandidate(HOLTranslation tr, Formula inc) { cb("hol-next", tr, link("increment", inc)); }

    public void holSplitStart(HOLTranslation tr, Formula formula)      { cb("hol-split", tr, link("formula", formula)); }
    public void holSplitChoice(HOLTranslation tr, Formula f, Bounds b) { cb("hol-split-choice", tr, link("formula", f), link("bounds", b)); }
    public void holSplitChoiceSAT(HOLTranslation tr, Instance inst)    { cb("hol-split-choice-sat", tr, link("instance", inst)); }
    public void holSplitChoiceUNSAT(HOLTranslation tr)                 { cb("hol-split-choice-unsat", tr); }

    public void holFixpointStart(HOLTranslation tr, Formula formula, Bounds bounds) { cb("hol-fix-start", tr, link("formula", formula), link("bounds", bounds)); }
    public void holFixpointNoSolution(HOLTranslation tr)                            { cb("hol-fix-unsat", tr); }
    public void holFixpointFirstSolution(HOLTranslation tr, Instance candidate)     { cb("hol-fix-first", tr, link("instance", candidate)); }
    public void holFixpointIncrementing(HOLTranslation tr, Formula inc)             { cb("hol-fix-inc", tr, link("formula", inc)); }
    public void holFixpointIncrementingOutcome(HOLTranslation tr, Instance next)    { if (next != null) cb("hol-fix-inc-sat", tr, link("instance", next));
                                                                                      else              cb("hol-fix-inc-unsat", tr); }

    /** {@inheritDoc} */
    @Override public void debug(final String msg) { cb("debug", msg.trim()); }

    /** {@inheritDoc} */
    @Override public void translate(String solver, int bitwidth, int maxseq, int skolemDepth, int symmetry) {
        lastTime = System.currentTimeMillis();
        cb("translate", "Solver="+solver+" Bitwidth="+bitwidth+" MaxSeq="+maxseq
        + (skolemDepth==0?"":" SkolemDepth="+skolemDepth)
        + " Symmetry="+(symmetry>0 ? (""+symmetry) : "OFF")+'\n');
    }

    /** {@inheritDoc} */
    @Override public void solve(final int primaryVars, final int totalVars, final int clauses) {
        minimized=0;
        cb("solve", ""+totalVars+" vars. "+primaryVars+" primary vars. "+clauses+" clauses. "+(System.currentTimeMillis()-lastTime)+"ms.\n");
        lastTime = System.currentTimeMillis();
    }

    /** {@inheritDoc} */
    @Override public void resultSAT(Object command, long solvingTime, Object solution) {
        if (!(solution instanceof A4Solution) || !(command instanceof Command)) return;
        A4Solution sol = (A4Solution)solution;
        Command cmd = (Command)command;
        String formula = recordKodkod ? sol.debugExtractKInput() : "";
        String filename = tempfile+".xml";
        synchronized(SimpleReporter.class) {
            try {
                cb("R3", "   Writing the XML file...");
                if (latestModule!=null) writeXML(this, latestModule, filename, sol, latestKodkodSRC);
            } catch(Throwable ex) {
                cb("bold", "\n" + (ex.toString().trim()) + "\nStackTrace:\n" + (MailBug.dump(ex).trim()) + "\n");
                return;
            }
            latestKodkods.clear();
            latestKodkods.add(sol.toString());
            latestKodkod=sol;
            latestKodkodXML=filename;
        }
        String formulafilename = "";
        if (formula.length()>0 && tempfile!=null) {
            formulafilename = tempfile+".java";
            try { Util.writeAll(formulafilename, formula); formulafilename="CNF: "+formulafilename; } catch(Throwable ex) { formulafilename=""; }
        }
        cb("sat", cmd.check, cmd.expects, filename, formulafilename, System.currentTimeMillis()-lastTime);
    }

    /** {@inheritDoc} */
    @Override public void minimizing(Object command, int before) {
        if (!(command instanceof Command)) return;
        Command cmd = (Command)command;
        minimized = System.currentTimeMillis();
        cb("minimizing", cmd.check, cmd.expects, before, minimized-lastTime);
    }

    /** {@inheritDoc} */
    @Override public void minimized(Object command, int before, int after) { minimizedBefore=before; minimizedAfter=after; }

    /** {@inheritDoc} */
    @Override public void resultUNSAT(Object command, long solvingTime, Object solution) {
        if (!(solution instanceof A4Solution) || !(command instanceof Command)) return;
        A4Solution sol = (A4Solution)solution;
        Command cmd = (Command)command;
        String originalFormula = recordKodkod ? sol.debugExtractKInput() : "";
        String corefilename="", formulafilename="";
        if (originalFormula.length()>0 && tempfile!=null) {
            formulafilename=tempfile+".java";
            try { Util.writeAll(formulafilename, originalFormula); formulafilename="CNF: "+formulafilename; } catch(Throwable ex) { formulafilename=""; }
        }
        Pair<Set<Pos>,Set<Pos>> core = sol.highLevelCore();
        if ((core.a.size()>0 || core.b.size()>0) && tempfile!=null) {
            corefilename=tempfile+".core";
            OutputStream fs=null;
            ObjectOutputStream os=null;
            try {
                fs=new FileOutputStream(corefilename);
                os=new ObjectOutputStream(fs);
                os.writeObject(core);
                os.writeObject(sol.lowLevelCore());
                corefilename="CORE: "+corefilename;
            } catch(Throwable ex) {
                corefilename="";
            } finally {
                Util.close(os);
                Util.close(fs);
            }
        }
        if (minimized==0) cb("unsat", cmd.check, cmd.expects, (System.currentTimeMillis()-lastTime), formulafilename);
        else cb("unsat", cmd.check, cmd.expects, minimized-lastTime, formulafilename, corefilename, minimizedBefore, minimizedAfter, (System.currentTimeMillis()-minimized));
    }

    private Serializable cand(Instance inst)            { return new LogLink("candidate", inst, tempdir, "candidate"); }
    private Serializable cex(Instance inst)             { return new LogLink("counterexample", inst, tempdir, "cex"); }
    private Serializable link(String label, Object obj) { return new LogLink(label, obj, tempdir); }

    private WorkerCallback cb;


    //========== These fields should be set each time we execute a set of commands

    /** Whether we should record Kodkod input/output. */
    private final boolean recordKodkod;

    /** The time that the last action began; we subtract it from System.currentTimeMillis() to determine the elapsed time. */
    private long lastTime=0;

    /** If we performed unsat core minimization, then this is the start of the minimization, else this is 0. */
    private long minimized = 0;

    /** The unsat core size before minimization. */
    private int minimizedBefore;

    /** The unsat core size after minimization. */
    private int minimizedAfter;

    /** The filename where we can write a temporary Java file or Core file. */
    private String tempfile=null;

    /** temp dir */
    private String tempdir = null;

    //========== These fields may be altered as each successful command generates a Kodkod or Metamodel instance

    /** The set of Strings already enumerated for this current solution. */
    private static final Set<String> latestKodkods=new LinkedHashSet<String>();

    /** The A4Solution corresponding to the latest solution generated by Kodkod; this field must be synchronized. */
    private static A4Solution latestKodkod=null;

    /** The root Module corresponding to this.latestKodkod; this field must be synchronized. */
    private static Module latestModule=null;

    /** Latest reporter */
    private static SimpleReporter latestRep=null;

    /** The source code corresponding to the latest solution generated by Kodkod; this field must be synchronized. */
    private static ConstMap<String,String> latestKodkodSRC = null;

    /** The XML filename corresponding to the latest solution generated by Kodkod; this field must be synchronized. */
    private static String latestKodkodXML=null;

    /** The XML filename corresponding to the latest metamodel generated by TranslateAlloyToMetamodel; this field must be synchronized. */
    private static String latestMetamodelXML=null;

    private static int inst_cnt = 0;

    /** Constructor is private.
     * @param simpleTask1 */
    private SimpleReporter(WorkerCallback cb, String tempdir, boolean recordKodkod) { this.tempdir = tempdir; this.cb=cb; this.recordKodkod=recordKodkod; }

    /** Helper method to write out a full XML file. */
    private static void writeXML(IA4Reporter rep, Module mod, String filename, A4Solution sol, Map<String,String> sources) throws Exception {
        sol.writeXML(rep, filename, mod.getAllFunc(), sources);
        if (Util.isDebug()) validate(filename);
    }

    private int warn=0;

    /** Task that performs solution enumeration. */
    static final class SimpleTask2 implements WorkerTask {
        private static final long serialVersionUID = 0;
        public String filename = "";
        public transient WorkerCallback out = null;
        private void cb(Object... objs) throws Exception { out.callback(objs); }
        public void run(WorkerCallback out) throws Exception {
            this.out = out;
            cb("S2", "Enumerating...\n");
            A4Solution sol;
            Module mod;
            synchronized(SimpleReporter.class) {
                if (latestMetamodelXML!=null && latestMetamodelXML.equals(filename))
                   {cb("pop", "You cannot enumerate a metamodel.\n"); return;}
                if (latestKodkodXML==null || !latestKodkodXML.equals(filename))
                   {cb("pop", "You can only enumerate the solutions of the most-recently-solved command."); return;}
                if (latestKodkod==null || latestModule==null || latestKodkodSRC==null)
                   {cb("pop", "Error: the SAT solver that generated the instance has exited,\nso we cannot enumerate unless you re-solve that command.\n"); return;}
                sol=latestKodkod;
                mod=latestModule;
                latestRep.setWorkerCallback(out);
            }
            if (!sol.satisfiable())
                {cb("pop", "Error: This command is unsatisfiable,\nso there are no solutions to enumerate."); return;}
            if (!sol.isIncremental())
                {cb("pop", "Error: This solution was not generated by an incremental SAT solver.\n" +
                "Currently only MiniSat and SAT4J are supported."); return;}
            int tries=0;
            while(true) {
                sol=sol.next();
                if (!sol.satisfiable())
                   {cb("pop", "There are no more satisfying instances.\n\n" +
                   "Note: due to symmetry breaking and other optimizations,\n" +
                   "some equivalent solutions may have been omitted."); return;}
                String toString = sol.toString();
                synchronized(SimpleReporter.class) {
                    if (!latestKodkods.add(toString)) if (tries<100) { tries++; continue; }
                    // The counter is needed to avoid a Kodkod bug where sometimes we might repeat the same solution infinitely number of times; this at least allows the user to keep going
                    writeXML(null, mod, filename, sol, latestKodkodSRC); latestKodkod=sol;
                }
                cb("declare", filename);
                return;
            }
        }
    }

    /** Validate the given filename to see if it is a valid Alloy XML instance file. */
    private static void validate(String filename) throws Exception {
        A4SolutionReader.read(new ArrayList<Sig>(), new XMLNode(new File(filename))).toString();
        StaticInstanceReader.parseInstance(new File(filename));
    }

    public void setWorkerCallback(WorkerCallback wc) {
        this.cb = wc;
    }

    /** Task that perform one command. */
    static final class SimpleTask1 implements WorkerTask {
        private static final long serialVersionUID = 0;
        public A4Options options;
        public String tempdir;
        public boolean bundleWarningNonFatal;
        public int bundleIndex;
        public int resolutionMode;
        public Map<String,String> map;
        public SimpleTask1() { }
        public void cb(WorkerCallback out, Object... objs) throws IOException { out.callback(objs); }
        public void run(WorkerCallback out) throws Exception {
            cb(out, "S2", "Starting the solver...\n\n");
            latestRep = new SimpleReporter(out, this.tempdir, options.recordKodkod);
            Module world = CompUtil.parseEverything_fromFile(latestRep, map, options.originalFilename, resolutionMode);
            List<Sig> sigs = world.getAllReachableSigs();
            ConstList<Command> cmds = world.getAllCommands();
            final int nCmds = cmds.size();
            cb(out, "warnings", bundleWarningNonFatal);
            if (latestRep.warn>0 && !bundleWarningNonFatal) return;
            List<String> result = new ArrayList<String>(nCmds);
            if (bundleIndex==-2) {
                final String outf=tempdir+File.separatorChar+"m.xml";
                cb(out, "S2", "Generating the metamodel...\n");
                PrintWriter of = new PrintWriter(outf, "UTF-8");
                Util.encodeXMLs(of, "\n<alloy builddate=\"", Version.buildDate(), "\">\n\n");
                A4SolutionWriter.writeMetamodel(ConstList.make(sigs), options.originalFilename, of);
                Util.encodeXMLs(of, "\n</alloy>");
                Util.close(of);
                if (Util.isDebug()) validate(outf);
                cb(out, "metamodel", outf);
                synchronized(SimpleReporter.class) { latestMetamodelXML=outf; }
            } else for(int i=0; i<nCmds; i++) if (bundleIndex<0 || i==bundleIndex) {
                // if (Execute All) && (not executing first command) && (using higher-order solver) => must rebuild world because of atomSigs
                if (bundleIndex<0 && i>0 && options.higherOrderSolver) {
                    cb(out, "", "Rebuilding world because higher-order solver is used.\n");
                    world = CompUtil.parseEverything_fromFile(latestRep, map, options.originalFilename, resolutionMode);
                    sigs = world.getAllReachableSigs();
                    cmds = world.getAllCommands();
                }
                synchronized(SimpleReporter.class) { latestModule=world; latestKodkodSRC=ConstMap.make(map); }
                final String tempXML=tempdir+File.separatorChar+i+".cnf.xml";
                final String tempCNF=tempdir+File.separatorChar+i+".cnf";
                final Command cmd=cmds.get(i);
                latestRep.tempfile=tempCNF;
                cb(out, "bold", "Executing \""+cmd+"\"\n");
                TranslateAlloyToKodkod tr = TranslateAlloyToKodkod.translate(latestRep, world.getAllReachableSigs(), cmd, options);
                A4Solution sol = tr.getFrame();
                latestKodkod = sol;
                sol = tr.executeCommandFromBook();
                        //TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), cmd, options);
                if (sol==null) result.add(null);
                else if (sol.satisfiable()) result.add(tempXML);
                else {
                    latestKodkod = null;
                    if (sol.highLevelCore().a.size()>0)
                        result.add(tempCNF+".core");
                    else
                        result.add("");
                }
            }
            (new File(tempdir)).delete(); // In case it was UNSAT, or canceled...
            if (result.size()>1) {
                latestRep.cb("bold", "" + result.size() + " commands were executed. The results are:\n");
                for(int i=0; i<result.size(); i++) {
                    Command r=world.getAllCommands().get(i);
                    if (result.get(i)==null) { latestRep.cb("", "   #"+(i+1)+": Unknown.\n"); continue; }
                    if (result.get(i).endsWith(".xml")) {
                        latestRep.cb("", "   #"+(i+1)+": ");
                        latestRep.cb("link", r.check?"Counterexample found. ":"Instance found. ", "XML: "+result.get(i));
                        latestRep.cb("", r.label+(r.check?" is invalid":" is consistent"));
                        if (r.expects==0) latestRep.cb("", ", contrary to expectation");
                        else if (r.expects==1) latestRep.cb("", ", as expected");
                    } else if (result.get(i).endsWith(".core")) {
                        latestRep.cb("", "   #"+(i+1)+": ");
                        latestRep.cb("link", r.check?"No counterexample found. ":"No instance found. ", "CORE: "+result.get(i));
                        latestRep.cb("", r.label+(r.check?" may be valid":" may be inconsistent"));
                        if (r.expects==1) latestRep.cb("", ", contrary to expectation");
                        else if (r.expects==0) latestRep.cb("", ", as expected");
                    } else {
                        if (r.check) latestRep.cb("", "   #"+(i+1)+": No counterexample found. "+r.label+" may be valid");
                        else latestRep.cb("", "   #"+(i+1)+": No instance found. "+r.label+" may be inconsistent");
                        if (r.expects==1) latestRep.cb("", ", contrary to expectation");
                        else if (r.expects==0) latestRep.cb("", ", as expected");
                    }
                    latestRep.cb("", ".\n");
                }
                latestRep.cb("", "\n");
            }
            if (latestRep.warn>1) latestRep.cb("bold", "Note: There were "+latestRep.warn+" compilation warnings. Please scroll up to see them.\n");
            if (latestRep.warn==1) latestRep.cb("bold", "Note: There was 1 compilation warning. Please scroll up to see it.\n");
        }
    }

    static class LogLink implements Serializable {
        private static final long serialVersionUID = 140775378800533167L;
        transient final Object obj;
        transient final String tempdir;
        final String label;
        final String kind;
        final String href;

        LogLink(String label, Object obj, String tempdir)              { this(label, obj, tempdir, label); }
        LogLink(String label, Object obj, String tempdir, String kind) {
            this.obj = obj;
            this.label = label;
            this.kind = kind;
            this.tempdir = tempdir;
            this.href = _href(latestKodkod);
        }

        private String _href(A4Solution sol) {
            if (obj instanceof Formula) {
                Formula n = (Formula) obj;
                //n = FullNegationPropagator.toNNF(AnnotatedNode.annotate(n)).node();
                return A4Preferences.HOLSaveFormulas.get() ? "MSG: " + PrettyPrinter.print(n, 0) : null;
            } else if (obj instanceof Instance) {
                InstFormat fmt = InstFormat.NOTHING;
                if ("candidate".equals(kind) || "instance".equals(kind)) fmt = A4Preferences.HOLSaveCandidates.get();
                if ("cex".equals(kind)) fmt = A4Preferences.HOLSaveCex.get();
                if (fmt == InstFormat.VIZ && sol != null) return "XML: " + createAndSaveTmpSolution(sol, (Instance)obj);
                else if (fmt == InstFormat.TEXT)          return "MSG: " + ((Instance)obj).toPrettyString();
                else                                      return null;
            } else if (obj instanceof Bounds) { return A4Preferences.HOLSavePI.get() ? "MSG: " + obj.toString() : null;
            } else if (obj == null)           {
                return "MSG: null";
            } else                            { return "MSG: " + obj.toString(); }
        }

        private String createAndSaveTmpSolution(A4Solution sol, Instance inst) {
            String filename = tempdir + File.separatorChar + (kind != null ? kind : "inst") + "_" + (inst_cnt++) + ".xml";
            try {
                sol.writeXMLFor(inst, filename);
                return filename;
            } catch (Err e) {
                e.printStackTrace();
                return null;
            }
        }
    }
}
