package edu.mit.csail.sdg.alloy4compiler.ast;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.alloy4.Pos;

public class ExprFix extends Expr {
    public final Op op;
    public final Expr formula;
    public final Expr cond;

    private ExprFix(Pos pos, Pos closingBracket, Op op, Type type, Expr formula, Expr cond, boolean ambiguous, long weight, JoinableList<Err> errs) {
        super(pos, closingBracket, ambiguous, type, 0, weight, errs);
        this.op = op;
        this.formula = formula;
        this.cond = cond;
    }

    @Override
    public void toString(StringBuilder out, int indent) {
        out.append("fix ").append(formula).append(" ").append(op).append(" ").append(cond);
    }

    @Override
    public <T> T accept(VisitReturn<T> visitor) throws Err {
        return visitor.visit(this);
    }

    @Override
    public Expr resolve(Type t, Collection<ErrorWarning> warnings) {
        return this;
    }

    @Override
    public int getDepth() {
        return Math.max(formula.getDepth(), cond.getDepth()) + 1;
    }

    @Override
    public String getHTML() {
        return "<b>fix</b>&nbsp;" + formula.getHTML() + "&nbsp;<b>" + op + "</b>&nbsp;" + cond.getHTML();
    }

    @Override
    public List<? extends Browsable> getSubnodes() {
        ArrayList<Browsable> ans = new ArrayList<Browsable>();
        ans.add(make(formula.pos, formula.closingBracket, "<b>formula</b>", formula));
        ans.add(make(formula.pos, formula.closingBracket, "<b>condition</b>", cond));
        return ans;
    }

    //=============================================================================================================//

    /** This class contains all possible quantification operators. */
    public enum Op {
       /** fix formula while formula  */  WHILE("while"),
       /** fix formula until formula  */  UNTIL("until");

       /** The constructor. */
       private Op(String label) { this.label = label; }

       /** The human readable label for this operator. */
       private final String label;

       /** Constructs a quantification expression with "this" as the operator.
        *
        * @param pos - the position of the "quantifier" in the source file (or null if unknown)
        * @param closingBracket - the position of the "closing bracket" in the source file (or null if unknown)
        * @param decls - the list of variable declarations (each variable must be over a set or relation)
        * @param sub - the body of the expression
        */
       public final Expr make(Pos pos, Pos closingBracket, Expr formula, Expr cond) {
          JoinableList<Err> err = emptyListOfErrors;
          boolean a = formula.ambiguous || cond.ambiguous;
          long w = formula.weight + cond.weight;
          return new ExprFix(pos, closingBracket, this, Type.FORMULA, formula, cond, a, w, err);
       }

       /** Returns the human readable label for this operator */
       @Override public final String toString() { return label; }
    }
}
