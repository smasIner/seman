// File generated by the BNF Converter (bnfc 2.9.5).

package org.syntax.stella.Absyn;

public class PatternInt  extends Pattern {
  public final Integer integer_;
  public int line_num, col_num, offset;
  public PatternInt(Integer p1) { integer_ = p1; }

  public <R,A> R accept(org.syntax.stella.Absyn.Pattern.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof org.syntax.stella.Absyn.PatternInt) {
      org.syntax.stella.Absyn.PatternInt x = (org.syntax.stella.Absyn.PatternInt)o;
      return this.integer_.equals(x.integer_);
    }
    return false;
  }

  public int hashCode() {
    return this.integer_.hashCode();
  }


}
