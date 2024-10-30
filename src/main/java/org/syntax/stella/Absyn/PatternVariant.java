// File generated by the BNF Converter (bnfc 2.9.5).

package org.syntax.stella.Absyn;

public class PatternVariant  extends Pattern {
  public final String stellaident_;
  public final PatternData patterndata_;
  public int line_num, col_num, offset;
  public PatternVariant(String p1, PatternData p2) { stellaident_ = p1; patterndata_ = p2; }

  public <R,A> R accept(org.syntax.stella.Absyn.Pattern.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof org.syntax.stella.Absyn.PatternVariant) {
      org.syntax.stella.Absyn.PatternVariant x = (org.syntax.stella.Absyn.PatternVariant)o;
      return this.stellaident_.equals(x.stellaident_) && this.patterndata_.equals(x.patterndata_);
    }
    return false;
  }

  public int hashCode() {
    return 37*(this.stellaident_.hashCode())+this.patterndata_.hashCode();
  }


}
