// File generated by the BNF Converter (bnfc 2.9.5).

package org.syntax.stella.Absyn;

public class TypeList  extends Type {
  public final Type type_;
  public int line_num, col_num, offset;
  public TypeList(Type p1) { type_ = p1; }

  public <R,A> R accept(org.syntax.stella.Absyn.Type.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof org.syntax.stella.Absyn.TypeList) {
      org.syntax.stella.Absyn.TypeList x = (org.syntax.stella.Absyn.TypeList)o;
      return this.type_.equals(x.type_);
    }
    return false;
  }

  public int hashCode() {
    return this.type_.hashCode();
  }


}
