// File generated by the BNF Converter (bnfc 2.9.5).

package org.syntax.stella.Absyn;

public abstract class Type implements java.io.Serializable {
  public abstract <R,A> R accept(Type.Visitor<R,A> v, A arg);
  public interface Visitor <R,A> {
    public R visit(org.syntax.stella.Absyn.TypeAuto p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeFun p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeForAll p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeRec p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeSum p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeTuple p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeRecord p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeVariant p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeList p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeBool p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeNat p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeUnit p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeTop p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeBottom p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeRef p, A arg);
    public R visit(org.syntax.stella.Absyn.TypeVar p, A arg);

  }

}
