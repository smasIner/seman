// File generated by the BNF Converter (bnfc 2.9.5).

package org.syntax.stella.Absyn;

public abstract class OptionalTyping implements java.io.Serializable {
  public abstract <R,A> R accept(OptionalTyping.Visitor<R,A> v, A arg);
  public interface Visitor <R,A> {
    public R visit(org.syntax.stella.Absyn.NoTyping p, A arg);
    public R visit(org.syntax.stella.Absyn.SomeTyping p, A arg);

  }

}
