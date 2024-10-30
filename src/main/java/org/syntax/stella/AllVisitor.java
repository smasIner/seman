// File generated by the BNF Converter (bnfc 2.9.5).

package org.syntax.stella;

/** All Visitor */

public interface AllVisitor<R,A> extends
  org.syntax.stella.Absyn.Program.Visitor<R,A>,
  org.syntax.stella.Absyn.LanguageDecl.Visitor<R,A>,
  org.syntax.stella.Absyn.Extension.Visitor<R,A>,
  org.syntax.stella.Absyn.Decl.Visitor<R,A>,
  org.syntax.stella.Absyn.LocalDecl.Visitor<R,A>,
  org.syntax.stella.Absyn.Annotation.Visitor<R,A>,
  org.syntax.stella.Absyn.ParamDecl.Visitor<R,A>,
  org.syntax.stella.Absyn.ReturnType.Visitor<R,A>,
  org.syntax.stella.Absyn.ThrowType.Visitor<R,A>,
  org.syntax.stella.Absyn.Type.Visitor<R,A>,
  org.syntax.stella.Absyn.MatchCase.Visitor<R,A>,
  org.syntax.stella.Absyn.OptionalTyping.Visitor<R,A>,
  org.syntax.stella.Absyn.PatternData.Visitor<R,A>,
  org.syntax.stella.Absyn.ExprData.Visitor<R,A>,
  org.syntax.stella.Absyn.Pattern.Visitor<R,A>,
  org.syntax.stella.Absyn.LabelledPattern.Visitor<R,A>,
  org.syntax.stella.Absyn.Binding.Visitor<R,A>,
  org.syntax.stella.Absyn.Expr.Visitor<R,A>,
  org.syntax.stella.Absyn.PatternBinding.Visitor<R,A>,
  org.syntax.stella.Absyn.VariantFieldType.Visitor<R,A>,
  org.syntax.stella.Absyn.RecordFieldType.Visitor<R,A>,
  org.syntax.stella.Absyn.Typing.Visitor<R,A>
{}
