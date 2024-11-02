package org.stella.typecheck;

import org.syntax.stella.Absyn.*;
import org.stella.typecheck.VisitTypeCheck;

public class TypeCheck
{
    public static void typecheckProgram(Program program) throws Exception
    {
        //#TODO make this catch throw exception from visitor
        VisitTypeCheck v = new VisitTypeCheck();
        program.accept(v.new ProgramVisitor<>(), null /* initial context information*/);
    }
}
