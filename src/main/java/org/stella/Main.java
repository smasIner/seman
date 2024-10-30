package org.stella;

import java.io.*;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.*;
import java.util.*;

import org.stella.typecheck.TypeCheck;
import org.syntax.stella.*;
import org.syntax.stella.Absyn.*;
import org.stella.eval.*;

public class Main
{
    stellaLexer l;
    stellaParser p;

    public Main(String[] args)
    {
        try
        {
            Reader input;
            if (args.length == 0) input = new InputStreamReader(System.in);
            else input = new FileReader(args[0]);
            l = new stellaLexer(new ANTLRInputStream(input));
            l.addErrorListener(new BNFCErrorListener());
        }
        catch(IOException e)
        {
            System.err.println("Error: File not found: " + args[0]);
            System.exit(1);
        }
        p = new stellaParser(new CommonTokenStream(l));
        p.addErrorListener(new BNFCErrorListener());
    }

    public Program parse() throws Exception
    {
        /* The default parser is the first-defined entry point. */
        /* Other options are: */
    /* languageDecl, extension, listExtensionName, listExtension, decl,
       listDecl, localDecl, listLocalDecl, annotation, listAnnotation,
       paramDecl, listParamDecl, returnType, throwType, expr, listExpr,
       matchCase, listMatchCase, pattern, listPattern, labelledPattern,
       listLabelledPattern, binding, listBinding, type, listType,
       fieldType, listFieldType, typing */
        stellaParser.Start_ProgramContext pc = p.start_Program();
        Program ast = pc.result;
        return ast;
    }

    public static void main(String args[]) throws Exception
    {
        Main t = new Main(args);
        try
        {
            Program ast = t.parse();
            TypeCheck.typecheckProgram(ast);

            if (args.length > 0) {
                stellaLexer l;
                stellaParser p;
                l = new stellaLexer(new ANTLRInputStream(new InputStreamReader(System.in)));
                l.addErrorListener(new BNFCErrorListener());
                p = new stellaParser(new CommonTokenStream(l));
                p.addErrorListener(new BNFCErrorListener());
                stellaParser.Start_ExprContext ec = p.start_Expr();
                Expr inputExpr = ec.result;
                Expr resultExpr = Eval.evalMainWith(ast, inputExpr);

                System.out.println(PrettyPrinter.print(resultExpr));
            }
        }
        catch(TestError e)
        {
            System.err.println("At line " + e.line + ", column " + e.column + " :");
            System.err.println("     " + e.getMessage());
            System.exit(1);
        }
    }
}

class TestError extends RuntimeException
{
    int line;
    int column;
    public TestError(String msg, int l, int c)
    {
        super(msg);
        line = l;
        column = c;
    }
}

class BNFCErrorListener implements ANTLRErrorListener
{
    @Override
    public void syntaxError(Recognizer<?, ?> recognizer, Object o, int i, int i1, String s, RecognitionException e)
    {
        throw new TestError(s,i,i1);
    }
    @Override
    public void reportAmbiguity(Parser parser, DFA dfa, int i, int i1, boolean b, BitSet bitSet, ATNConfigSet atnConfigSet)
    {
        throw new TestError("Ambiguity at",i,i1);
    }
    @Override
    public void reportAttemptingFullContext(Parser parser, DFA dfa, int i, int i1, BitSet bitSet, ATNConfigSet atnConfigSet)
    {
    }
    @Override
    public void reportContextSensitivity(Parser parser, DFA dfa, int i, int i1, int i2, ATNConfigSet atnConfigSet)
    {
    }
}

