package org.stella.typecheck;

import org.syntax.stella.Absyn.*;
import org.syntax.stella.PrettyPrinter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * TypeChecker is a singleton class responsible for type checking Stella programs.
 * It verifies that all expressions in a program have valid types according to
 * the language's type system rules.
 */
public class TypeChecker {
    /** Global context storing function declarations and their types */
    private static final Env ENV = new Env();

    /**
     * Checks if a list of match cases is exhaustive for a sum type.
     * A match is exhaustive if it includes both inl and inr patterns.
     *
     * @param cases The list of match cases
     * @return true if the match is exhaustive, false otherwise
     */
    private static boolean arePatternMatchesExhaustive(List<MatchCase> cases) {
        boolean inl = false;
        boolean inr = false;
        for (MatchCase matchCase : cases) {
            if (matchCase instanceof AMatchCase aMatchCase) {
                if (aMatchCase.pattern_ instanceof PatternInr) {
                    inr = true;
                } else if (aMatchCase.pattern_ instanceof PatternInl) {
                    inl = true;
                }
            }
        }

        return inl && inr;
    }

    /**
     * Checks if a type is a subtype of another type.
     * This implements the subtyping relation of the language's type system.
     *
     * @param subType The potential subtype
     * @param superType The potential supertype
     * @return true if subType is a subtype of superType, false otherwise
     */
    private static boolean isSubtypeOf(Type subType, Type superType) {
        // Bottom is a subtype of everything
        if (subType instanceof TypeBottom) {
            return true;
        }

        // Top is a supertype of everything
        if (superType instanceof TypeTop) {
            return true;
        }

        // Handle null types safely
        if (subType == null || superType == null) {
            return false;
        }

        // Check if the types have the same class (same type constructor)
        // Fixed the potential null pointer issue by using Objects.equals
        if (!Objects.equals(subType.getClass(), superType.getClass())) {
            return false;
        }

        // Check for structural equality #TODO may be inline
        if (areTypesEqual(subType, superType)) {
            return true;
        }

        // Handle specific subtyping rules for different type constructors
        if (subType instanceof TypeRecord) {
            return isRecordSubtypeOf((TypeRecord) subType, (TypeRecord) superType);
        } else if (subType instanceof TypeFun) {
            return isFunctionSubtypeOf((TypeFun) subType, (TypeFun) superType);
        } else {
            return false;
        }
    }

    /**
     * Checks if a function type is a subtype of another function type.
     * A function type A -> B is a subtype of C -> D if C is a subtype of A (contravariant)
     * and B is a subtype of D (covariant).
     *
     * @param subType The potential subtype function
     * @param superType The potential supertype function
     * @return true if subType is a subtype of superType, false otherwise
     */
    private static boolean isFunctionSubtypeOf(TypeFun subType, TypeFun superType) {
        return (isSubtypeOf(subType.type_, superType.type_) &&
                isSubtypeOf(superType.listtype_.get(0), subType.listtype_.get(0)));
    }

    /**
     * Checks if a record type is a subtype of another record type.
     * A record type is a subtype of another if it has at least all the fields of the supertype
     * with the same types.
     *
     * @param subType The potential subtype record
     * @param superType The potential supertype record
     * @return true if subType is a subtype of superType, false otherwise
     */
    private static boolean isRecordSubtypeOf(TypeRecord subType, TypeRecord superType) {
        Map<String, Type> superRecordFieldTypes = new HashMap<>();

        // Extract all fields from the supertype
        for (RecordFieldType recordFieldType : superType.listrecordfieldtype_) {
            if (recordFieldType instanceof ARecordFieldType aRecordFieldType) {
                superRecordFieldTypes.put(aRecordFieldType.stellaident_, aRecordFieldType.type_);
            }
        }

        // Check that the subtype has all fields from the supertype with compatible types
        for (RecordFieldType recordFieldType : subType.listrecordfieldtype_) {
            if (recordFieldType instanceof ARecordFieldType aRecordFieldType) {
                String subFieldKey = aRecordFieldType.stellaident_;
                Type subFieldValue = aRecordFieldType.type_;

                if (superRecordFieldTypes.containsKey(subFieldKey)) {
                    if (!superRecordFieldTypes.get(subFieldKey).equals(subFieldValue)) {
                        return false;
                    }
                    superRecordFieldTypes.remove(subFieldKey);
                }
            }
        }

        // All fields in the supertype must be present in the subtype
        return superRecordFieldTypes.isEmpty();
    }

    /**
     * Checks if two types are equal, handling null values safely.
     *
     * @param type1 The first type
     * @param type2 The second type
     * @return true if the types are equal, false otherwise
     */
    private static boolean areTypesEqual(Type type1, Type type2) {
        if (type1 instanceof TypeSum typeSum1 && type2 instanceof TypeSum typeSum2) {
            return (areTypesEqual(typeSum1.type_1, typeSum2.type_1) && areTypesEqual(typeSum1.type_2, typeSum2.type_2));
        }

        if (type2 instanceof TypeSum) {
            return type1 == null;
        }

        if (type1 instanceof TypeSum) {
            return type2 == null;
        }
        //#TODO Possible redundant
        if (type1 == null || type2 == null) {
            return true;
        }

        return type1.equals(type2);
    }

    /**
     * Finds the most general type that is a supertype of all types in the list.
     * This is used for type inference in conditional expressions and pattern matching.
     *
     * @param listTypes The list of types to find a common supertype for
     * @return The most general common supertype, or null if none exists
     */
    private static Type findMostGeneralSupertype(List<Type> listTypes) {
        Type mostGeneralType = listTypes.get(0);

        for (int i = 1; i < listTypes.size(); i++) {
            Type type = listTypes.get(i);
            if (!isSubtypeOf(type, mostGeneralType)) {
                if (isSubtypeOf(mostGeneralType, type)) {
                    mostGeneralType = type;
                } else {
                    return null;
                }
            }
        }

        return mostGeneralType;
    }

    /**
     * Creates a function type from a parameter type to a return type.
     *
     * @param paramType The parameter type
     * @param returnType The return type
     * @return The function type
     */
    private static TypeFun createFunctionType(Type paramType, Type returnType) {
        ListType paramListType = new ListType();
        paramListType.add(paramType);

        return new TypeFun(paramListType, returnType);
    }

    /**
     * Creates a tuple type from a list of expressions.
     *
     * @param tupleExpressions The list of expressions
     * @param context The typing context
     * @return The tuple type
     * @throws TypeError If the expressions contain type errors
     */
    private static TypeTuple createTupleType(List<Expr> tupleExpressions, Context context) throws TypeError {
        ListType exprListType = new ListType();

        for (Expr expr : tupleExpressions) {
            exprListType.add(inferExpressionType(expr, null, context));
        }

        return new TypeTuple(exprListType);
    }

    /**
     * Creates a record type from a list of bindings.
     *
     * @param recordBindings The list of bindings
     * @param context The typing context
     * @return The record type
     * @throws TypeError If the bindings contain type errors
     */
    private static TypeRecord createRecordType(List<Binding> recordBindings, Context context) throws TypeError {
        ListRecordFieldType recordListRecordFieldType = new ListRecordFieldType();

        for (Binding binding : recordBindings) {
            if (binding instanceof ABinding aBinding) {
                recordListRecordFieldType.add(
                        new ARecordFieldType(
                                aBinding.stellaident_,
                                inferExpressionType(aBinding.expr_, null, context)
                        )
                );
            }
        }

        return new TypeRecord(recordListRecordFieldType);
    }

    /**
     * Validates that a parameter type is compatible with the expected type.
     *
     * @param paramType The parameter type
     * @param expectedType The expected type
     * @throws TypeError If the parameter type is not compatible with the expected type
     */
    private static void validateParameterType(Type paramType, Type expectedType) throws TypeError {
        if (!isSubtypeOf(paramType, expectedType)) {
            throw new TypeError(
                    "Parameter type " + PrettyPrinter.print(paramType) + " is not compatible with " +
                            "declared type " + PrettyPrinter.print(expectedType)
            );
        }
    }

    /**
     * Gets the type of a record field.
     *
     * @param dotRecord The record field access expression
     * @param fieldName The name of the field
     * @param recordType The record type
     * @return The type of the field
     * @throws TypeError If the field doesn't exist in the record
     */
    private static Type getRecordFieldType(DotRecord dotRecord, String fieldName, TypeRecord recordType) throws TypeError {
        List<RecordFieldType> recordListRecordFieldType = recordType.listrecordfieldtype_;

        for (RecordFieldType recordFieldType : recordListRecordFieldType) {
            if (recordFieldType instanceof ARecordFieldType aRecordFieldType) {
                if (aRecordFieldType.stellaident_.equals(fieldName)) {
                    return aRecordFieldType.type_;
                }
            }
        }

        throw new TypeError(
                "Field '" + fieldName + "' does not exist in record of type " +
                        PrettyPrinter.print(recordType) + " in expression " + PrettyPrinter.print(dotRecord)
        );
    }

    /**
     * Extracts variable bindings from a list of pattern bindings.
     *
     * @param listPatternBinding The list of pattern bindings
     * @param context The typing context
     * @return A map from variable names to their types
     * @throws TypeError If the bindings contain type errors
     */
    private static Map<String, Type> extractPatternBindings(
            List<PatternBinding> listPatternBinding,
            Context context) throws TypeError {
        Map<String, Type> mapPatternBinding = new HashMap<>();

        for (PatternBinding patternBinding : listPatternBinding) {
            if (patternBinding instanceof APatternBinding aPatternBinding) {
                Pattern pattern = aPatternBinding.pattern_;
                if (pattern instanceof PatternVar patternVar) {
                    mapPatternBinding.put(patternVar.stellaident_,
                            inferExpressionType(aPatternBinding.expr_, null, context));
                }
            }
        }

        return mapPatternBinding;
    }

    /**
     * Extracts the variable and its type from a pattern.
     *
     * @param pattern The pattern
     * @param currentType The type being matched against
     * @return A pair of the variable name and its type
     * @throws TypeError If the pattern is invalid for the given type
     */
    private static Pair<String, Type> extractPatternVariable(Pattern pattern, Type currentType) throws TypeError {
        if (currentType instanceof TypeSum typeSum) {
            if (pattern instanceof PatternInl) {
                return extractPatternVariable(((PatternInl) pattern).pattern_, typeSum.type_1);
            } else if (pattern instanceof PatternInr) {
                return extractPatternVariable(((PatternInr) pattern).pattern_, typeSum.type_2);
            } else if (pattern instanceof PatternVar) {
                return new Pair<>(((PatternVar) pattern).stellaident_, currentType);
            } else {
                return new Pair<>("", null);
            }
        } else {
            if (pattern instanceof PatternVar) {
                return new Pair<>(((PatternVar) pattern).stellaident_, currentType);
            } else {
                throw new TypeError(
                        "Cannot pattern match on type " + PrettyPrinter.print(currentType) +
                                " with pattern " + PrettyPrinter.print(pattern)
                );
            }
        }
    }

    /**
     * Extracts parameter declaration information into a map of parameter names to types.
     *
     * @param paramDecl The parameter declaration to extract
     * @param context The typing context
     * @return A map from parameter names to their types
     * @throws TypeError If the parameter declaration contains invalid types
     */
    private static Map<String, Type> extractParameterDeclaration(ParamDecl paramDecl, Context context) throws TypeError {
        if (paramDecl instanceof AParamDecl aParamDecl) {
            if (isValidType(aParamDecl.type_, context)) {
                Map<String, Type> result = new HashMap<>();
                result.put(aParamDecl.stellaident_, aParamDecl.type_);
                return result;
            }
        }
        return new HashMap<>();
    }

    /**
     * Validates that the type of an accessed item matches the expected type.
     *
     * @param expr The access expression
     * @param typeAccessed The type of the accessed item
     * @param expectedType The expected type, or null if no specific type is expected
     * @return The type of the accessed item
     * @throws TypeError If the accessed item doesn't match the expected type
     */
    private static Type validateAccessedItemType(Expr expr, Type typeAccessed, Type expectedType) throws TypeError {
        if (expectedType == null) {
            return typeAccessed;
        }

        if (!isSubtypeOf(typeAccessed, expectedType)) {
            throw new TypeError(
                    "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                            " but found " + PrettyPrinter.print(typeAccessed) +
                            " in expression " + PrettyPrinter.print(expr)
            );
        }

        return typeAccessed;
    }

    /**
     * Type checks numeric operators (arithmetic and comparison).
     * Ensures that both operands are of type Nat and returns the appropriate result type.
     *
     * @param operatorType The type of operator: "comp" for comparison, or other for arithmetic
     * @param leftExpr The left operand expression
     * @param rightExpr The right operand expression
     * @param expectedType The expected result type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the operation result
     * @throws TypeError If the operands are not of type Nat or the result doesn't match the expected type
     */
    private static Type inferNumericOperatorType(
            String operatorType,
            Expr leftExpr,
            Expr rightExpr,
            Type expectedType,
            Context context) throws TypeError {

        // Check that both operands are of type Nat
        inferExpressionType(leftExpr, new TypeNat(), context);
        inferExpressionType(rightExpr, new TypeNat(), context);

        // Determine the result type based on the operator type
        Type resultType = operatorType.equals("comp") ? new TypeBool() : new TypeNat();

        // If no expected type is provided, return the inferred result type
        if (expectedType == null) {
            return resultType;
        }

        // Check that the result type matches the expected type
        if (operatorType.equals("comp")) {
            if (!(expectedType instanceof TypeBool)) {
                throw new TypeError(
                        "Type mismatch in comparison operation: expected " + PrettyPrinter.print(expectedType) +
                                " but comparison operations return Bool"
                );
            }
        } else {
            if (!(expectedType instanceof TypeNat)) {
                throw new TypeError(
                        "Type mismatch in arithmetic operation: expected " + PrettyPrinter.print(expectedType) +
                                " but arithmetic operations return Nat"
                );
            }
        }

        return resultType;
    }

    /**
     * Infers the type of a natural number function expression.
     * Checks that the argument is a natural number.
     *
     * @param expr The expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The natural number type
     * @throws TypeError If the argument is not a natural number or the expected type is not a natural number
     */
    private static Type inferNaturalNumberFunctionType(Expr expr, Type expectedType, Context context) throws TypeError {
        if (expectedType == null) {
            return inferExpressionType(expr, new TypeNat(), context);
        }

        if (!(expectedType instanceof TypeNat)) {
            throw new TypeError(
                    "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                            " but natural number functions return Nat"
            );
        }

        return inferExpressionType(expr, new TypeNat(), context);
    }

    /**
     * Replaces a type variable with a concrete type throughout a type expression.
     * This is used for type instantiation in generic functions and type abstractions.
     *
     * @param originalType The type in which to perform the substitution
     * @param varIdent The name of the type variable to replace
     * @param varType The type to substitute for the variable
     * @param depth The current depth of substitution (for handling nested quantifiers)
     * @param swappedBefore Whether a variable has been swapped before (to avoid infinite recursion)
     * @return The type with the variable replaced
     * @throws TypeError If the substitution cannot be performed
     */
    private static Type substituteTypeVariable(
            Type originalType,
            String varIdent,
            Type varType,
            int depth,
            boolean swappedBefore) throws TypeError {

        if (originalType instanceof TypeFun typeFun) {
            return createFunctionType(
                    substituteTypeVariable(typeFun.listtype_.get(0), varIdent, varType, depth, swappedBefore),
                    substituteTypeVariable(typeFun.type_, varIdent, varType, depth, swappedBefore)
            );
        } else if (originalType instanceof TypeSum typeSum) {
            return new TypeSum(
                    substituteTypeVariable(typeSum.type_1, varIdent, varType, depth, swappedBefore),
                    substituteTypeVariable(typeSum.type_2, varIdent, varType, depth, swappedBefore)
            );
        } else if (originalType instanceof TypeTuple typeTuple) {
            ListType newListType = new ListType();
            for (Type element : typeTuple.listtype_) {
                newListType.add(substituteTypeVariable(element, varIdent, varType, depth, swappedBefore));
            }
            return new TypeTuple(newListType);
        } else if (originalType instanceof TypeRecord typeRecord) {
            ListRecordFieldType newListRecordFieldType = new ListRecordFieldType();
            for (RecordFieldType element : typeRecord.listrecordfieldtype_) {
                if (element instanceof ARecordFieldType aRecordFieldType) {
                    newListRecordFieldType.add(new ARecordFieldType(
                            aRecordFieldType.stellaident_,
                            substituteTypeVariable(aRecordFieldType.type_, varIdent, varType, depth, swappedBefore)
                    ));
                }
            }
            return new TypeRecord(newListRecordFieldType);
        } else if (originalType instanceof TypeRef typeRef) {
            return new TypeRef(substituteTypeVariable(typeRef.type_, varIdent, varType, depth, swappedBefore));
        } else if (originalType instanceof TypeVar typeVar) {
            if (typeVar.stellaident_.equals(varIdent)) {
                return varType;
            } else {
                return originalType;
            }
        } else if (originalType instanceof TypeForAll typeForAll) {
            // Handle quantified types carefully to avoid variable capture
            if (typeForAll.liststellaident_.contains(varIdent) && swappedBefore) {
                return originalType;
            } else if (varType instanceof TypeVar && typeForAll.liststellaident_.contains(((TypeVar) varType).stellaident_)) {
                String newVarIdent = ((TypeVar) varType).stellaident_ + depth;
                String oldVarIdent = ((TypeVar) varType).stellaident_;
                List<String> oldListStellaIdent = typeForAll.liststellaident_;

                ListStellaIdent newListStellaIdent = new ListStellaIdent();
                for (String it : oldListStellaIdent) {
                    newListStellaIdent.add(it.equals(oldVarIdent) ? newVarIdent : it);
                }

                TypeForAll ret = new TypeForAll(
                        newListStellaIdent,
                        substituteTypeVariable(
                                typeForAll.type_,
                                oldVarIdent,
                                new TypeVar(newVarIdent),
                                depth + 1,
                                true
                        )
                );
                ret = new TypeForAll(
                        ret.liststellaident_,
                        substituteTypeVariable(ret.type_, varIdent, varType, depth + 1, true)
                );
                return ret;
            } else {
                return new TypeForAll(
                        typeForAll.liststellaident_,
                        substituteTypeVariable(typeForAll.type_, varIdent, varType, depth, true)
                );
            }
        } else if (originalType instanceof TypeBool) {
            return new TypeBool();
        } else if (originalType instanceof TypeNat) {
            return new TypeNat();
        } else if (originalType instanceof TypeUnit) {
            return new TypeUnit();
        } else if (originalType instanceof TypeTop) {
            return new TypeTop();
        } else if (originalType instanceof TypeBottom) {
            return new TypeBottom();
        } else {
            return null;
        }
    }

    /**
     * Convenience method for substituting a type variable with a concrete type.
     *
     * @param originalType The type in which to perform the substitution
     * @param varIdent The name of the type variable to replace
     * @param varType The type to substitute for the variable
     * @param depth The current depth of substitution
     * @return The type with the variable replaced
     * @throws TypeError If the substitution cannot be performed
     */
    private static Type substituteTypeVariable(Type originalType, String varIdent, Type varType, int depth) throws TypeError {
        return substituteTypeVariable(originalType, varIdent, varType, depth, false);
    }

    /**
     * Convenience method for substituting a type variable with a concrete type.
     *
     * @param originalType The type in which to perform the substitution
     * @param varIdent The name of the type variable to replace
     * @param varType The type to substitute for the variable
     * @return The type with the variable replaced
     * @throws TypeError If the substitution cannot be performed
     */
    private static Type substituteTypeVariable(Type originalType, String varIdent, Type varType) throws TypeError {
        return substituteTypeVariable(originalType, varIdent, varType, 0, false);
    }

    /**
     * Checks if a given type is valid within the current context.
     * A type is valid if it's well-formed according to the language's type system.
     *
     * @param type The type to check
     * @param context The typing context
     * @return true if the type is valid, false otherwise
     * @throws TypeError If the type contains references to undefined type variables
     */
    private static boolean isValidType(Type type, Context context) throws TypeError {
        if (type instanceof TypeFun typeFun) {
            return isValidType(typeFun.listtype_.get(0), context) && isValidType(typeFun.type_, context);
        } else if (type instanceof TypeSum typeSum) {
            return isValidType(typeSum.type_1, context) && isValidType(typeSum.type_2, context);
        } else if (type instanceof TypeTuple typeTuple) {
            for (Type element : typeTuple.listtype_) {
                if (!isValidType(element, context)) {
                    return false;
                }
            }
            return true;
        } else if (type instanceof TypeRecord typeRecord) {
            for (RecordFieldType element : typeRecord.listrecordfieldtype_) {
                if (element instanceof ARecordFieldType) {
                    if (!isValidType(((ARecordFieldType) element).type_, context)) {
                        return false;
                    }
                } else {
                    return false;
                }
            }
            return true;
        } else if (type instanceof TypeRef) {
            return isValidType(((TypeRef) type).type_, context);
        } else if (type instanceof TypeVar typeVar) {
            if (context.hasType(typeVar.stellaident_)) {
                return true;
            } else {
                throw new TypeError("Undefined type variable: " + typeVar.stellaident_);
            }
        } else if (type instanceof TypeForAll typeForAll) {
            context.appendTypes(typeForAll.liststellaident_);
            return isValidType(typeForAll.type_, context);
        } else if (type instanceof TypeBool ||
                type instanceof TypeNat ||
                type instanceof TypeUnit ||
                type instanceof TypeTop ||
                type instanceof TypeBottom) {
            return true; //#TODO read about those types
        } else {
            return false;
        }
    }

    /**
     * Entry point for type checking a Stella program.
     * Processes all declarations in the program and verifies their type correctness.
     *
     * @param program The Stella program to type check
     * @throws TypeError If any type error is detected during type checking
     */
    public static void typeCheckProgram(Program program) throws TypeError {
        if (program instanceof AProgram aProgram) {
            for (Decl declaration : aProgram.listdecl_) {
                if (declaration instanceof DeclFunGeneric) {
                    validateGenericFunctionDeclaration((DeclFunGeneric) declaration);
                } else if (declaration instanceof DeclFun) {
                    validateFunctionDeclaration((DeclFun) declaration);
                }
            }
        }
    }

    /**
     * Validates a regular function declaration by checking its return type,
     * parameters, and body expression.
     *
     * @param declaration The function declaration to validate
     * @throws TypeError If the function declaration contains type errors
     */
    private static void validateFunctionDeclaration(DeclFun declaration) throws TypeError {
        validateFunction(
                declaration.returntype_,
                declaration.listparamdecl_,
                declaration.stellaident_,
                declaration.expr_,
                new Context()
        );
    }

    /**
     * Validates a generic function declaration by checking its return type,
     * parameters, and body expression within a context that includes the generic type parameters.
     *
     * @param declaration The generic function declaration to validate
     * @throws TypeError If the function declaration contains type errors
     */
    private static void validateGenericFunctionDeclaration(DeclFunGeneric declaration) throws TypeError {
        ArrayList<String> genericTypeContext = new ArrayList<>(declaration.liststellaident_);

        Context context = new Context(genericTypeContext);
        ENV.appendFunctionGenerics(declaration.stellaident_, genericTypeContext);

        validateFunction(
                declaration.returntype_,
                declaration.listparamdecl_,
                declaration.stellaident_,
                declaration.expr_,
                context
        );
    }

    /**
     * Validates a function by checking that its body expression has the expected return type
     * and that all parameter types are valid.
     *
     * @param returnType The declared return type of the function
     * @param paramList The list of parameter declarations
     * @param functionName The name of the function
     * @param bodyExpression The body expression of the function
     * @param context The typing context for validation
     * @throws TypeError If the function contains type errors
     */
    private static void validateFunction(
            ReturnType returnType,
            List<ParamDecl> paramList,
            String functionName,
            Expr bodyExpression,
            Context context) throws TypeError {

        Map<String, Type> variableContext = new HashMap<>();
        Type expectedReturnType;

        // Extract the expected return type
        if (returnType instanceof SomeReturnType) {
            expectedReturnType = ((SomeReturnType) returnType).type_;
        } else {
            throw new TypeError("Function '" + functionName + "' must specify a return type");
        }

        // Validate that the return type is a valid type
        if (!isValidType(expectedReturnType, context)) {
            throw new TypeError("Invalid return type for function '" + functionName + "'");
        }

        // Process each parameter declaration
        for (ParamDecl paramDecl : paramList) {
            Map<String, Type> params = extractParameterDeclaration(paramDecl, context);
            variableContext.putAll(params);
            // #TODO why do we use equal?
            Type paramType = null;
            for (Type value : params.values()) {
                paramType = value;
            }

            // Construct and register the function type
            Type functionType = createFunctionType(paramType, expectedReturnType);
            ENV.appendFunction(functionName, functionType);
        }

        // Add the parameters to the context
        context.appendVariables(variableContext);

        // Type check the function body
        Type actualReturnType = inferExpressionType(bodyExpression, expectedReturnType, context);

        // Verify that the actual return type is a subtype of the expected return type
        if (!isSubtypeOf(actualReturnType, expectedReturnType)) {
            throw new TypeError(
                    "Return type mismatch in function '" + functionName + "': expected " +
                            PrettyPrinter.print(expectedReturnType) + " but found " +
                            PrettyPrinter.print(actualReturnType) + " in expression " +
                            PrettyPrinter.print(bodyExpression)
            );
        }
    }

    /**
     * Infers the type of an expression and checks if it matches the expected type.
     * This is the main type checking function that dispatches to specific type checking
     * methods based on the expression type.
     *
     * @param expression The expression to type check
     * @param expectedType The expected type of the expression, or null if no specific type is expected
     * @param context The typing context
     * @return The inferred type of the expression
     * @throws TypeError If the expression cannot be typed or doesn't match the expected type
     */
    private static Type inferExpressionType(Expr expression, Type expectedType, Context context) throws TypeError {
        if (expression instanceof Abstraction) {
            return inferLambdaAbstractionType((Abstraction) expression, expectedType, context);
        } else if (expression instanceof TypeAbstraction) {
            return inferTypeAbstractionType((TypeAbstraction) expression, context);
        } else if (expression instanceof Application) {
            return inferFunctionApplicationType((Application) expression, expectedType, context);
        } else if (expression instanceof TypeApplication) {
            return inferTypeApplicationType((TypeApplication) expression, context);
        } else if (expression instanceof If) {
            return inferConditionalType((If) expression, expectedType, context);
        } else if (expression instanceof org.syntax.stella.Absyn.Var) {
            return inferVariableType((org.syntax.stella.Absyn.Var) expression, expectedType, context);
        } else if (expression instanceof org.syntax.stella.Absyn.Tuple) {
            return inferTupleType((org.syntax.stella.Absyn.Tuple) expression, expectedType, context);
        } else if (expression instanceof org.syntax.stella.Absyn.DotTuple) {
            return inferTupleAccessType((org.syntax.stella.Absyn.DotTuple) expression, expectedType, context);
        } else if (expression instanceof org.syntax.stella.Absyn.Record) {
            return inferRecordType((org.syntax.stella.Absyn.Record) expression, expectedType, context);
        } else if (expression instanceof org.syntax.stella.Absyn.DotRecord) {
            return inferRecordAccessType((org.syntax.stella.Absyn.DotRecord) expression, expectedType, context);
        } else if (expression instanceof ConstTrue || expression instanceof ConstFalse) {
            return inferBooleanLiteralType(expectedType);
        } else if (expression instanceof ConstInt) {
            return inferIntegerLiteralType(expectedType);
        } else if (expression instanceof ConstUnit) {
            return inferUnitLiteralType(expectedType);
        } else if (expression instanceof Succ) {
            return inferSuccessorType((Succ) expression, expectedType, context);
        } else if (expression instanceof Pred) {
            return inferPredecessorType((Pred) expression, expectedType, context);
        } else if (expression instanceof Match) {
            return inferPatternMatchType((Match) expression, expectedType, context);
        } else if (expression instanceof Inl) {
            return inferSumLeftType((Inl) expression, expectedType, context);
        } else if (expression instanceof Inr) {
            return inferSumRightType((Inr) expression, expectedType, context);
        } else if (expression instanceof NatRec) {
            return inferNaturalRecursionType((NatRec) expression, expectedType, context);
        } else if (expression instanceof IsZero) {
            return inferIsZeroType((IsZero) expression, expectedType, context);
        } else if (expression instanceof Sequence) {
            return inferSequenceType((Sequence) expression, expectedType, context);
        } else if (expression instanceof Panic) {
            return inferPanicType((Panic) expression, expectedType);
        } else if (expression instanceof Ref) {
            return inferReferenceType((Ref) expression, expectedType, context);
        } else if (expression instanceof Deref) {
            return inferDereferenceType((Deref) expression, expectedType, context);
        } else if (expression instanceof Assign) {
            return inferAssignmentType((Assign) expression, expectedType, context);
        } else if (expression instanceof Let) {
            return inferLetBindingType((Let) expression, expectedType, context);
        } else if (expression instanceof TypeCast) {
            return inferTypeCastType((TypeCast) expression, expectedType, context);
        } else if (expression instanceof Add) {
            return inferAdditionType((Add) expression, expectedType, context);
        } else if (expression instanceof Subtract) {
            return inferSubtractionType((Subtract) expression, expectedType, context);
        } else if (expression instanceof Multiply) {
            return inferMultiplicationType((Multiply) expression, expectedType, context);
        } else if (expression instanceof Divide) {
            return inferDivisionType((Divide) expression, expectedType, context);
        } else if (expression instanceof LessThan) {
            return inferLessThanType((LessThan) expression, expectedType, context);
        } else if (expression instanceof LessThanOrEqual) {
            return inferLessThanOrEqualType((LessThanOrEqual) expression, expectedType, context);
        } else if (expression instanceof GreaterThan) {
            return inferGreaterThanType((GreaterThan) expression, expectedType, context);
        } else if (expression instanceof GreaterThanOrEqual) {
            return inferGreaterThanOrEqualType((GreaterThanOrEqual) expression, expectedType, context);
        } else if (expression instanceof Equal) {
            return inferEqualityType((Equal) expression, expectedType, context);
        } else if (expression instanceof NotEqual) {
            return inferInequalityType((NotEqual) expression, expectedType, context);
        } else {
            return null;
        }
    }

    /**
     * Infers the type of a boolean literal expression.
     *
     * @param expectedType The expected type, or null if no specific type is expected
     * @return The boolean type
     * @throws TypeError If the expected type is not boolean
     */
    private static Type inferBooleanLiteralType(Type expectedType) throws TypeError {
        if (expectedType == null) {
            return new TypeBool();
        }

        if (!(expectedType instanceof TypeBool)) {
            throw new TypeError(
                    "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                            " but boolean literals have type Bool"
            );
        }

        return new TypeBool();
    }

    /**
     * Infers the type of an integer literal expression.
     *
     * @param expectedType The expected type, or null if no specific type is expected
     * @return The natural number type
     * @throws TypeError If the expected type is not a natural number
     */
    private static Type inferIntegerLiteralType(Type expectedType) throws TypeError {
        if (expectedType == null) {
            return new TypeNat();
        }

        if (!(expectedType instanceof TypeNat)) {
            throw new TypeError(
                    "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                            " but integer literals have type Nat"
            );
        }

        return new TypeNat();
    }

    /**
     * Infers the type of a unit literal expression.
     *
     * @param expectedType The expected type, or null if no specific type is expected
     * @return The unit type
     * @throws TypeError If the expected type is not unit
     */
    private static Type inferUnitLiteralType(Type expectedType) throws TypeError {
        if (expectedType == null) {
            return new TypeUnit();
        }

        if (!(expectedType instanceof TypeUnit)) {
            throw new TypeError(
                    "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                            " but unit literals have type Unit"
            );
        }

        return new TypeUnit();
    }

    /**
     * Infers the type of a successor expression.
     *
     * @param succExpr The successor expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The natural number type
     * @throws TypeError If the argument is not a natural number or the expected type is not a natural number
     */
    private static Type inferSuccessorType(Succ succExpr, Type expectedType, Context context) throws TypeError {
        return inferNaturalNumberFunctionType(succExpr.expr_, expectedType, context);
    }

    /**
     * Infers the type of a predecessor expression.
     *
     * @param predExpr The predecessor expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The natural number type
     * @throws TypeError If the argument is not a natural number or the expected type is not a natural number
     */
    private static Type inferPredecessorType(Pred predExpr, Type expectedType, Context context) throws TypeError {
        return inferNaturalNumberFunctionType(predExpr.expr_, expectedType, context);
    }

    /**
     * Infers the type of an isZero expression.
     * Checks that the argument is a natural number.
     *
     * @param isZeroExpr The isZero expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The boolean type
     * @throws TypeError If the argument is not a natural number or the expected type is not boolean
     */
    private static Type inferIsZeroType(IsZero isZeroExpr, Type expectedType, Context context) throws TypeError {
        Expr isZeroContent = isZeroExpr.expr_;
        inferExpressionType(isZeroContent, new TypeNat(), context);

        if (expectedType == null) {
            return new TypeBool();
        }

        if (!(expectedType instanceof TypeBool)) {
            throw new TypeError(
                    "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                            " but isZero expressions return Bool"
            );
        }

        return new TypeBool();
    }

    /**
     * Infers the type of a conditional expression.
     * Checks that the condition is a boolean and the branches have compatible types.
     *
     * @param ifExpr The conditional expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The common supertype of the branch types
     * @throws TypeError If the condition is not a boolean or the branches have incompatible types
     */
    private static Type inferConditionalType(If ifExpr, Type expectedType, Context context) throws TypeError {
        Expr condition = ifExpr.expr_1;
        Expr firstBranch = ifExpr.expr_2;
        Expr secondBranch = ifExpr.expr_3;

        inferExpressionType(condition, new TypeBool(), context);

        Type firstBranchType = inferExpressionType(firstBranch, expectedType, context);
        Type secondBranchType = inferExpressionType(secondBranch, expectedType, context);

        List<Type> branchTypes = new ArrayList<>();
        branchTypes.add(firstBranchType);
        branchTypes.add(secondBranchType);

        Type mostGeneralType = findMostGeneralSupertype(branchTypes);
        if (mostGeneralType == null) {
            throw new TypeError(
                    "Incompatible branch types in if statement: " +
                            PrettyPrinter.print(firstBranchType) + " and " +
                            PrettyPrinter.print(secondBranchType)
            );
        }

        return mostGeneralType;
    }

    /**
     * Infers the type of a variable reference.
     * Looks up the variable in the context or global function declarations.
     *
     * @param variable The variable reference
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the variable
     * @throws TypeError If the variable is not found or has an incompatible type
     */
    private static Type inferVariableType(Var variable, Type expectedType, Context context) throws TypeError {
        String variableName = variable.stellaident_;

        Type variableType;
        if (context.hasVariable(variableName)) {
            variableType = context.getVariableType(variableName);
        } else {
            Type funType = ENV.getFunctionType(variableName);
            List<String> funGenerics = ENV.getFunctionGenerics(variableName);

            if (funGenerics.isEmpty()) {
                variableType = funType;
            } else {
                ListStellaIdent listStellaIdent = new ListStellaIdent();
                listStellaIdent.addAll(funGenerics);
                variableType = new TypeForAll(listStellaIdent, funType);
            }
        }

        if (expectedType == null) {
            return variableType;
        }

        if (!isSubtypeOf(variableType, expectedType)) {
            throw new TypeError(
                    "Type mismatch for variable '" + variableName + "': expected " +
                            PrettyPrinter.print(expectedType) + " but found " +
                            PrettyPrinter.print(variableType)
            );
        }

        return variableType;
    }

    /**
     * Infers the type of a tuple expression.
     * Constructs a tuple type from the types of the tuple elements.
     *
     * @param tuple The tuple expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The tuple type
     * @throws TypeError If the tuple doesn't match the expected type
     */
    private static Type inferTupleType(Tuple tuple, Type expectedType, Context context) throws TypeError {
        Type typeOfTuple = createTupleType(tuple.listexpr_, context);

        if (expectedType == null) {
            return typeOfTuple;
        }

        if (expectedType instanceof TypeTuple) {
            if (!isSubtypeOf(typeOfTuple, expectedType)) {
                throw new TypeError(
                        "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                                " but found " + PrettyPrinter.print(typeOfTuple) +
                                " in tuple expression " + PrettyPrinter.print(tuple)
                );
            } else {
                return typeOfTuple;
            }
        } else {
            throw new TypeError(
                    "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                            " but found a tuple type"
            );
        }
    }

    /**
     * Infers the type of a tuple element access expression.
     * Checks that the expression is a tuple and the index is valid.
     *
     * @param dotTuple The tuple element access expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the accessed element
     * @throws TypeError If the expression is not a tuple or the index is invalid
     */
    private static Type inferTupleAccessType(DotTuple dotTuple, Type expectedType, Context context) throws TypeError {
        Type exprType = inferExpressionType(dotTuple.expr_, null, context);

        if (exprType instanceof TypeTuple typeTuple) {
            int dotTupleIndex = dotTuple.integer_;

            if (dotTupleIndex == 0) {
                throw new TypeError("Invalid tuple access: index 0 is out of bounds (tuple indices start at 1)");
            }

            int tupleSize = typeTuple.listtype_.size();

            if (dotTupleIndex > tupleSize) {
                throw new TypeError(
                        "Invalid tuple access: index " + dotTupleIndex + " is out of bounds for tuple of size " +
                                tupleSize + " in expression " + PrettyPrinter.print(dotTuple.expr_)
                );
            }

            Type typeAccessed = typeTuple.listtype_.get(dotTupleIndex - 1);

            return validateAccessedItemType(dotTuple, typeAccessed, expectedType);
        } else {
            throw new TypeError(
                    "Type error: cannot access tuple element on non-tuple expression of type " +
                            PrettyPrinter.print(exprType)
            );
        }
    }

    /**
     * Infers the type of a record expression.
     * Constructs a record type from the types of the record fields.
     *
     * @param record The record expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The record type
     * @throws TypeError If the record doesn't match the expected type
     */
    private static Type inferRecordType(org.syntax.stella.Absyn.Record record, Type expectedType, Context context) throws TypeError {
        Type typeOfRecord = createRecordType(record.listbinding_, context);

        if (expectedType == null) {
            return typeOfRecord;
        }

        if (expectedType instanceof TypeRecord) {
            if (!isSubtypeOf(typeOfRecord, expectedType)) {
                throw new TypeError(
                        "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                                " but found " + PrettyPrinter.print(typeOfRecord) +
                                " in record expression " + PrettyPrinter.print(record)
                );
            } else {
                return typeOfRecord;
            }
        } else {
            throw new TypeError(
                    "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                            " but found a record type"
            );
        }
    }

    /**
     * Infers the type of a record field access expression.
     * Checks that the expression is a record and the field exists.
     *
     * @param dotRecord The record field access expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the accessed field
     * @throws TypeError If the expression is not a record or the field doesn't exist
     */
    private static Type inferRecordAccessType(DotRecord dotRecord, Type expectedType, Context context) throws TypeError {
        Type exprType = inferExpressionType(dotRecord.expr_, null, context);

        if (exprType instanceof TypeRecord typeRecord) {
            String dotRecordFieldAccessed = dotRecord.stellaident_;

            Type typeAccessed = getRecordFieldType(dotRecord, dotRecordFieldAccessed, typeRecord);

            return validateAccessedItemType(dotRecord, typeAccessed, expectedType);
        } else {
            throw new TypeError(
                    "Type error: cannot access record field on non-record expression of type " +
                            PrettyPrinter.print(exprType)
            );
        }
    }

    /**
     * Infers the type of a sum left injection expression.
     * Constructs a sum type with the left component being the type of the expression.
     *
     * @param expr The sum left injection expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The sum type
     * @throws TypeError If the expression doesn't match the expected type
     */
    private static Type inferSumLeftType(Inl expr, Type expectedType, Context context) throws TypeError {
        Type innerExprType = inferExpressionType(expr.expr_, null, context);

        if (expectedType == null) {
            return new TypeSum(innerExprType, null);
        }

        if (expectedType instanceof TypeSum typeSum) {
            if (typeSum.type_1 == null) {
                return new TypeSum(innerExprType, typeSum.type_2);
            }

            if (!isSubtypeOf(innerExprType, typeSum.type_1)) {
                throw new TypeError(
                        "Type mismatch in left injection: expected " + PrettyPrinter.print(typeSum.type_1) +
                                " but found " + PrettyPrinter.print(innerExprType) +
                                " in sum type " + PrettyPrinter.print(expectedType)
                );
            }

            return expectedType;
        } else {
            throw new TypeError(
                    "Type mismatch: expected sum type but found " + PrettyPrinter.print(expectedType)
            );
        }
    }

    /**
     * Infers the type of a sum right injection expression.
     * Constructs a sum type with the right component being the type of the expression.
     *
     * @param expr The sum right injection expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The sum type
     * @throws TypeError If the expression doesn't match the expected type
     */
    private static Type inferSumRightType(Inr expr, Type expectedType, Context context) throws TypeError {
        Type innerExprType = inferExpressionType(expr.expr_, null, context);

        if (expectedType == null) {
            return new TypeSum(null, innerExprType);
        }

        if (expectedType instanceof TypeSum typeSum) {
            if (typeSum.type_2 == null) {
                return new TypeSum(typeSum.type_1, innerExprType);
            }

            if (!isSubtypeOf(innerExprType, typeSum.type_2)) {
                throw new TypeError(
                        "Type mismatch in right injection: expected " + PrettyPrinter.print(typeSum.type_2) +
                                " but found " + PrettyPrinter.print(innerExprType) +
                                " in sum type " + PrettyPrinter.print(expectedType)
                );
            }

            return expectedType;
        } else {
            throw new TypeError(
                    "Type mismatch: expected sum type but found " + PrettyPrinter.print(expectedType)
            );
        }
    }

    /**
     * Infers the type of a pattern match expression.
     * Checks that the scrutinee is a sum type and the patterns are exhaustive.
     *
     * @param match The pattern match expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The common supertype of all branch types
     * @throws TypeError If the scrutinee is not a sum type, the patterns are not exhaustive,
     *                   or the branches have incompatible types
     */
    private static Type inferPatternMatchType(Match match, Type expectedType, Context context) throws TypeError {
        Type exprType = inferExpressionType(match.expr_, null, context);

        if (exprType instanceof TypeSum typeSum) {
            int numExpr = match.listmatchcase_.size();

            if (numExpr == 0) {
                throw new TypeError("Empty pattern match is not allowed in expression " + PrettyPrinter.print(match));
            }

            if (!arePatternMatchesExhaustive(match.listmatchcase_)) {
                throw new TypeError("Pattern match is not exhaustive in expression " + PrettyPrinter.print(match));
            }

            List<Type> branchTypes = new ArrayList<>();
            for (MatchCase matchCase : match.listmatchcase_) {
                if (matchCase instanceof AMatchCase aMatchCase) {
                    Pair<String, Type> varTypeTuple = extractPatternVariable(aMatchCase.pattern_, typeSum);
                    Map<String, Type> caseVariableContext = new HashMap<>();
                    caseVariableContext.put(varTypeTuple.first, varTypeTuple.second);

                    Context innerContext = new Context(context);
                    innerContext.appendVariables(caseVariableContext);

                    Type branchType = inferExpressionType(aMatchCase.expr_, expectedType, innerContext);
                    branchTypes.add(branchType);
                }
            }

            Type mostGeneralType = findMostGeneralSupertype(branchTypes);
            if (mostGeneralType == null) {
                throw new TypeError(
                        "Incompatible branch types in match expression: " +
                                PrettyPrinter.print(branchTypes.get(0)) + " and " +
                                PrettyPrinter.print(branchTypes.get(1))
                );
            }

            return mostGeneralType;
        } else if (exprType instanceof TypeVariant) {
            List<Type> branchTypes = new ArrayList<>();

            for (MatchCase matchCase : match.listmatchcase_) {
                if (matchCase instanceof AMatchCase aMatchCase) {
                    // Extract pattern variable and type
                    Pair<String, Type> varTypeTuple = extractPatternVariable(aMatchCase.pattern_, exprType);
                    Map<String, Type> caseVariableContext = new HashMap<>();

                    if (varTypeTuple.first != null && !varTypeTuple.first.isEmpty()) {
                        caseVariableContext.put(varTypeTuple.first, varTypeTuple.second);
                    }

                    Context innerContext = new Context(context);
                    innerContext.appendVariables(caseVariableContext);

                    Type branchType = inferExpressionType(aMatchCase.expr_, expectedType, innerContext);
                    branchTypes.add(branchType);
                }
            }

            // Find common supertype of all branch types
            if (!branchTypes.isEmpty()) {
                Type mostGeneralType = findMostGeneralSupertype(branchTypes);
                if (mostGeneralType == null) {
                    throw new TypeError(
                            "Incompatible branch types in match expression: " +
                                    branchTypes.stream().map(PrettyPrinter::print).collect(java.util.stream.Collectors.joining(", "))
                    );
                }

                // Check against expected type if provided
                if (expectedType != null && !isSubtypeOf(mostGeneralType, expectedType)) {
                    throw new TypeError(
                            "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                                    " but match expression has type " + PrettyPrinter.print(mostGeneralType)
                    );
                }

                return mostGeneralType;
            }
        }

        // If we can't determine the type, return the expected type or throw an error
        if (expectedType != null) {
            return expectedType;
        }
        throw new TypeError(
                "Cannot determine type of match expression on non-variant, non-sum type: " +
                        PrettyPrinter.print(exprType)
        );
    }

    /**
     * Infers the type of a natural number recursion expression.
     * Checks that the first argument is a Nat, the second argument has some type T,
     * and the third argument has type Nat -> (T -> T).
     *
     * @param natRec The natural number recursion expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the second argument
     * @throws TypeError If the arguments have incompatible types
     */
    private static Type inferNaturalRecursionType(NatRec natRec, Type expectedType, Context context) throws TypeError {
        inferExpressionType(natRec.expr_1, new TypeNat(), context);
        Type secondExprType = inferExpressionType(natRec.expr_2, null, context);
        Type thirdExprType = inferExpressionType(natRec.expr_3, null, context);

        Type innerReturnType = createFunctionType(secondExprType, secondExprType);
        Type thirdExprExpectedType = createFunctionType(new TypeNat(), innerReturnType);

        if (!isSubtypeOf(thirdExprType, thirdExprExpectedType)) {
            throw new TypeError(
                    "Type mismatch in Nat::rec: third argument must have type " +
                            "fn(Nat) -> (fn(" + PrettyPrinter.print(secondExprType) + ") -> " +
                            PrettyPrinter.print(secondExprType) + ") but found " +
                            PrettyPrinter.print(thirdExprType)
            );
        }

        if (expectedType != null && !isSubtypeOf(secondExprType, expectedType)) {
            throw new TypeError(
                    "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                            " but Nat::rec returns " + PrettyPrinter.print(secondExprType)
            );
        }

        return secondExprType;
    }

    /**
     * Infers the type of a lambda abstraction expression.
     * Creates a function type from the parameter types to the body type.
     *
     * @param abstraction The lambda abstraction expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param outerContext The outer typing context
     * @return The function type
     * @throws TypeError If the body contains type errors or the function doesn't match the expected type
     */
    private static Type inferLambdaAbstractionType(Abstraction abstraction, Type expectedType, Context outerContext) throws TypeError {
        Map<String, Type> innerVariableContext = new HashMap<>();

        for (ParamDecl paramDecl : abstraction.listparamdecl_) {
            innerVariableContext.putAll(extractParameterDeclaration(paramDecl, outerContext));
        }

        Context innerContext = new Context(outerContext);
        innerContext.appendVariables(innerVariableContext);

        Expr innerExpr = abstraction.expr_;
        AParamDecl firstParam = (AParamDecl) abstraction.listparamdecl_.get(0);

        if (expectedType == null) {
            Type returnType = inferExpressionType(innerExpr, null, innerContext);
            return createFunctionType(firstParam.type_, returnType);
        }

        Type actualReturnType;

        if (expectedType instanceof TypeFun typeFun) {
            validateParameterType(firstParam.type_, typeFun.listtype_.get(0));
            actualReturnType = inferExpressionType(innerExpr, typeFun.type_, innerContext);

            if (!isSubtypeOf(actualReturnType, typeFun.type_)) {
                throw new TypeError(
                        "Return type mismatch in lambda: expected " + PrettyPrinter.print(typeFun.type_) +
                                " but found " + PrettyPrinter.print(actualReturnType)
                );
            }
        } else {
            throw new TypeError(
                    "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                            " but found a function type for abstraction " + PrettyPrinter.print(abstraction)
            );
        }

        return createFunctionType(firstParam.type_, actualReturnType);
    }

    /**
     * Infers the type of a type abstraction expression.
     * Creates a polymorphic type by quantifying over the type variables.
     *
     * @param typeAbstraction The type abstraction expression
     * @param outerContext The outer typing context
     * @return The polymorphic type
     * @throws TypeError If the body contains type errors
     */
    private static Type inferTypeAbstractionType(TypeAbstraction typeAbstraction, Context outerContext) throws TypeError {
        List<String> genericTypes = typeAbstraction.liststellaident_;

        // Create a new context with the generic type variables
        Context innerContext = new Context(outerContext);
        innerContext.appendTypes(genericTypes);

        // Infer the type of the body expression
        Type bodyType = inferExpressionType(typeAbstraction.expr_, null, innerContext);

        // Create a proper ListStellaIdent with the generic type variables
        ListStellaIdent typeParams = new ListStellaIdent();
        typeParams.addAll(genericTypes);

        // Return a forall type with the correct type parameters
        return new TypeForAll(typeParams, bodyType);
    }

    /**
     * Infers the type of a function application expression.
     * Checks that the function has a function type and the argument has a compatible type.
     *
     * @param expr The function application expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The return type of the function
     * @throws TypeError If the expression is not a function or the argument has an incompatible type
     */
    private static Type inferFunctionApplicationType(Application expr, Type expectedType, Context context) throws TypeError {
        Type functionType = inferExpressionType(expr.expr_, null, context);

        if (functionType instanceof TypeFun typeFun) {
            Type firstArgExpectedType = typeFun.listtype_.get(0);
            Type applicationReturnType = typeFun.type_;

            inferExpressionType(expr.listexpr_.get(0), firstArgExpectedType, context);

            if (expectedType == null) {
                return applicationReturnType;
            }

            if (!isSubtypeOf(applicationReturnType, expectedType)) {
                throw new TypeError(
                        "Type mismatch in function application: expected " + PrettyPrinter.print(expectedType) +
                                " but function returns " + PrettyPrinter.print(applicationReturnType) +
                                " in expression " + PrettyPrinter.print(expr)
                );
            }

            return applicationReturnType;
        } else {
            throw new TypeError(
                    "Cannot apply argument " + PrettyPrinter.print(expr.listexpr_.get(0)) +
                            " to non-function expression " + PrettyPrinter.print(expr.expr_)
            );
        }
    }

    /**
     * Infers the type of a type application expression.
     * Instantiates a polymorphic type by substituting type arguments for type variables.
     *
     * @param expr The type application expression
     * @param context The typing context
     * @return The instantiated type
     * @throws TypeError If the expression is not of a polymorphic type or the number of type arguments is incorrect
     */
    private static Type inferTypeApplicationType(TypeApplication expr, Context context) throws TypeError {
        Type exprType = inferExpressionType(expr.expr_, null, context);

        if (exprType instanceof TypeForAll typeForAll) {
            List<Type> appliedTypes = expr.listtype_;
            List<String> typeVars = typeForAll.liststellaident_;

            if (appliedTypes.size() != typeVars.size()) {
                throw new TypeError(
                        "Type parameter count mismatch: expected " + typeVars.size() +
                                " type parameters but found " + appliedTypes.size() +
                                " in type application " + PrettyPrinter.print(expr)
                );
            }

            TypeForAll returnType = typeForAll;
            for (int i = 0; i < typeVars.size(); i++) {
                String typeVar = typeVars.get(i);
                Type appliedType = appliedTypes.get(i);
                returnType = (TypeForAll) substituteTypeVariable(returnType, typeVar, appliedType);
            }
            return returnType.type_;
        }

        return null;
    }

    /**
     * Infers the type of a sequence expression.
     * The first expression must have type Unit, and the type of the sequence is the type of the second expression.
     *
     * @param expr The sequence expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the second expression
     * @throws TypeError If the first expression is not of type Unit or the result doesn't match the expected type
     */
    private static Type inferSequenceType(Sequence expr, Type expectedType, Context context) throws TypeError {
        // The first expression must have type Unit
        inferExpressionType(expr.expr_1, new TypeUnit(), context);

        // The type of the sequence is the type of the second expression
        Type secondBranchReturnType = inferExpressionType(expr.expr_2, null, context);

        if (expectedType == null) {
            return secondBranchReturnType;
        }

        if (!isSubtypeOf(secondBranchReturnType, expectedType)) {
            throw new TypeError(
                    "Type mismatch in sequence expression: expected " + PrettyPrinter.print(expectedType) +
                            " but found " + PrettyPrinter.print(secondBranchReturnType) +
                            " in expression " + PrettyPrinter.print(expr.expr_2)
            );
        }

        return secondBranchReturnType;
    }

    /**
     * Infers the type of a panic expression.
     * A panic expression can have any expected type.
     *
     * @param expr The panic expression
     * @param expectedType The expected type, which must not be null
     * @return The expected type
     * @throws TypeError If no expected type is provided
     */
    private static Type inferPanicType(Panic expr, Type expectedType) throws TypeError {
        if (expectedType == null) {
            throw new TypeError("Cannot infer type for panic expression without an expected type");
        }

        return expectedType;
    }

    /**
     * Infers the type of a reference creation expression.
     * Creates a reference type containing the type of the expression.
     *
     * @param expr The reference creation expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The reference type
     * @throws TypeError If the result doesn't match the expected type
     */
    private static Type inferReferenceType(Ref expr, Type expectedType, Context context) throws TypeError {
        Type innerExprType = inferExpressionType(expr.expr_, null, context);
        Type refType = new TypeRef(innerExprType);

        if (expectedType == null) {
            return refType;
        }

        if (!isSubtypeOf(refType, expectedType)) {
            throw new TypeError(
                    "Type mismatch in reference creation: expected " + PrettyPrinter.print(expectedType) +
                            " but found " + PrettyPrinter.print(refType) +
                            " in expression " + PrettyPrinter.print(expr)
            );
        }

        return refType;
    }

    /**
     * Infers the type of a dereference expression.
     * Checks that the expression is a reference and returns its content type.
     *
     * @param expr The dereference expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the dereferenced value
     * @throws TypeError If the expression is not a reference or the result doesn't match the expected type
     */
    private static Type inferDereferenceType(Deref expr, Type expectedType, Context context) throws TypeError {
        Type innerExprType = inferExpressionType(expr.expr_, null, context);

        if (innerExprType instanceof TypeRef typeRef) {
            Type dereferencedType = typeRef.type_;

            if (expectedType == null) {
                return dereferencedType;
            }

            if (!isSubtypeOf(dereferencedType, expectedType)) {
                throw new TypeError(
                        "Type mismatch in dereference: expected " + PrettyPrinter.print(expectedType) +
                                " but found " + PrettyPrinter.print(dereferencedType) +
                                " in expression " + PrettyPrinter.print(expr)
                );
            }

            return dereferencedType;
        } else {
            throw new TypeError(
                    "Cannot dereference non-reference expression " + PrettyPrinter.print(expr.expr_) +
                            " of type " + PrettyPrinter.print(innerExprType)
            );
        }
    }

    /**
     * Infers the type of an assignment expression.
     * Checks that the left-hand side is a reference and the right-hand side has a compatible type.
     *
     * @param expr The assignment expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the assignment expression (Unit)
     * @throws TypeError If the left-hand side is not a reference or the types are incompatible
     */
    private static Type inferAssignmentType(Assign expr, Type expectedType, Context context) throws TypeError {
        Type leftExpressionType = inferExpressionType(expr.expr_1, null, context);
        Type rightExpressionType = inferExpressionType(expr.expr_2, null, context);

        if (leftExpressionType instanceof TypeRef typeRef) {
            if (!isSubtypeOf(rightExpressionType, typeRef.type_)) {
                throw new TypeError(
                        "Type mismatch in assignment: expected " + PrettyPrinter.print(typeRef.type_) +
                                " but found " + PrettyPrinter.print(rightExpressionType) +
                                " in expression " + PrettyPrinter.print(expr)
                );
            }

            if (expectedType == null) {
                return new TypeUnit();
            }

            if (!(expectedType instanceof TypeUnit)) {
                throw new TypeError(
                        "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                                " but assignment expressions return Unit"
                );
            }

            return new TypeUnit();
        } else {
            throw new TypeError("Cannot assign to non-reference expression " + PrettyPrinter.print(expr.expr_1));
        }
    }

    /**
     * Infers the type of a let binding expression.
     * Creates a new context with the bound variables and their types.
     *
     * @param letExpr The let binding expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param outerContext The outer typing context
     * @return The type of the let expression (the type of its body)
     * @throws TypeError If the bindings or body contain type errors
     */
    private static Type inferLetBindingType(Let letExpr, Type expectedType, Context outerContext) throws TypeError {
        // Extract variable bindings from the pattern bindings
        Map<String, Type> innerVariableContext = new HashMap<>(extractPatternBindings(letExpr.listpatternbinding_, outerContext));

        // Create a new context with the bound variables
        Context innerContext = new Context(outerContext);
        innerContext.appendVariables(innerVariableContext);

        // Type check the body expression in the new context
        return inferExpressionType(letExpr.expr_, expectedType, innerContext);
    }

    /**
     * Infers the type of a type cast expression.
     * Checks that the cast is valid (the expression type is a subtype of the target type).
     *
     * @param castExpr The type cast expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the cast expression (the target type)
     * @throws TypeError If the cast is invalid or the result doesn't match the expected type
     */
    private static Type inferTypeCastType(TypeCast castExpr, Type expectedType, Context context) throws TypeError {
        Type exprType = inferExpressionType(castExpr.expr_, null, context);

        if (!isSubtypeOf(exprType, castExpr.type_)) {
            throw new TypeError(
                    "Invalid type cast: cannot cast from " + PrettyPrinter.print(exprType) +
                            " to " + PrettyPrinter.print(castExpr.type_)
            );
        }

        if (expectedType == null) {
            return castExpr.type_;
        }

        if (!isSubtypeOf(castExpr.type_, expectedType)) {
            throw new TypeError(
                    "Type mismatch: expected " + PrettyPrinter.print(expectedType) +
                            " but cast expression has type " + PrettyPrinter.print(castExpr.type_)
            );
        }

        return castExpr.type_;
    }

    /**
     * Infers the type of an addition expression (+).
     *
     * @param addExpr The addition expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the addition expression (Nat)
     * @throws TypeError If the operands are not of type Nat or the result doesn't match the expected type
     */
    private static Type inferAdditionType(Add addExpr, Type expectedType, Context context) throws TypeError {
        return inferNumericOperatorType("add", addExpr.expr_1, addExpr.expr_2, expectedType, context);
    }

    /**
     * Infers the type of a subtraction expression (-).
     *
     * @param subtractExpr The subtraction expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the subtraction expression (Nat)
     * @throws TypeError If the operands are not of type Nat or the result doesn't match the expected type
     */
    private static Type inferSubtractionType(Subtract subtractExpr, Type expectedType, Context context) throws TypeError {
        return inferNumericOperatorType("sub", subtractExpr.expr_1, subtractExpr.expr_2, expectedType, context);
    }

    /**
     * Infers the type of a multiplication expression (*).
     *
     * @param multiplyExpr The multiplication expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the multiplication expression (Nat)
     * @throws TypeError If the operands are not of type Nat or the result doesn't match the expected type
     */
    private static Type inferMultiplicationType(Multiply multiplyExpr, Type expectedType, Context context) throws TypeError {
        return inferNumericOperatorType("mul", multiplyExpr.expr_1, multiplyExpr.expr_2, expectedType, context);
    }

    /**
     * Infers the type of a division expression (/).
     *
     * @param divideExpr The division expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the division expression (Nat)
     * @throws TypeError If the operands are not of type Nat or the result doesn't match the expected type
     */
    private static Type inferDivisionType(Divide divideExpr, Type expectedType, Context context) throws TypeError {
        return inferNumericOperatorType("div", divideExpr.expr_1, divideExpr.expr_2, expectedType, context);
    }

    /**
     * Infers the type of a less-than expression (<).
     *
     * @param compExpr The less-than expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the less-than expression (Bool)
     * @throws TypeError If the operands are not of type Nat or the result doesn't match the expected type
     */
    private static Type inferLessThanType(LessThan compExpr, Type expectedType, Context context) throws TypeError {
        return inferNumericOperatorType("comp", compExpr.expr_1, compExpr.expr_2, expectedType, context);
    }

    /**
     * Infers the type of a less-than-or-equal expression (<=).
     *
     * @param compExpr The less-than-or-equal expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the less-than-or-equal expression (Bool)
     * @throws TypeError If the operands are not of type Nat or the result doesn't match the expected type
     */
    private static Type inferLessThanOrEqualType(LessThanOrEqual compExpr, Type expectedType, Context context) throws TypeError {
        return inferNumericOperatorType("comp", compExpr.expr_1, compExpr.expr_2, expectedType, context);
    }

    /**
     * Infers the type of a greater-than expression (>).
     *
     * @param compExpr The greater-than expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the greater-than expression (Bool)
     * @throws TypeError If the operands are not of type Nat or the result doesn't match the expected type
     */
    private static Type inferGreaterThanType(GreaterThan compExpr, Type expectedType, Context context) throws TypeError {
        return inferNumericOperatorType("comp", compExpr.expr_1, compExpr.expr_2, expectedType, context);
    }

    /**
     * Infers the type of a greater-than-or-equal expression (>=).
     *
     * @param compExpr The greater-than-or-equal expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the greater-than-or-equal expression (Bool)
     * @throws TypeError If the operands are not of type Nat or the result doesn't match the expected type
     */
    private static Type inferGreaterThanOrEqualType(
            GreaterThanOrEqual compExpr,
            Type expectedType,
            Context context) throws TypeError {
        return inferNumericOperatorType("comp", compExpr.expr_1, compExpr.expr_2, expectedType, context);
    }

    /**
     * Infers the type of an equality expression (==).
     *
     * @param compExpr The equality expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the equality expression (Bool)
     * @throws TypeError If the operands are not of type Nat or the result doesn't match the expected type
     */
    private static Type inferEqualityType(Equal compExpr, Type expectedType, Context context) throws TypeError {
        return inferNumericOperatorType("comp", compExpr.expr_1, compExpr.expr_2, expectedType, context);
    }

    /**
     * Infers the type of an inequality expression (!=).
     *
     * @param compExpr The inequality expression
     * @param expectedType The expected type, or null if no specific type is expected
     * @param context The typing context
     * @return The type of the inequality expression (Bool)
     * @throws TypeError If the operands are not of type Nat or the result doesn't match the expected type
     */
    private static Type inferInequalityType(NotEqual compExpr, Type expectedType, Context context) throws TypeError {
        return inferNumericOperatorType("comp", compExpr.expr_1, compExpr.expr_2, expectedType, context);
    }

    private record Pair<A, B>(A first, B second) {
        /**
         * Creates a new pair.
         *
         * @param first  The first value
         * @param second The second value
         */
        private Pair {
        }
    }
}
