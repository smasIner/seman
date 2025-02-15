package org.stella.typecheck;

import org.syntax.stella.Absyn.Type;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Env {
    private Map<String, Type> functionTypes = new HashMap<>();
    private Map<String, List<String>> functionGenericTypes = new HashMap<>();

    public void appendFunction(String funcIdent, Type funcType) {
        this.functionTypes.put(funcIdent, funcType);
    }

    public void appendFunctionGenerics(String funcIdent, List<String> generics) {
        this.functionGenericTypes.put(funcIdent, generics);
    }

    public Type getFunctionType(String funcIdent) {
        return this.functionTypes.getOrDefault(funcIdent, null);
    }

    public List<String> getFunctionGenerics(String funcIdent) {
        return this.functionGenericTypes.getOrDefault(funcIdent, new ArrayList<>());
    }
}
