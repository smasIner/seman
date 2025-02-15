package org.stella.typecheck;

import org.syntax.stella.Absyn.Type;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Context {
    private Map<String, Type> variables = new HashMap<>();
    private List<String> availableGenericTypes = new ArrayList<>();

    public Context() {
    }

    public Context(List<String> initialAvailableTypes) {
        this.availableGenericTypes.addAll(initialAvailableTypes);
    }

    public Context(Context oldContext) {
        this.variables = new HashMap<>(oldContext.variables);
        this.availableGenericTypes = new ArrayList<>(oldContext.availableGenericTypes);
    }

    public void appendVariables(Map<String, Type> newVariables) {
        this.variables.putAll(newVariables);
    }

    public void appendTypes(List<String> newTypes) {
        this.availableGenericTypes.addAll(newTypes);
    }

    public Type getVariableType(String varIdent) {
        return this.variables.get(varIdent);
    }

    public boolean hasType(String typeIdent) {
        return this.availableGenericTypes.contains(typeIdent);
    }

    public boolean hasVariable(String varIdent) {
        return this.variables.containsKey(varIdent);
    }
}
