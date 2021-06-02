package fr.univlyon1.mif37.dex.mapping;

import java.util.Arrays;
import java.util.List;
import java.util.ArrayList;
import java.util.Collection;

public class Atom {

    private String name;
    private Value[] args;

    public Atom(String name, List<Value> args) {
        this.name = name;
        this.args = args.toArray(new Value[args.size()]);
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public Value[] getArgs() {
        return args;
    }

    public Collection<Variable> getVars() {
      Collection<Variable> container = new ArrayList<Variable>();
      for (Value v: this.getArgs()) {
        if (v instanceof Variable) {
          container.add((Variable)v);
        }
      }
      return container;
    }

    @Override
    public String toString() {
        String result = "";
        result += name + "(";
        int i = 1;
        for(Value v : args) {
            result += v;
            if(i  != args.length)
                result += ",";
            ++i;
        }
        result += ")";
        return  result;
    }
}
