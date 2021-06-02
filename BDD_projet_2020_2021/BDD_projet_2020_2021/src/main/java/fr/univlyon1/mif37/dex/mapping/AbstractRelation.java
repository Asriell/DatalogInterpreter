package fr.univlyon1.mif37.dex.mapping;

import java.util.Arrays;
import java.util.List;

public class AbstractRelation {

    private String name;
    private AbstractArgument[] attributes;

    public AbstractRelation(String name, List<AbstractArgument> attributes) {
        this.name = name;
        this.attributes = attributes.toArray(new AbstractArgument[attributes.size()]);
    }

    public String getName() {
        return name;
    }

    public AbstractArgument[] getAttributes() {
        return attributes;
    }

    @Override
    public String toString() {
        String result = "";
        result += name + "(";
        int i = 1;
        for(AbstractArgument r : attributes) {
            result += r.toString();
            if(i != attributes.length)
                result += ",";
            ++i;
        }
        result += ")";
        return result;
    }
}
