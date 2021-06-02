package fr.univlyon1.mif37.dex.mapping;

import java.util.Arrays;
import java.util.List;

/**
 * Created by ecoquery on 20/05/2016.
 */
public class Relation {

    private String name;
    private String[] attributes;

    public Relation(String name, List<String> attributes) {
        this.name = name;
        this.attributes = attributes.toArray(new String[attributes.size()]);
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String[] getAttributes() {
        return attributes;
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder(name + '(');

        for(String s : this.getAttributes())
            result.append(s).append(',');
        result.deleteCharAt(result.length()-1);
        result.append(')');
        return result.toString();
    }

}
