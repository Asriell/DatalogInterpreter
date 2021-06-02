package fr.univlyon1.mif37.dex.mapping;

import com.google.common.collect.Multimap;

import java.util.List;
import java.util.Map;

/*
*@juba depends on your usage this class can be avoided
* 
**/
public class Result {

    private final Map<Value, String> parameters;

    private final List<String> listIdb;

    public Result(List<String> listIdb, Map<Value, String> parameters) {
        this.parameters = parameters;
        this.listIdb = listIdb;
    }

    public Map<Value, String> getParameters() {
        return parameters;
    }


    public List<String> getListIdb() {
        return listIdb;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Result result = (Result) o;

        if (parameters != null ? !parameters.equals(result.parameters) : result.parameters != null) return false;
        return listIdb != null ? listIdb.equals(result.listIdb) : result.listIdb == null;
    }

    @Override
    public int hashCode() {
        int result = parameters != null ? parameters.hashCode() : 0;
        result = 31 * result + (listIdb != null ? listIdb.hashCode() : 0);
        return result;
    }

    @Override
    public String toString() {
        return "Result{" +
                "parameters=" + parameters +
                ", listIdb=" + listIdb +
                '}';
    }
}
