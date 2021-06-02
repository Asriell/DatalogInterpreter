package fr.univlyon1.mif37.dex.mapping.topDown;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
/**
 * @juba BDD
 */
/**
 * A relation, i.e., a set of tuples  with an associated
 * attribute schema of the same arity.
 *
 */
public class Relation {
    /**
     * The tuples of this relation.
     */
    protected Set<Tuple> tuples;
    /**
     * The attribute schema of this relation.
     */
    protected TermSchema attributes;

    /**
     * Constructs an empty relation
     */
    public Relation (){
        this.tuples = new HashSet<Tuple>();
        this.attributes = new TermSchema(new ArrayList<>());
    }
}
