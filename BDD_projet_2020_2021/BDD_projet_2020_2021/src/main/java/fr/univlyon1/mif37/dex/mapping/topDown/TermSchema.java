package fr.univlyon1.mif37.dex.mapping.topDown;
import fr.univlyon1.mif37.dex.mapping.Value;
import java.util.List;
/**
 * @juba BDD
 */
/**
 * A list of terms of fixed arity representing the attribute schema for a
 * relation of the same arity (i.e., the 2nd term in the list is the attribute
 * for the 2nd "column" in the relation).
 *
 */
public class TermSchema {
    /**
     * The attributes of this schema.
     */
    public final List<Value> attributes;

    /**
     * Constructs a schema from a list of terms.
     *
     * @param terms
     *            the terms
     */
    public TermSchema(List<Value> terms) {
        this.attributes = terms;
    }

}
