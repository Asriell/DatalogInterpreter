package fr.univlyon1.mif37.dex.mapping.topDown;

import fr.univlyon1.mif37.dex.mapping.Value;

import java.util.List;
/**
 * @juba BDD
 */

/**
 * A tuple of terms, i.e., an ordered list of fixed arity.
 *
 */
public class Tuple {
    /**
     * The value in this tuple.
     */
    public  Value[] elts;

    /**
     * Constructs a tuple from a list of values.
     *
     * @param elts
     *            the list of values
     */
    public Tuple(List<Value> elts) {
        Value[] tmp = new Value[elts.size()];
        this.elts = elts.toArray(tmp);

    }

}
