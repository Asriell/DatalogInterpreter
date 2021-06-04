package fr.univlyon1.mif37.dex.mapping.topDown;
import com.sun.jmx.remote.internal.ArrayQueue;
import fr.univlyon1.mif37.dex.mapping.Atom;
import fr.univlyon1.mif37.dex.mapping.Value;
import fr.univlyon1.mif37.dex.mapping.Variable;

import java.util.ArrayList;
import java.util.List;
/**
 * @juba BDD
 */

/**
 * An adorned atom. Each argument of any atom formed from this
 * predicate symbol will be marked as bound or free in accordance with the
 * predicate's adornment.
 *
 */


public class AdornedAtom {

    private Atom atom;
    /**
     * The adornment of the atom. A true value means that the
     * corresponding term in the arguments of an atom
     * is considered bound; a false value implies that the argument is
     * free.
     */
    private List<Boolean> adornment;
    /**
     * Total number of bound terms in the adornment.
     */
    private int bound;


    public Atom getAtom() {
        return atom;
    }

    public List<Boolean> getAdornment() {
        return adornment;
    }
    public void setAdornment(List<Boolean> _adornment) {
        adornment = _adornment;
    }

    public int getBound() {
        return bound;
    }

    public Boolean hasFree() {
        for (Boolean bound : adornment) {
            if (!bound) {
                return true;
            }
        }
        return false;
    }
    /**
     * Constructs an adorned Atom from a atom and an
     * adornment.
     *
     * @param atom
     *            atom
     * @param adornment
     *            adornment
     */
    public AdornedAtom(Atom atom, List<Boolean> adornment) {
        List<Value> args = new ArrayList<Value>();
        for (Value v : atom.getArgs()) {
            args.add(v);
        }
        this.atom = new Atom(atom.getName(),args);
        this.adornment = new ArrayList<Boolean>();
        for(Boolean b : adornment) {
            this.adornment.add(b);
        }
    }

    @Override
    public String toString() {
        String result = atom.toString();
        result += " ";
        result += adornment.toString();
        return result;
    }

}
