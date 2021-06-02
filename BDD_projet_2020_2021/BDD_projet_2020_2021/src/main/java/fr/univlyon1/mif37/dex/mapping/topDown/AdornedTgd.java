package fr.univlyon1.mif37.dex.mapping.topDown;

import java.util.List;
/**
 * @juba BDD
 */
/**
 * An adorned tgd (i.e., a Horn clause where every atom is itself adorned).
 *
 */

public class AdornedTgd {

    private final AdornedAtom head;
    private final List<AdornedAtom> body;

    public AdornedAtom getHead() {
        return head;
    }

    public List<AdornedAtom> getBody() {
        return body;
    }
    /**
     * Constructs an adorned tgd given an adorned atom for the head and a
     * list of adorned atoms for the body.
     *
     * @param head
     *            head atom of clause
     * @param body
     *            atoms for body of clause
     */
    public AdornedTgd(AdornedAtom head, List<AdornedAtom> body) {
        this.head = head;
        this.body = body;
    }

    @Override
    public String toString() {
        return "[head : " + head.toString() + "], [body : " + body + "]";
    }

}
