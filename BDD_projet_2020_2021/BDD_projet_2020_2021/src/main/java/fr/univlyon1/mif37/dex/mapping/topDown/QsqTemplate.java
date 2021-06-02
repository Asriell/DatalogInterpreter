package fr.univlyon1.mif37.dex.mapping.topDown;

import fr.univlyon1.mif37.dex.mapping.Atom;
import fr.univlyon1.mif37.dex.mapping.Value;

import java.util.ArrayList;
import java.util.List;
/**
 * @juba BDD
 */
/**
 * A template containing the attribute schemata of the supplementary relations
 * for a given rule in QSQ evaluation.
 *
 */
public class QsqTemplate {
    /**
     * The attribute schemata for the supplementary relations.
     */
    private  List<TermSchema> schemata;
    /**
     * Constructs a template from an adorned rule.
     *
     * @param rule
     *            the adorned rule
     */
    public QsqTemplate(AdornedTgd rule) {
        schemata = new ArrayList<>();
        List<Value> listValsHead = new ArrayList<>();
        for(Value v : rule.getHead().getAtom().getVars()) {
            listValsHead.add(v);
        }
        schemata.add(new TermSchema(listValsHead));


        for (AdornedAtom a : rule.getBody()) {
            List<Value> listValsBody = new ArrayList<>();
            for (Value v : a.getAtom().getArgs())
            {
                listValsBody.add(v);
            }
            schemata.add(new TermSchema(listValsBody));
        }
    }

}
