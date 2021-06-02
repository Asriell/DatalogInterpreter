package fr.univlyon1.mif37.dex;

import fr.univlyon1.mif37.dex.mapping.*;


import fr.univlyon1.mif37.dex.mapping.topDown.AdornedAtom;
import fr.univlyon1.mif37.dex.mapping.topDown.RecursiveQsqEngine;
import fr.univlyon1.mif37.dex.parser.MappingParser;
import fr.univlyon1.mif37.dex.parser.ParseException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class App {
    private static final Logger LOG = LoggerFactory.getLogger(App.class);

    public static void main(String[] args) throws Exception {
        MappingParser mp = new MappingParser(App.class.getResourceAsStream("/exemple3.txt"));
        Mapping mapping = mp.mapping();
        /*
        LOG.info("\n"+mapping.toString());
        LOG.info("Parsed {} edb(s), {} idb(s) and {} tgd(s).",
                mapping.getEDB().size(),
                mapping.getIDB().size(),
                mapping.getTgds().size());
         */
        //System.out.println(Arrays.stream(((Literal)((Tgd)mapping.getTgds().toArray()[mapping.getTgds().size()-1]).getLeft().toArray()[0]).getAtom().getArgs()).toArray()[1]);
        /*
        List<Boolean> bools = new ArrayList<Boolean>();
        bools.add(Boolean.TRUE);
        bools.add(Boolean.FALSE);
        AdornedAtom at = new AdornedAtom(   ((Literal)((Tgd) mapping.getTgds().toArray()[mapping.getTgds().size()-1]).getLeft().toArray()[1]).getAtom(), bools);
         */

        /*
        for (Tgd tgd : mapping.getTgds()) {
            for(Literal l : tgd.getLeft()) {
                Atom a = l.getAtom();
                if (a.getArgs().length == 1) {
                    for(Relation edb : mapping.getEDB()) {
                        if (a.getName().equals(edb.getName())) {
                            System.out.println(edb.getAttributes()[0]);
                        }
                    }
                }
            }
        }*/
        RecursiveQsqEngine engine = new RecursiveQsqEngine(mapping);
        engine.query(((Tgd)mapping.getTgds().toArray()[mapping.getTgds().size()-1]).getRight());
    }
}
