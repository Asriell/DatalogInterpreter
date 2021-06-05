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
        MappingParser mp = new MappingParser(App.class.getResourceAsStream("/exemple5.txt"));
        Mapping mapping = mp.mapping();

        RecursiveQsqEngine engine = new RecursiveQsqEngine(mapping);
        System.out.println(
                "Query answer : " +
                engine.query(((Tgd)mapping.getTgds().toArray()[mapping.getTgds().size()-1]).getRight())
        );
    }
}
