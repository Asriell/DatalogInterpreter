package fr.univlyon1.mif37.dex.mapping.topDown;

import com.sun.org.apache.xpath.internal.operations.Bool;
import fr.univlyon1.mif37.dex.mapping.*;
import fr.univlyon1.mif37.dex.mapping.Relation;

import java.awt.*;
import java.util.*;
import java.util.List;
/**
 * @juba BDD
 */
/**
 * A Datalog evaluation engine that uses a recursive version of the
 * query-subquery top-down technique.
 *
 */
public class RecursiveQsqEngine {
    /**
     * A container for tracking global information passed back and forth between
     * recursion frames.
     *
     */
    private class QSQRState {
        /**
         * Tracks the answer tuples generated for each adorned predicate.
         */
        private Collection<fr.univlyon1.mif37.dex.mapping.Relation> ans;// Datas for each IDB, Map<String,List<String[]>> -> ans[IDB] = {couple of answers} -> [query] = {[x,y],[y,z]} for example
        /**
         * Tracks which input tuples have been used for each rule.
         */
        private Map<AdornedTgd, Map<String,Map<String,List<String>>>> inputByRule;//Map<AdornedTgd, Map<String,Map<String,List<String>>>   > -> inputByRule[Rule] =  ( [predicate1] = [[$var1] = [value1,value2], [$var2] = ...]] )
        /**
         * Holds all the adorned rules for a given adorned predicate.
         */
        private Map<String, List<AdornedTgd>> adornedRules;//Map<String, List<AdornedTgd>> -> adorned rules for a predicate
        /**
         * Holds all the unadorned rules for a given predicate.
         */
        private final Map<String, List<Tgd>>  unadornedRules; // Map<String, List<Tgd> -> all rules for each IDB


        /**
         * Initializes state with a set of all unadorned rules for the program.
         *
         * @param unadornedRules
         *            set of unadorned rules
         */
        public QSQRState(Map<String, List<Tgd>> unadornedRules) {
            this.ans = new ArrayList<>();
            this.inputByRule = new LinkedHashMap<>();
            this.adornedRules = new LinkedHashMap<>();
            this.unadornedRules = unadornedRules;

        }

        @Override
        public String toString() {
            return "ans : " + ans + "  , inputByRule : " + inputByRule + " , adornedRules : " + adornedRules + "  , unardornedRules : " + unadornedRules;
        }

    }

    /**
     *
     *
     * Preparation of query q and retun the obtained result : adornment of the body of the query
     *
     *
    **/

    public List<Object> query(Atom q) {//0-> results, 1-> answer details, 2-> the whole state
        //adornment of the query
        Map<String, List<Tgd>> unadornedRules = new HashMap<>(); //unadornedRules[IDB predicate] = rules
        for(AbstractRelation idb : mapping.getIDB()) {
            List<Tgd> tgds = new ArrayList<>();
            for(Tgd tgd : mapping.getTgds()) {
                if(idb.getName().equals(tgd.getRight().getName())) {
                    tgds.add(tgd);
                }
                unadornedRules.put(idb.getName(),tgds);
            }
        }
        QSQRState state = new QSQRState(unadornedRules);



        Set<Object> result = new LinkedHashSet<>();


        //Beginning of the adornment of the query
        Map<String,Map<String,List<String>>> constants = new HashMap<>();
        for(Tgd tgd : this.mapping.getTgds()) {
            if (q == tgd.getRight()) {
                List<Boolean> booleans = new ArrayList<>(q.getArgs().length);//list of adornments
                for(int i =0; i < q.getArgs().length; i++) {
                    booleans.add(false); //Before resolution, query has no bound variable.
                }
                AdornedAtom head = new AdornedAtom(q,booleans);
                List<AdornedAtom> body = new ArrayList<>();
                for (int i = 0; i < tgd.getLeft().size(); i++) {
                    Map<String,List<String>> constantsForOnePredicate = new HashMap<>(); //constants[parameter] = value
                    Atom left = ((Literal) tgd.getLeft().toArray()[i]).getAtom();
                    booleans = new ArrayList<>(left.getArgs().length);
                    Boolean isBound = false;
                    for (fr.univlyon1.mif37.dex.mapping.Relation edb : this.mapping.getEDB()) {
                        if (edb.getName().equals(left.getName())) {//there is EDBs with the predicate of the atom -> its variables are bound
                            isBound = true;
                            for(int j = 0; j < edb.getAttributes().length; j++) {//add values to constants array
                                if (!constantsForOnePredicate.containsKey(((Variable)left.getVars().toArray()[j]).getName())) {
                                    constantsForOnePredicate.put(((Variable)left.getVars().toArray()[j]).getName(),new ArrayList<String>());
                                }
                                List<String> tmp = constantsForOnePredicate.get(((Variable)left.getVars().toArray()[j]).getName());
                                tmp.add(edb.getAttributes()[j]);//add the new constant to the constants set of a given variable
                                constantsForOnePredicate.put(((Variable)left.getVars().toArray()[j]).getName(),tmp);
                            }
                        }
                    }
                    for(int j = 0; j < left.getArgs().length; j++) {
                        if (isBound) {
                            booleans.add(true);
                        } else {
                            Boolean isFinallyBound = false;
                            for (Map.Entry<String,Map<String,List<String>>> entry : constants.entrySet()) {
                                if (entry.getValue().containsKey(((Variable)left.getVars().toArray()[j]).getName())) {
                                    booleans.add(true);
                                    isFinallyBound = true;
                                    break;
                                }
                            }
                            if (!isFinallyBound) {
                                booleans.add(false);
                            }
                        }
                    }
                    if (!constants.containsKey(left.getName())) {
                        constants.put(left.getName(),constantsForOnePredicate);
                    } else {
                        Map<String,List<String>> CFOP = constants.get(left.getName());
                        for(Map.Entry<String,List<String>> elements : constantsForOnePredicate.entrySet()) {
                            if(!CFOP.containsKey(elements.getKey())){
                                CFOP.put(elements.getKey(), elements.getValue());
                            }
                        }
                    }
                    body.add(new AdornedAtom(left,booleans));
                }

                //non determinist file reading : need a body correction and variable affectations :
                for (AdornedAtom atom : body) {
                    Map<String,List<String>> constantsForOnePredicate = constants.get(atom.getAtom().getName());
                    for (int index = 0; index < atom.getAtom().getVars().toArray().length; index++) {
                        Boolean isFinallyBound = false;
                        for (Map.Entry<String,Map<String,List<String>>> entry : constants.entrySet()) {
                            if (entry.getValue().containsKey(((Variable)atom.getAtom().getVars().toArray()[index]).getName())) {
                                booleans.add(true);
                                if (!constantsForOnePredicate.containsKey(((Variable)atom.getAtom().getVars().toArray()[index]).getName()))
                                    constantsForOnePredicate.put(((Variable)atom.getAtom().getVars().toArray()[index]).getName(),entry.getValue().get(((Variable)atom.getAtom().getVars().toArray()[index]).getName()));
                                isFinallyBound = true;
                                break;
                            }
                        }
                        if (isFinallyBound) {
                            atom.getAdornment().set(index,true);
                        }
                    }
                }

                AdornedTgd adornedRule =  new AdornedTgd(head,body);
                List<AdornedTgd> adornedRules = new ArrayList<>();
                adornedRules.add(adornedRule);
                state.adornedRules.put(q.getName(),adornedRules); //adornedRules[query] = query adornment
                state.inputByRule.put(adornedRule,constants); //all the constants found. inputByRule[query adornment] = Dictionary variable -> constants.
            }
        }
        AdornedTgd adornedQuery =((List<AdornedTgd>)state.adornedRules.get(q.getName())).get(0);
        qsqrSubroutine(adornedQuery,0,state);

        for(Relation relation : state.ans) {
            if (relation.getName().equals(adornedQuery.getHead().getAtom().getName())) {
                List<String> tuples = new ArrayList<>();
                for (String s : relation.getAttributes()) {
                    tuples.add(s);
                }
                result.add(tuples);
            }
        }
        List<Object> details = new ArrayList<>();
        details.add(result);
        details.add(state.ans);
        details.add(state);
        return details;
    }

    /**
     * Evaluates the query represented by the adorned predicate p and the
     * relation newInput.
     *
     * @param p
     *            adorned predicate of query
     * @param newInput
     *            input tuples
     * @param state
     *            current state of evaluation-wide variables
     */
    private void qsqr(AdornedAtom p, Map<String,List<String>> newInput, QSQRState state) {

        List<List<String>> newInputList = new ArrayList<>();//Conversion of the inputs as a list (to make operations more simple)
        Map.Entry<String,List<String>> firstIndexInput = newInput.entrySet().iterator().next();
        for (int i = 0; i < newInput.get(firstIndexInput.getKey()).size(); i++) {
            List<String> line = new ArrayList<>();
            for (Variable predicateVariable : p.getAtom().getVars()) {
                Boolean inInputs = false;
                for(Map.Entry<String,List<String>> entry: newInput.entrySet()) {
                    if(predicateVariable.getName().equals(entry.getKey())){
                        line.add(entry.getValue().get(i));
                        inInputs = true;
                    }
                }
                if(!inInputs) {
                    line.add("");
                }
            }
            newInputList.add(line);
        }

        List<Tgd> unadornedRules = (List<Tgd>) state.unadornedRules.get(p.getAtom().getName());
        List<AdornedTgd> tgds = new ArrayList<>();
        Map<String,List<String>> inputAllPredicates = new HashMap<>();
        for(Tgd tgd : unadornedRules) {//adornment for all unadorned rules which contains our predicate
            Atom head = tgd.getRight();
            Collection<Literal> body = tgd.getLeft();
            List<Boolean> adornments = new ArrayList<>();
            for(Variable var : head.getVars()) { //the head first : if there are inputs relatives to the head, these variables are bound
                if (newInput.containsKey(var.getName()))
                {
                    adornments.add(true);
                } else {
                    adornments.add(false);
                }
            }
            AdornedAtom adornedHead = new AdornedAtom(head,adornments);
            List<AdornedAtom> adornedBody = new ArrayList<>();
            Map<String,Map<String,List<String>>> constants = new HashMap<>();
            //Side-ways passing information -> pass the informations to the body
            for(Literal literal : body) {
                Atom atom = literal.getAtom(); //for each atoms in the body...
                Map<String,List<String>> constantsForOnePredicate = new HashMap<>();
                for(Variable var : atom.getVars()) {
                    constantsForOnePredicate.put(var.getName(),new ArrayList<>());
                }
                Boolean isEdb = false;
                for(fr.univlyon1.mif37.dex.mapping.Relation edb : mapping.getEDB()) { //if this atom is an edb, copy of the constants for its variables
                    if(atom.getName().equals(edb.getName())) {
                        isEdb = true;
                        Iterator<Map.Entry<String,List<String>>> it = constantsForOnePredicate.entrySet().iterator();
                        Map.Entry<String,List<String>> entr = it.next();
                        for(String s : edb.getAttributes()) {
                            List<String> list = constantsForOnePredicate.get(entr.getKey());
                            list.add(s);
                            constantsForOnePredicate.put(entr.getKey(), list);
                            if (it.hasNext()) {
                                entr = it.next();
                            }
                        }

                    }
                }


                if (!isEdb) {//if there are bound variables with previous edbs atoms.
                    for (Variable variable : literal.getAtom().getVars()) {
                        for (Map.Entry<String,Map<String, List<String>>> computedConstants : constants.entrySet()) {
                            if (computedConstants.getValue().containsKey(variable.getName())) {
                                constantsForOnePredicate.put(variable.getName(),computedConstants.getValue().get(variable.getName()));
                            }
                        }
                    }
                }

                List<List<String>> tmp = new ArrayList<>();//change the "$x : ... $y : ... form to (...,...) form for the inputs and the atom
                Map.Entry<String,List<String>> entr = constantsForOnePredicate.entrySet().iterator().next();
                for(int i = 0; i < constantsForOnePredicate.get(entr.getKey()).size(); i++) {
                    List<String> elementTmp = new ArrayList<>();
                    for( Map.Entry<String,List<String>> entry : constantsForOnePredicate.entrySet()) {
                        elementTmp.add(constantsForOnePredicate.get(entry.getKey()).get(i));
                    }
                    tmp.add(elementTmp);
                }
                List<List<String>> tmp3 = new ArrayList<>();  //join of the input and the edb.
                for(List<String> list1 : tmp) {
                    for (List<String> list2 : newInputList) {
                        if (intersectsSameIndex(list1,list2)) {
                            tmp3.add(unionTwoArrays(list1,list2));
                        }
                    }
                }
                for( Map.Entry<String,List<String>> entry : constantsForOnePredicate.entrySet()) {//clear the map to update it with fusion beetween input and edb (Above).
                    constantsForOnePredicate.put(entry.getKey(),new ArrayList<>());
                }
                for (int i = 0; i < tmp3.size(); i++) {//map updating
                    int j = 0;
                    for( Map.Entry<String,List<String>> entry : constantsForOnePredicate.entrySet()) {
                        List<String> elements = constantsForOnePredicate.get(entry.getKey());
                        elements.add(tmp3.get(i).get(j));
                        constantsForOnePredicate.put(entry.getKey(),elements);
                        j++;
                    }
                }
                Map<String,List<String>>inputMapTmp = new HashMap<>(constantsForOnePredicate);
                for( Map.Entry<String,List<String>> entry : inputMapTmp.entrySet()) {
                    if (entry.getValue().isEmpty()) {
                        constantsForOnePredicate.remove(entry.getKey());
                    }
                }


                constants.put(atom.getName(),constantsForOnePredicate);

                if (isEdb && constantsForOnePredicate.isEmpty()) {//contradition -> useless to continue
                    return;
                }

                List <Boolean>adornment = new ArrayList<>();
                for(Variable variable : atom.getVars()) { //computes the adornment
                    if (constantsForOnePredicate.containsKey(variable.getName()) || isEdb) {//if a variable has a constants, this variable is bound.
                        adornment.add(true);
                    } else {
                        Boolean isFinallyBound = false;
                        for (Map.Entry<String,Map<String,List<String>>> entry : constants.entrySet()) {//if the variable is bound in another atom, this variable is bound.
                            if (entry.getValue().containsKey(variable.getName()) && !constantsForOnePredicate.containsKey(variable.getName())) {
                                constantsForOnePredicate.put(variable.getName(), entry.getValue().get(variable.getName()));
                                adornment.add(true);
                                isFinallyBound = true;
                            }
                        }
                        if (!isFinallyBound)
                            adornment.add(false);
                    }
                }

                adornedBody.add(new AdornedAtom(atom,adornment));
            }

            for (AdornedAtom atom : adornedBody) {//adornment correction (due to non determinist file reading)
                Map<String,List<String>> constantsForOnePredicate = constants.get(atom.getAtom().getName());
                int i = 0;
                for(Variable variable : atom.getAtom().getVars()) {
                    if (! constantsForOnePredicate.containsKey(variable.getName()))  {
                        for (Map.Entry<String,Map<String,List<String>>> entry : constants.entrySet()) {
                            if (entry.getValue().containsKey(variable.getName()) && !constantsForOnePredicate.containsKey(variable.getName())) {
                                constantsForOnePredicate.put(variable.getName(), entry.getValue().get(variable.getName()));
                                atom.getAdornment().set(i,true);
                            }
                        }
                    }
                    i++;
                }
            }
            AdornedTgd adornedTgd = new AdornedTgd(adornedHead,adornedBody);
            tgds.add( adornedTgd);
            state.inputByRule.put(adornedTgd,constants);//fill QSQRState

        }
        if (!state.adornedRules.containsKey(p.getAtom().getName()))
            state.adornedRules.put(p.getAtom().getName(),tgds);
        for (int i = 0; i < tgds.size(); i++) {
            qsqrSubroutine(tgds.get(i),state.ans.size(),state);
        }
        for (Map.Entry<String, List<AdornedTgd>> entry : state.adornedRules.entrySet()) { //updating of adornment, for each rule.
            for(AdornedTgd adornedTgd : entry.getValue()) {
                List<AdornedAtom> adornedBody = adornedTgd.getBody();
                for(AdornedAtom atom :adornedBody) {
                    if (atom.getAtom().getName().equals(tgds.get(0).getHead().getAtom().getName())) {
                        atom.setAdornment(tgds.get(0).getHead().getAdornment());
                    }
                }
            }
        }
    }

    /**
     * Evaluates the supplied rule using the input tuples newInput.
     *
     * @param rule
     *            rule
     * @param ansSize
     *            Size of calls of qsqrSubroutine
     * @param state
     *            current state of evaluation-wide variables
     */
    private void qsqrSubroutine(AdornedTgd rule, int ansSize, QSQRState state) {

        List<Integer> commons = new ArrayList<>();//non determinist rule reading -> sorting of the rule
        for(int i = 0; i < rule.getBody().size();i++) {
            int common = 0;
            AdornedAtom atom1 = rule.getBody().get(i);
            for(int j = 0; j < rule.getBody().size(); j++) {
                AdornedAtom atom2 = rule.getBody().get(j);
                for(Variable var1 : atom1.getAtom().getVars()) {
                    for(Variable var2 : atom2.getAtom().getVars()) {
                        if (var1.getName().equals(var2.getName())) {
                            common ++;
                        }
                    }
                }
            }
            commons.add(common);
        }

        for(int i = 0; i < rule.getBody().size();i++){
            int maxId = i;
            int max = commons.get(i);
            for(int j = i; j <  rule.getBody().size(); j++) {
                if (max < commons.get(j)) {
                    maxId = j;
                }
            }
            AdornedAtom tmp = rule.getBody().get(i);
            rule.getBody().set(i, rule.getBody().get(maxId));
            rule.getBody().set(maxId, tmp);
        }
        Map<String,Map<String,List<String>>> inputs = (Map<String,Map<String,List<String>>>)state.inputByRule.get(rule); //inputs by atoms and by variables
        if (!rule.bodyHasFree()) {//If no free variable -> already computed, we can build the answer with AND of inputs i, the state.
            AdornedAtom head = rule.getHead();
            List<AdornedAtom> body = rule.getBody();
            Map<String,List<String>> input1 = inputs.get(body.get(0).getAtom().getName());// for the atom 0 : $x = {...], $y = {...}
            Map<String,List<String>> input2;
            Map<String, List<String>> filteredAnswers = new HashMap<>();
            for (int indexAtoms = 0; indexAtoms < body.size(); indexAtoms++) {
                if (indexAtoms >= 1) {
                    input2 = new HashMap<>(inputs.get(body.get(indexAtoms).getAtom().getName()));// for the atom 1 : $x = {...], $y = {...}
                } else {
                    input2 = new HashMap<>(input1);
                }

                Map<String,List<String>> input2Tmp = new HashMap<>(input2);
                for (Map.Entry<String,List<String>> inputEntry : input2Tmp.entrySet()) {
                    Boolean exists = false;
                    for(Variable v : body.get(indexAtoms).getAtom().getVars()) {
                        String s = v.getName();
                        if(s.equals(inputEntry.getKey())) {
                            exists = true;
                        }

                    }
                    if (!exists) {
                        input2.remove(inputEntry.getKey());
                    }
                }

                Map<String,List<String>> answers = eval(input1,input2);

                filteredAnswers = filter(head,answers);
                input1 = answers;
            }
            if (!filteredAnswers.isEmpty()) {
                Map.Entry<String,List<String>> entries = filteredAnswers.entrySet().iterator().next();//answers updating
                for (int l = 0; l < filteredAnswers.get(entries.getKey()).size() ; l++) {
                    List <String> attributes = new ArrayList<>();
                    for(Variable v : head.getAtom().getVars()) {
                        attributes.add(filteredAnswers.get(v.getName()).get(l));
                    }
                    Boolean add = true;

                    if (state.ans.size() != 0) {//to not add duplicates
                        for (fr.univlyon1.mif37.dex.mapping.Relation relation : state.ans) {
                            int index = 0;
                            int similarities = 0;
                            for (index = 0; index < relation.getAttributes().length; index++) {
                                if (attributes.size() > index){
                                    if (relation.getAttributes()[index].equals(attributes.get(index))) {
                                        similarities ++;
                                    }
                                }
                            }
                            if (similarities == index) {
                                add = false;
                            }
                        }
                    }
                    if (add) {
                        state.ans.add(new fr.univlyon1.mif37.dex.mapping.Relation(head.getAtom().getName(),attributes));
                    }
                }
            }

            inputs.put(head.getAtom().getName(),filteredAnswers);//inputs updating
            state.inputByRule.put(rule,inputs);

            List<Boolean> headAdornment = new ArrayList<>();
            for(int i = 0; i < filteredAnswers.size(); i++) {
                headAdornment.add(true);
            }
            rule.getHead().setAdornment(headAdornment);//adornment of the head updating

        } else {

            if (rule.hasRecursion()) {//a recursive atom is not free but has to be evaluated : look for all the adbs and previous answers to have a result
                Map<String, Map<String,List<String>>> constants = new HashMap<>();
                Map<String, List<String>> filteredAnswers = new HashMap<>();
                List<AdornedAtom> queue = new ArrayList<>();
                for(AdornedAtom a : rule.getBody()) {
                    Map<String,List<String>> constantsForOnePredicate = new HashMap<>();
                    Boolean isEdb = false;
                    for (fr.univlyon1.mif37.dex.mapping.Relation edb : this.mapping.getEDB()) {
                        if (edb.getName().equals(a.getAtom().getName())) {
                            isEdb = true;
                            for(int j = 0; j < edb.getAttributes().length; j++) {//add values to constants array
                                if (!constantsForOnePredicate.containsKey(((Variable)a.getAtom().getVars().toArray()[j]).getName())) {
                                    constantsForOnePredicate.put(((Variable)a.getAtom().getVars().toArray()[j]).getName(),new ArrayList<String>());
                                }
                                List<String> tmp = constantsForOnePredicate.get(((Variable)a.getAtom().getVars().toArray()[j]).getName());
                                tmp.add(edb.getAttributes()[j]);//add the new constant to the constants set of a given variable
                                constantsForOnePredicate.put(((Variable)a.getAtom().getVars().toArray()[j]).getName(),tmp);
                            }
                        }
                    }
                    if (!isEdb) {
                        for(Relation idb : state.ans) {
                            if (idb.getName().equals(a.getAtom().getName())) {
                                for(int j = 0; j < idb.getAttributes().length; j++) {//add values to constants array
                                    if (!constantsForOnePredicate.containsKey(((Variable)a.getAtom().getVars().toArray()[j]).getName())) {
                                        constantsForOnePredicate.put(((Variable)a.getAtom().getVars().toArray()[j]).getName(),new ArrayList<String>());
                                    }
                                    List<String> tmp = constantsForOnePredicate.get(((Variable)a.getAtom().getVars().toArray()[j]).getName());
                                    tmp.add(idb.getAttributes()[j]);//add the new constant to the constants set of a given variable
                                    constantsForOnePredicate.put(((Variable)a.getAtom().getVars().toArray()[j]).getName(),tmp);
                                }
                            }
                        }
                    }
                    constants.put(a.getAtom().getName(),constantsForOnePredicate);
                    queue.add(a);
                }
                Map<String,List<String>> input1 = constants.get(rule.getBody().get(0).getAtom().getName());
                for (int i = 1; i < queue.size(); i++) {
                    Map<String,List<String>> input2 = constants.get(rule.getBody().get(i).getAtom().getName());
                    Map<String,List<String>> answers = eval(input1,input2); //as above, evaluation and filtering of result.
                    filteredAnswers = filter(rule.getHead(), answers);
                }
                Iterator<Map.Entry<String,List<String>>> entriesIterator = filteredAnswers.entrySet().iterator();//answers updating
                if (entriesIterator.hasNext()) {
                    Map.Entry<String,List<String>> entries = entriesIterator.next();
                    for (int l = 0; l < filteredAnswers.get(entries.getKey()).size() ; l++) {
                        List <String> attributes = new ArrayList<>();
                        for (Map.Entry<String,List<String>> vars : filteredAnswers.entrySet()) {
                            attributes.add(vars.getValue().get(l));
                        }
                        Boolean add = true;

                        if (state.ans.size() != 0) {//to not add duplicates
                            for (fr.univlyon1.mif37.dex.mapping.Relation relation : state.ans) {
                                int index = 0;
                                int similarities = 0;
                                for (index = 0; index < relation.getAttributes().length; index++) {
                                    if (attributes.size() > index){
                                        if (relation.getAttributes()[index].equals(attributes.get(index))) {
                                            similarities ++;
                                        }
                                    }
                                }
                                if (similarities == index) {
                                    add = false;
                                }
                            }
                        }
                        if (add) {
                            state.ans.add(new fr.univlyon1.mif37.dex.mapping.Relation(rule.getHead().getAtom().getName(),attributes));
                        }
                    }

                    inputs.put(rule.getHead().getAtom().getName(),filteredAnswers);//inputs updating
                    state.inputByRule.put(rule,inputs);
                }


                List<Boolean> headAdornment = new ArrayList<>();
                for(int i = 0; i < filteredAnswers.size(); i++) {
                    headAdornment.add(true);
                }
                rule.getHead().setAdornment(headAdornment);//adornment of the head updating
                if (ansSize == state.ans.size()) { //if no new result, we have to stop to avoid infinite loop.
                    return ;
                }
            }


            //Top-down information passing : we look for all free variables in our IDB, on the head of tcgs.
            List<AdornedAtom>body = rule.getBody();

            List<AdornedAtom> freeAtoms = new ArrayList<>();
            for(AdornedAtom atom : body) {
                if(atom.hasFree()) {
                    qsqr(atom,inputs.get(atom.getAtom().getName()),state); //adornment computing
                    freeAtoms.add(atom);
                }
            }
            for(AdornedAtom atom : freeAtoms) {//refreshing of inputs according to the answers.
                inputs.get(atom.getAtom().getName()).clear();
                for(fr.univlyon1.mif37.dex.mapping.Relation relation : state.ans) {
                    System.out.println(relation);
                    if(relation.getName().equals(atom.getAtom().getName())) {
                        int i = 0;
                        for( Variable var : state.adornedRules.get(atom.getAtom().getName()).get(0).getHead().getAtom().getVars()) {
                            if(! inputs.get(atom.getAtom().getName()).containsKey(var.getName())) {
                                inputs.get(atom.getAtom().getName()).put(var.getName(),new ArrayList<>());
                            }
                            List <String> tmp =  inputs.get(atom.getAtom().getName()).get(var.getName());
                            tmp.add(relation.getAttributes()[i]);
                            i++;
                        }
                    }
                }
            }
            qsqrSubroutine(rule,state.ans.size(),state);//evaluation with new inputs
        }
    }

    /**
     * Returns true if the both arrays have a same String at a same index
     * @param array1 an array of String
     * @param array2 an array of String
     * @return a boolean
     */
    private Boolean intersectsSameIndex(List<String>array1,List<String>array2) {
        int i = 0;
        for(String s : array1) {
            if (s.equals(array2.get(i))) {
                return true;
            }
            i++;
        }
        return false;
    }

    /**
     * Fills the empty slots of an array with another array
     * @param array1 an array with empty slots
     * @param array2 another array
     * @return a filled array
     */
    private List<String> unionTwoArrays(List<String>array1,List<String>array2) {
        List<String> result = new ArrayList<>(array1);
        int i = 0;
        for(String s : result) {
            if(s.equals("")) {
                result.set(i,array2.get(i));
            }
            i++;
        }
        return result;
    }

    /**
     * evaluation of two atoms, with their inputs.
     * @param input1 Inputs of the first atom
     * @param input2 Inputs of the second atom
     * @return the result of a subquery with both atoms.
     */
    private Map<String, List<String>> eval(Map<String,List<String>> input1, Map<String,List<String>> input2) {
        List<List<String>> couplesInput1 = new ArrayList<>();//for the atom 0 : ((x1,y1),(x2,y2),...)
        List<List<String>> couplesInput2 = new ArrayList<>();//for the atom 1 : ((x1,y1),(x2,y2),...)
        List<String> variablesInput1 = new ArrayList<>();//for the atom 0 : ($x,$y,...)
        for (Map.Entry<String, List<String>> entry : input1.entrySet()) {
            variablesInput1.add(entry.getKey());
        }
        List<String> variablesInput2 = new ArrayList<>();//for the atom 1 : ($x,$y,...)
        for (Map.Entry<String, List<String>> entry : input2.entrySet()) {
            variablesInput2.add(entry.getKey());
        }
        List<String> commonVars = new ArrayList<>(variablesInput1); //union of both
        for (String s : variablesInput2) {
            if (!commonVars.contains(s)) {
                commonVars.add(s);
            }
        }
        Collections.sort(commonVars);
        Map.Entry<String, List<String>> entr = input1.entrySet().iterator().next();//converts to the same form (($x,"") for atom 1 if only has $x and no $y but atom 2 has ($x,$y)) and put in couplesInput1
        for (int i = 0; i < input1.get(entr.getKey()).size(); i++) {
            List<String> vals = new ArrayList<>();
            for (String s : commonVars) {
                if (input1.containsKey(s)) {
                    vals.add(input1.get(s).get(i));
                } else {
                    vals.add("");
                }
            }
            couplesInput1.add(vals);
        }

        entr = input2.entrySet().iterator().next();//same than couplesInput1
        for (int i = 0; i < input2.get(entr.getKey()).size(); i++) {
            List<String> vals = new ArrayList<>();
            for (String s : commonVars) {
                if (input2.containsKey(s)) {
                    vals.add(input2.get(s).get(i));
                } else {
                    vals.add("");
                }
            }
            couplesInput2.add(vals);
        }

        List<List<String>> answersArray = new ArrayList<>();//answer = union(intersect(atoms))
        for (List<String> inputs1 : couplesInput1) {
            for (List<String> inputs2 : couplesInput2) {
                if (intersectsSameIndex(inputs1, inputs2)) {
                    answersArray.add(unionTwoArrays(inputs1, inputs2));
                }
            }
        }

        Map<String, List<String>> answers = new HashMap<>();
        int i = 0;
        for (String s : commonVars) {
            for (List<String> tuple : answersArray) {
                if (!answers.containsKey(s)) {
                    answers.put(s, new ArrayList<String>());
                }
                List<String> tmp = answers.get(s);
                tmp.add(tuple.get(i));//add the new constant to the constants set of a given variable
                answers.put(s, tmp);
            }
            i++;
        }

        return answers;

    }

    /**
     * Removes elements which does not appear in the head.
     * @param head head of a rule
     * @param answers a map of values we have to filter
     * @return the answer filtered.
     */
    private  Map<String, List<String>> filter (AdornedAtom head,Map<String, List<String>> answers) {
        Map<String, List<String>> filteredAnswers = new HashMap<>();
        List<String> headVars = new ArrayList<>();

        for (Variable v : head.getAtom().getVars()) {
            headVars.add(v.getName());
        }
        filteredAnswers = new HashMap<>(answers);
        //conversion of the answer
        for (Map.Entry<String, List<String>> entry : answers.entrySet()) {
            if (!headVars.contains(entry.getKey())) {
                filteredAnswers.remove(entry.getKey());
            }
        }
        return filteredAnswers;
    }

    private Mapping mapping;
    public RecursiveQsqEngine(Mapping mapping) {
        this.mapping = mapping;
    }

}
