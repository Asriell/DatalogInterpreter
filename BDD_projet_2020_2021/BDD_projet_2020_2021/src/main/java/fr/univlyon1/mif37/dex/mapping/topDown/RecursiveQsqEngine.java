package fr.univlyon1.mif37.dex.mapping.topDown;

import com.sun.org.apache.xpath.internal.operations.Bool;
import fr.univlyon1.mif37.dex.mapping.*;

import java.util.*;
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
        private Map<Object,Object> ans;// Datas for each IDB, Map<String,List<String[]>> -> ans[IDB] = {couple of answers} -> [query] = {[x,y],[y,z]} for example
        /**
         * Tracks which input tuples have been used for each rule.
         */
        private Map<Object,Object> inputByRule;//Map<AdornedTgd, Map<String,Map<String,List<String>>>   > -> inputByRule[Rule] =  ( [predicate1] = [[$var1] = [value1,value2], [$var2] = ...]] )
        /**
         * Holds all the adorned rules for a given adorned predicate.
         */
        private Map<Object,Object> adornedRules;//Map<String, List<Adorned Tgd>> -> adorned rules for a predicate
        /**
         * Holds all the unadorned rules for a given predicate.
         */
        private final Map<Object,Object>  unadornedRules; // Map<String, List<Tgd> -> all rules for each IDB


        /**
         * Initializes state with a set of all unadorned rules for the program.
         *
         * @param unadornedRules
         *            set of unadorned rules
         */
        public QSQRState(Map<Object,Object> unadornedRules) {
            this.ans = new LinkedHashMap<>();
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
     * Preparation of query q and retun the obtained result : adornment of the body query
     *
     *
    **/

    public Set<Object> query(Atom q) {
        //adornment of the query
        Map<Object,Object> unadornedRules = new HashMap<>(); //unadornedRules[IDB predicate] = rules
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
        //System.out.println(state);



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
                //System.out.println(head);
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
                    constants.put(left.getName(),constantsForOnePredicate);
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
        qsqrSubroutine(adornedQuery,null,state);
        Map<String,Map<String,List<String>>> inputs = (Map<String,Map<String,List<String>>>)state.inputByRule.get(adornedQuery);
        Map<String,List<String>> inputsQuery = inputs.get(adornedQuery.getHead().getAtom().getName());
        if (inputsQuery != null) {
            Map.Entry<String,List<String>> entr = inputsQuery.entrySet().iterator().next();
            for(int i = 0; i < inputsQuery.get(entr.getKey()).size(); i++) {
                List<String> tuple = new ArrayList<>();
                for (Map.Entry<String,List<String>> entry : inputsQuery.entrySet()) {
                    tuple.add(entry.getValue().get(i));
                }
                result.add(tuple);
            }
        }
        return result;
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
        List<Tgd> unadornedRules = (List<Tgd>) state.unadornedRules.get(p.getAtom().getName());
        for(Tgd tgd : unadornedRules) {
            System.out.println("_________________________");
            System.out.println("input : " + newInput);
            System.out.println("tgd : " + tgd);

            Atom head = tgd.getRight();
            Collection<Literal> body = tgd.getLeft();
            List<Boolean> adornments = new ArrayList<>();
            for(Variable var : head.getVars()) {
                if (newInput.containsKey(var.getName()))
                {
                    adornments.add(true);
                } else {
                    adornments.add(false);
                }
            }
            AdornedAtom adornedHead = new AdornedAtom(head,adornments);
            List<AdornedAtom> adornedBody = new ArrayList<>();
            for(Literal literal : body) {
                Atom atom = literal.getAtom();
                Map<String,List<String>> inputAtom = new HashMap<>();
                for(Variable var : atom.getVars()) {
                    inputAtom.put(var.getName(),new ArrayList<>());
                }
                for(fr.univlyon1.mif37.dex.mapping.Relation edb : mapping.getEDB()) {
                    if(atom.getName().equals(edb.getName())) {
                        Iterator<Map.Entry<String,List<String>>> it = inputAtom.entrySet().iterator();
                        Map.Entry<String,List<String>> entr = it.next();
                        for(String s : edb.getAttributes()) {
                            List<String> list = inputAtom.get(entr.getKey());
                            list.add(s);
                            inputAtom.put(entr.getKey(), list);
                            if (it.hasNext()) {
                                entr = it.next();
                            }
                        }

                    }
                }
                List<List<String>> tmp = new ArrayList<>();
                Map.Entry<String,List<String>> entr = inputAtom.entrySet().iterator().next();
                for(int i = 0; i < inputAtom.get(entr.getKey()).size(); i++) {
                    List<String> elementTmp = new ArrayList<>();
                    for( Map.Entry<String,List<String>> entry : inputAtom.entrySet()) {
                        elementTmp.add(inputAtom.get(entry.getKey()).get(i));
                    }
                    tmp.add(elementTmp);
                }
                System.out.println("inputAtom : " + inputAtom);
                System.out.println("tmp : " + tmp);
                List<List<String>>tmp2 = new ArrayList<>();
                entr = newInput.entrySet().iterator().next();
                for(int i = 0; i < newInput.get(entr.getKey()).size(); i++) {
                    List<String> elementTmp = new ArrayList<>();
                    for( Map.Entry<String,List<String>> entry : inputAtom.entrySet()) {
                        if (newInput.containsKey(entry.getKey())) {
                            elementTmp.add(newInput.get(entry.getKey()).get(i));
                        } else {
                            elementTmp.add("");
                        }
                    }
                    tmp2.add(elementTmp);
                }
                System.out.println("tmp2 : " + tmp2);
                List<List<String>> tmp3 = new ArrayList<>();
                for(List<String> list1 : tmp) {
                    for (List<String> list2 : tmp2) {
                        if (intersectsSameIndex(list1,list2)) {
                            tmp3.add(unionTwoArrays(list1,list2));
                        }
                    }
                }
                System.out.println("tmp3 : " + tmp3);
                for( Map.Entry<String,List<String>> entry : inputAtom.entrySet()) {
                    inputAtom.put(entry.getKey(),new ArrayList<>());
                }
                for (int i = 0; i < tmp3.size(); i++) {
                    int j = 0;
                    for( Map.Entry<String,List<String>> entry : inputAtom.entrySet()) {
                        List<String> elements = inputAtom.get(entry.getKey());
                        elements.add(tmp3.get(i).get(j));
                        inputAtom.put(entry.getKey(),elements);
                        j++;
                    }
                }
                System.out.println("input atom : " + inputAtom);
            }
        }
    }

    /**
     * Evaluates the supplied rule using the input tuples newInput.
     *
     * @param rule
     *            rule
     * @param newInput
     *            input tuples
     * @param state
     *            current state of evaluation-wide variables
     */
    private void qsqrSubroutine(AdornedTgd rule, Relation newInput, QSQRState state) {
        Map<String,Map<String,List<String>>> inputs = (Map<String,Map<String,List<String>>>)state.inputByRule.get(rule); //inputs by atoms and by variables
        if (!rule.bodyHasFree()) {//If no free variable -> already computed, we can build the answer with AND of inputs i, the state.
            AdornedAtom head = rule.getHead();
            List<AdornedAtom> body = rule.getBody();
            Map<String,List<String>> input1 = inputs.get(body.get(0).getAtom().getName());// for the atom 0 : $x = {...], $y = {...}
            Map<String,List<String>> input2;
            if (body.size()>1) {
                input2 = inputs.get(body.get(1).getAtom().getName());// for the atom 1 : $x = {...], $y = {...}
            } else {
                input2 = input1;
            }
            List<List<String>> couplesInput1 = new ArrayList<>();//for the atom 0 : ((x1,y1),(x2,y2),...)
            List<List<String>> couplesInput2 = new ArrayList<>();//for the atom 1 : ((x1,y1),(x2,y2),...)
            List<String> variablesInput1 = new ArrayList<>();//for the atom 0 : ($x,$y,...)
            for (Map.Entry<String,List<String>> entry : input1.entrySet()) {
                variablesInput1.add(entry.getKey());
            }
            List<String> variablesInput2 = new ArrayList<>();//for the atom 1 : ($x,$y,...)
            for (Map.Entry<String,List<String>> entry : input2.entrySet()) {
                variablesInput2.add(entry.getKey());
            }
            List<String> commonVars = new ArrayList<>(variablesInput1); //union of both
            for(String s : variablesInput2) {
                if(!commonVars.contains(s)) {
                    commonVars.add(s);
                }
            }
            Collections.sort(commonVars);
            Map.Entry<String,List<String>> entr = input1.entrySet().iterator().next();//converts to the same form (($x,"") for atom 1 if only has $x but atom 2 has ($x,$y)) and put in couplesInput1
            for(int i = 0; i < input1.get(entr.getKey()).size(); i++) {
                List<String> vals = new ArrayList<>();
                for (String s : commonVars)  {
                    if (input1.containsKey(s)) {
                        vals.add(input1.get(s).get(i));
                    } else {
                        vals.add("");
                    }
                }
                couplesInput1.add(vals);
            }

            entr = input2.entrySet().iterator().next();//same than couplesInput1
            for(int i = 0; i < input2.get(entr.getKey()).size(); i++) {
                List<String> vals = new ArrayList<>();
                for (String s : commonVars)  {
                    if (input2.containsKey(s)) {
                        vals.add(input2.get(s).get(i));
                    } else {
                        vals.add("");
                    }
                }
                couplesInput2.add(vals);
            }

            List<List<String>> answersArray = new ArrayList<>();//answer = union(intersect(atoms))
            for(List<String> inputs1: couplesInput1) {
                for(List<String> inputs2 : couplesInput2) {
                    if (intersectsSameIndex(inputs1,inputs2)) {
                        answersArray.add(unionTwoArrays(inputs1,inputs2));
                    }
                }
            }

            Map<String,List<String>> answers = new HashMap<>();
            int i = 0;
            for(String s : commonVars) {
                for(List<String> tuple : answersArray) {
                    if (!answers.containsKey(s)) {
                        answers.put(s,new ArrayList<String>());
                    }
                    List<String> tmp = answers.get(s);
                    tmp.add(tuple.get(i));//add the new constant to the constants set of a given variable
                    answers.put(s,tmp);
                }
                i++;
            }

            List<String> headVars = new ArrayList<>();

            for (Variable v : head.getAtom().getVars()) {
                headVars.add(v.getName());
            }
            Map<String, List<String>> filteredAnswers = new HashMap<>(answers);
            //conversion of the answer
            for (Map.Entry<String,List<String>> entry : answers.entrySet()) {
                if (!headVars.contains(entry.getKey())) {
                    filteredAnswers.remove(entry.getKey());
                }
            }

            inputs.put(head.getAtom().getName(),filteredAnswers);
            state.inputByRule.put(rule,inputs);

            List<Boolean> headAdornment = new ArrayList<>();
            for(i = 0; i < filteredAnswers.size(); i++) {
                headAdornment.add(true);
            }
            rule.getHead().setAdornment(headAdornment);
        } else {
            //Top-down affectation
            List<AdornedAtom>body = rule.getBody();

            for(AdornedAtom atom : body) {
                if(atom.hasFree()) {
                    qsqr(atom,inputs.get(atom.getAtom().getName()),state);
                }
            }
        }
    }

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

    private List<String> unionTwoArrays(List<String>array1,List<String>array2) {
        List<String> result = new ArrayList<>(array1);
        int i = 0;
        for(String s : result) {
            if(s.equals("")) {
                //System.out.println(array2.get(i));
                result.set(i,array2.get(i));
            }
            i++;
        }
        return result;
    }

    private Mapping mapping;
    public RecursiveQsqEngine(Mapping mapping) {
        this.mapping = mapping;
    }

}
