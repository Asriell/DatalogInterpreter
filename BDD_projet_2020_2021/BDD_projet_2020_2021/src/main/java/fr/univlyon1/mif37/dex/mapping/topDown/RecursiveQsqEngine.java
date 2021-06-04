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
    private void qsqr(AdornedAtom p, Relation newInput, QSQRState state) {

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
        if (!rule.bodyHasFree()) {//If no free variable -> already computed, we can build the answer with AND of inputs i, the state.
            Map<String,Map<String,List<String>>> inputs = (Map<String,Map<String,List<String>>>)state.inputByRule.get(rule);
            AdornedAtom head = rule.getHead();
            List<AdornedAtom> body = rule.getBody();
            Map<String,List<String>> input1 = inputs.get(body.get(0).getAtom().getName());// for the atom 0 : $x = {...], $y = {...}
            Map<String,List<String>> input2 = inputs.get(body.get(1).getAtom().getName());// for the atom 1 : $x = {...], $y = {...}
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
            System.out.println(couplesInput1);
            System.out.println(couplesInput2);


            List<List<String>> answersArray = new ArrayList<>();//answer = union(intersect(atoms))
            for(List<String> inputs1: couplesInput1) {
                for(List<String> inputs2 : couplesInput2) {
                    if (intersectsSameIndex(inputs1,inputs2)) {
                        answersArray.add(unionTwoArrays(inputs1,inputs2));
                    }
                }
            }

            System.out.println(answersArray);
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
            System.out.println(answers);
            //conversion of the answer

        } else {
            System.out.println("Build the recursion");
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
