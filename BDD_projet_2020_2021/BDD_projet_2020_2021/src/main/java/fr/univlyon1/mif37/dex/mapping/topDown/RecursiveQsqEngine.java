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
        private Map<Object,Object> inputByRule;//Map<AdornedTgd, Map<String,List<String>> > -> inputByRule[Rule] = [[$var1] = [value1,value2], [$var2] = ...]
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
     * Preparation of query q and retun the obtained result
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

                //non determinist file reading : need a body correction :
                for (AdornedAtom atom : body) {
                    Map<String,List<String>> constantsForOnePredicate = constants.get(atom.getAtom().getName());
                    for (int index = 0; index < atom.getAtom().getVars().toArray().length; index++) {
                        Boolean isFinallyBound = false;
                        for (Map.Entry<String,Map<String,List<String>>> entry : constants.entrySet()) {
                            if (entry.getValue().containsKey(((Variable)atom.getAtom().getVars().toArray()[index]).getName())) {
                                booleans.add(true);
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
        System.out.println(state);
        //qsqrSubroutine(adornedQuery,null,state);
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
        System.out.println(rule);
        System.out.println(state);
        System.out.println(rule.bodyHasFree());
        if (!rule.bodyHasFree()) {//If no free variable -> already computed, we can build the answer.
            Map<String,List<String>> inputs = (Map<String,List<String>>)state.inputByRule.get(rule);
            AdornedAtom head = rule.getHead();
            List<String[]> answers = new ArrayList<>();
            for (int h = 0; h < inputs.get(((Variable)head.getAtom().getVars().toArray()[0]).getName()).size(); h++) {
                String couple [] = new String [head.getAtom().getVars().toArray().length];
                for(int i = 0; i < head.getAtom().getVars().toArray().length; i++) {
                    couple[i] = inputs.get(((Variable)head.getAtom().getVars().toArray()[i]).getName()).get(h);
                }
                answers.add(couple);
            }
            state.ans.put(head.getAtom().getName(),answers);
            for (String []s :  (List<String[]>) state.ans.get("query"))
                System.out.println(" [ " + s[0]  + " , " + s[1] +  " ] ");
            for(AdornedTgd tgd : (List<AdornedTgd>) state.adornedRules.get(head.getAtom().getName()) ) {
                System.out.println(tgd.getHead().getAtom().getName());
                for (int index = 0; index < tgd.getHead().getAtom().getVars().toArray().length; index++) {
                    tgd.getHead().getAdornment().set(index,true);
                }
            }
            System.out.println(state);
        } else {
            System.out.println("Build the recursion");
        }
    }

    private Mapping mapping;
    public RecursiveQsqEngine(Mapping mapping) {
        this.mapping = mapping;
    }

}
