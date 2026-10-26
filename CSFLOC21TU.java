package org.example;
import java.util.*;
import java.io.*;

public class CSFLOC21TU {
    private static String fileName =
            "C:\\Temp\\satlib\\ssa2670-141.cnf";
    static String variableRenamingStrategy = "CUB"; // may contain the letters: B, C, H, I, R, S, T, U, W, or the same lower case letters
    static boolean doInvert = false; // If true then each literal is negated in the input. In case of pigeon-holes it should be true.
    static int[] extraUnits = null; // if null, then no change, keep it null, unless to learn the effect of extra units, like: {-1},{+10}, or {-1,+10}
    static int[] flips = null; // if null, then no changes, otherwise flips to entry in translate


    static int learn10ClausesPerLevel = 1;    // 0 = do not learn clauses,
    // 1 = learn max 10 clauses at each index level,
    // 3 short (length<=5), 3 medium (length<=9), and 4 long ones
    static int addLongTailClauses = 0;    // 0 = do not add long tail clauses,
    // 1 = add long tail clauses,
    // 2 = use learnedClauses to store long tail clauses
    static int clusteringFactor = 5; // it must be at least 2,
    // works only if the variable renaming strategy contains "C" for clustering
    static int clauseListWithSorting = 0;    // 0 = do not use sorting while creating a clause list
    // 1 = use sorting while creating a clause list, sort by the first literal
    // it is easy to add a new kind of sorting, just create a new subclass of ClauseList
    static int BCP = 0;                 // does not work, must be 0, 0 = do not do BCP, 1 = do BCP, it works, but only if the input is UNSAT, otherwise do not use this option yet
    public static int learn3ClausesForClauses = 0;    // it works, but it is a beta feature, so do not use yet, so let it be 0
    // 0 = do not learn clauses for each clause,
    // 1 = learn max 3 clauses for each clause
    public static int useExtendedResolution = 0;  // number of new variables added by extended resolution

    // New feature: enumerate all solutions.
    static boolean listAllSolutions = false; // default: list all solutions

    public static void main(String[] args) {
        try {
            if (args.length >= 1) {
                fileName = args[0];
                if (fileName.equals("-help") ||
                        fileName.equals("help") ||
                        fileName.equals("-?") ||
                        fileName.equals("?")) {
                    printHelp();
                    return;
                }
            }
            if (args.length >= 2) {
                variableRenamingStrategy = args[1];
                if (args[1].toUpperCase().equals("NON")) variableRenamingStrategy = "";
            }
            if (args.length >= 3) { learn10ClausesPerLevel = Integer.parseInt(args[2]); }
            if (args.length >= 4) { addLongTailClauses = Integer.parseInt(args[3]); }
            if (args.length >= 5) { clusteringFactor = Integer.parseInt(args[4]); }
            if (args.length >= 6) { clauseListWithSorting = Integer.parseInt(args[5]); }
            if (args.length >= 7) { listAllSolutions = Integer.parseInt(args[6]) != 0; }
            if (args.length >= 8) {
                System.out.println("Too many parameters! Please read the help:");
                printHelp();
                return;
            }
        }
        catch(Exception e) {
            System.out.println("Argument error! Please read the help:");
            printHelp();
            return;
        }
        long startNs = System.nanoTime();
        DIMACSReader dcs = new DIMACSReader(fileName);
        if (useExtendedResolution > 0) dcs.addExtendedResolutionClauses(useExtendedResolution);
        if (extraUnits != null) dcs.addExtraUnits(extraUnits);
        HighLevelReader reader = new HighLevelReader(dcs, variableRenamingStrategy);

        // Build initial clause set (this also sorts literals inside clauses).
        ClauseSet S = reader.getClauseSet();
        int[] translate = reader.translate;
        ArrayList<int[]> cs = reader.getClauseSetAsArrayListOfIntArray();

        CSFLOCSolver.resetStatistics();
        CSFLOCSolver solver = new CSFLOCSolver(S, translate);
        boolean[] solution = solver.CSFLOC_v7();
        CSFLOCSolver.runtimeNanos = System.nanoTime() - startNs;

        if (!listAllSolutions) {
            if (solution == null) {
                System.out.println("s UNSATISFIABLE");
            } else {
                System.out.println("s SATISFIABLE");
                printSolutionInOriginalVariableOrder(solution, translate, S.numberOfVariables);
                System.out.println("c model check                            : " + CheckSolution.SimpleCheckSolution(cs, solution));
            }
        } else {
            if (solver.solutionsFound == 0) {
                System.out.println("s UNSATISFIABLE");
            } else {
                System.out.println("s SATISFIABLE");
                System.out.println("c number of solutions found             : " + solver.solutionsFound);
            }
        }
        solver.printStatistics();

    }

    private static ArrayList<int[]> deepCopyClauses(ArrayList<int[]> cs) {
        ArrayList<int[]> out = new ArrayList<>(cs.size());
        for (int[] clause : cs) {
            out.add(Arrays.copyOf(clause, clause.length));
        }
        return out;
    }

    /**
     * Prints a model as a DIMACS-style line (but without the ending 0),
     * in the order of the *original* variables (before renaming).
     */
    private static void printSolutionInOriginalVariableOrder(boolean[] internalSolution, int[] translate, int numberOfVariables) {
        StringBuilder sb = new StringBuilder("v");
        for (int i = 1; i <= numberOfVariables; i++) {
            int var = i;
            if (translate != null) {
                var = translate[i];
            }
            boolean value = internalSolution[var];
            if (doInvert) {
                value = !value;
            }
            sb.append(' ').append(value ? i : -i);
        }
        sb.append(" 0");
        System.out.println(sb);
    }

    /**
     * Returns a full-length blocking clause in the solver's *internal* variable indices.
     *
     * If a model assigns x_v = true, then the blocking clause contains -v; otherwise it contains +v.
     */
    private static int[] createBlockingClauseFromSolution(boolean[] internalSolution, int numberOfVariables) {
        int[] clause = new int[numberOfVariables];
        for (int v = 1; v <= numberOfVariables; v++) {
            clause[v - 1] = internalSolution[v] ? -v : v;
        }
        return clause;
    }

    private static void printHelp() {
        System.out.println("Usage: java CSFLOC21TU cnf_file_name variable_renaming_strategy use_learned_clauses add_long_tail_clauses clustering_factor clause_list_ordering [list_all_solutions]");
        System.out.println("Example (list all solutions): java CSFLOC21TU hole7.cnf BC 1 1 5 1 1");
        System.out.println("Example (stop at first solution): java CSFLOC21TU hole7.cnf BC 1 1 5 1 0");
        System.out.println("The parameter 'cnf_file_name' is the name of a file in DIMACS format containing a CNF SAT problem.");
        System.out.println("The parameter 'variable_renaming_strategy' may contain the letters in any order: B, C, H, I, R, S, T, U, W, or the same lower case letters;");
        System.out.println("or it is 'NON' which means, that there is no strategy.");
        System.out.println("If it is not set, then no strategy is used.");
        System.out.println("Letter 'B' means, that black clauses (all literals are negative) will contain low variable indices.");
        System.out.println("Letter 'C' means, that it clusters variables, i.e., it moves those variables closer, which occurs frequently together in the clauses.");
        System.out.println("Letter 'H' means, that definite horn clauses (exactly one positive literal) will contain low variable indices. It renames the literals of a definite horn clause only if non of them are renamed yet.");
        System.out.println("Letter 'I' means, that definite horn clauses will contain low variable indices. The positive literal will get the biggest index inside the definite horn clause.");
        System.out.println("Letter 'R' means, that it renames variables by their frequency, the most frequent variable will get the least index.");
        System.out.println("Letter 'S' means, that 'strait' clauses (exactly one negative literal) will contain low variable indices. The negative literal will get the least index inside the strait clause.");
        System.out.println("Letter 'T' means, that it tries to create a small prefix hitting all long clauses, so after the first variables are fixed the remaining formula is 2-SAT.");
        System.out.println("Letter 'U' means, that it tries to place variables so that the first variables create unit clauses as early as possible.");
        System.out.println("Letter 'W' means, that white clauses (all literals are positive) will contain low variable indices.");
        System.out.println("List of some useful strategies:");
        System.out.println("In case of random 3-SAT problems: 'IWCR', 'HWCR', or 'BHWCR'.");
        System.out.println("In case of pigeon-holes problems: 'B'.");
        System.out.println("In case of Black-and-White SAT problems generated by the Balatonboglar model: 'I 1 2 0 0'.");
        System.out.println("The parameter 'use_learned_clauses' may be 0 or 1.");
        System.out.println("If it is not set, then it is 1.");
        System.out.println("Number '0' means, that it does not use learned clauses to speed up the search.");
        System.out.println("Number '1' means, that it generates for each variable upto 2*10 learned clauses, and it uses them to speed up the search.");
        System.out.println("The parameter 'add_long_tail_clauses' may be 0, 1, or 2.");
        System.out.println("If it is not set, then it is 0.");
        System.out.println("Number '0' means, that it does not generate resolvents in the preprocessing steps.");
        System.out.println("Number '1' means, that it generates resolvents, which contains big index variables, and it adds them to the initial clause set.");
        System.out.println("Number '2' means, that it generates resolvents, which contains big index variables, and it adds them to the learned clauses.");
        System.out.println("The parameter 'clustering_factor' may be 2 or a bigger number.");
        System.out.println("If it is not set, then it is 5.");
        System.out.println("Clustering computes the variable pair frequency.");
        System.out.println("It groups the most frequent pairs in the first cluster until it becomes full, and so on.");
        System.out.println("It works only if the variable_renaming_strategy contains 'C'.");
        System.out.println("Usually 5 is the best option.");
        System.out.println("The parameter 'clause_list_ordering' may be 0 or 1.");
        System.out.println("If it is not set, then it is 0.");
        System.out.println("Number '0' means, that it does not sort clauses inside a clause list.");
        System.out.println("Number '1' means, that it sorts the clauses inside each clause list by the index of their first literal. For example {-1, 5, 10} precedes {2, 4, -8}.");
        System.out.println("Sorting almost always results in less 'numberOfRunsOfTheMainLoop', but sorting needs O(numberOfClauses*numberOfClauses/numberOfVariables) time, so if you have lots of clauses, you might consider to switch it off.");
        System.out.println("The optional parameter 'list_all_solutions' may be 0 or 1 (default: 1). 1 means enumerate all solutions by adding a blocking clause after each found model.");
    }
    private static void printParameters() {
        System.out.println("The parameter file_name was: " + fileName);
        System.out.println("The parameter variable_renaming_strategy was: '" + variableRenamingStrategy + "'");
        System.out.println("The parameter use_learned_clauses was: " + learn10ClausesPerLevel);
        System.out.println("The parameter add_long_tail_clauses was: " + addLongTailClauses);
        System.out.println("The parameter clustering_factor was: " + clusteringFactor);
        System.out.println("The parameter clause_list_ordering was: " + clauseListWithSorting);
        System.out.println("The parameter list_all_solutions was: " + (listAllSolutions ? 1 : 0));
    }
}

class CSFLOCSolver {
    static long numberOfRunsOfTheMainLoop = 0;
    static long numberOfUsedLearnedClauses = 0;
    static long islandsLengthSum = 0;
    static long islandsCount = 0;
    static long islandsMaxLength = 0;
    static long lastSeaLengthSum = 0;
    static long lastSeaCount = 0;
    static long lastSeaMaxLength = 0;
    static long jumpLengthSum = 0;
    static long jumpCount = 0;
    static long jumpMaxLength = 0;
    static long numberOfCasesWithoutLearnedClauses = 0;
    static long subsumptionCandidatesChecked = 0;
    static long subsumptionLiteralChecks = 0;
    static long subsumptionCandidateHits = 0;
    static long effectedCauseHits = 0;
    static long oldEffectedCauseHits = 0;
    static long inputClauseHits = 0;
    static long learnedClausesAdded = 0;
    static long learnedClauseCandidates = 0;
    static long learnedClauseRejectedDensePrefix = 0;
    static long effectedCausesInstalled = 0;
    static long effectedCausesCleared = 0;
    static long counterBitSets = 0;
    static long counterBitClears = 0;
    static long unionClausesBuilt = 0;
    static long runtimeNanos = 0;

    ClauseSet S;
    private final int[] translate;
    public long solutionsFound = 0;
    private final boolean[] tmpNegation;

    int numberOfVariables;
    Clause[][] effectedClauses, oldEffectedClauses;
    Clause[][] learnedClausesNeg;
    Clause[][] learnedClausesPos;

    public static void resetStatistics() {
        numberOfRunsOfTheMainLoop = 0;
        numberOfUsedLearnedClauses = 0;
        islandsLengthSum = 0;
        islandsCount = 0;
        islandsMaxLength = 0;
        lastSeaLengthSum = 0;
        lastSeaCount = 0;
        lastSeaMaxLength = 0;
        jumpLengthSum = 0;
        jumpCount = 0;
        jumpMaxLength = 0;
        numberOfCasesWithoutLearnedClauses = 0;
        subsumptionCandidatesChecked = 0;
        subsumptionLiteralChecks = 0;
        subsumptionCandidateHits = 0;
        effectedCauseHits = 0;
        oldEffectedCauseHits = 0;
        inputClauseHits = 0;
        learnedClausesAdded = 0;
        learnedClauseCandidates = 0;
        learnedClauseRejectedDensePrefix = 0;
        effectedCausesInstalled = 0;
        effectedCausesCleared = 0;
        counterBitSets = 0;
        counterBitClears = 0;
        unionClausesBuilt = 0;
        runtimeNanos = 0;
    }

    public CSFLOCSolver(ClauseSet S, int[] translate) {
        this.S = S;
        this.translate = translate;
        numberOfVariables = S.numberOfVariables;
        setupEffectedClauses();
        setupLearnedClauses();
        tmpNegation = new boolean[numberOfVariables + 1];
        if (CSFLOC21TU.addLongTailClauses == 2) { populateLearnedClauses(); }
    }

    public CSFLOCSolver(ClauseSet S) {
        this(S, null);
    }
    private void setupEffectedClauses() {
        effectedClauses = new Clause[numberOfVariables+1][2];
        oldEffectedClauses = new Clause[numberOfVariables+1][2];
    }
    private void setupLearnedClauses() {
        learnedClausesNeg = new Clause[numberOfVariables+1][10];
        learnedClausesPos = new Clause[numberOfVariables+1][10];
    }
    public void addEffectedClause(int index, Clause c) {
        c.isEffected = true;
        effectedCausesInstalled++;
        if (effectedClauses[index][0] == null)
            effectedClauses[index][0] = c;
        else
            effectedClauses[index][1] = c;
    }
    public void clearEffectedClauses(int index) {
        if (effectedClauses[index][0] != null || effectedClauses[index][1] != null) {
            effectedCausesCleared++;
        }
        oldEffectedClauses[index][0] = effectedClauses[index][0];
        oldEffectedClauses[index][1] = effectedClauses[index][1];
        effectedClauses[index][0] = null;
        effectedClauses[index][1] = null;
    }
    public void addLearnedClause_v6(Clause c) {
        //System.out.println("Learned clause: " + c);
        learnedClauseCandidates++;
        if (CSFLOC21TU.learn10ClausesPerLevel != 1) return;
        int index = c.lastVarIndex;
        if (c.literals.length == index) {
            learnedClauseRejectedDensePrefix++;
            return;
        }
        Clause[] cache = c.lastLiteral > 0 ?
                learnedClausesPos[index] :
                learnedClausesNeg[index];
        if (c.literals.length <= 5 || cache[2] == null) {
            cache[2] = cache[1];
            cache[1] = cache[0];
            cache[0] = c;
        } else
        if (c.literals.length <= 9 || cache[5] == null) {
            cache[5] = cache[4];
            cache[4] = cache[3];
            cache[3] = c;
        } else {
            cache[9] = cache[8];
            cache[8] = cache[7];
            cache[7] = cache[6];
            cache[6] = c;
        }
        learnedClausesAdded++;
    }
    public void populateLearnedClauses() {
        for(int i=numberOfVariables; i>0; i--) {
            if (S.clauseListOrderdByLastVarIndexNeg[i].length == 0) continue;
            Clause b = S.clauseListOrderdByLastVarIndexNeg[i][0];
            for(int j=0; j<S.clauseListOrderdByLastVarIndexPos[i].length; j++) {
                Clause a = S.clauseListOrderdByLastVarIndexPos[i][j];
                Clause c = Clause.resolution_v3(a,b,a.lastVarIndex);
                if (c!=null) {
                    if (c.lastLiteral > 0 && learnedClausesPos[c.lastLiteral][9] == null) addLearnedClause_v6(c);
                    else if (learnedClausesNeg[c.lastVarIndex][9] == null) addLearnedClause_v6(c);
                }
            }
        }
        for(int i=numberOfVariables; i>0; i--) {
            if (S.clauseListOrderdByLastVarIndexPos[i].length == 0) continue;
            Clause a = S.clauseListOrderdByLastVarIndexPos[i][0];
            for(int k=1; k<S.clauseListOrderdByLastVarIndexNeg[i].length; k++) {
                Clause b = S.clauseListOrderdByLastVarIndexNeg[i][k];
                Clause c = Clause.resolution_v3(a,b,a.lastVarIndex);
                if (c!=null) {
                    if (c.lastLiteral > 0 && learnedClausesPos[c.lastLiteral][9] == null) addLearnedClause_v6(c);
                    else if (learnedClausesNeg[c.lastVarIndex][9] == null) addLearnedClause_v6(c);
                }
            }
        }
    }

    private boolean[] negationOf(boolean[] counter) {
        for (int i = 0; i < counter.length; i++) {
            tmpNegation[i] = !counter[i];
        }
        return tmpNegation;
    }

    // Converts the current full-length counter representation into a Clause.
    // ("Caluse" is kept intentionally to match earlier call-sites / comments.)
    private Clause convertToCaluse(boolean[] counter) {
        int[] lits = new int[numberOfVariables];
        for (int i = 1; i <= numberOfVariables; i++) {
            lits[i - 1] = counter[i] ? i : -i;
        }
        return new Clause(lits);
    }

    private void printSolution(boolean[] internalSolution) {
        solutionsFound++;
        StringBuilder sb = new StringBuilder("v");
        for (int i = 1; i <= numberOfVariables; i++) {
            int var = i;
            if (translate != null) {
                var = translate[i];
            }
            boolean value = internalSolution[var];
            if (CSFLOC21TU.doInvert) {
                value = !value;
            }
            sb.append(' ').append(value ? i : -i);
        }
        sb.append(" 0");
        System.out.println(sb);
    }

    public boolean[] CSFLOC_v7() {
        boolean[] counter;
        counter = new boolean[numberOfVariables+1];
        int index = S.indexOfLastVariableOfBestBlackClause;
        if (index == S.numberOfVariables+1) {
            if (!CSFLOC21TU.listAllSolutions) {
                for(int i=0; i<counter.length; i++) { counter[i] = !counter[i]; }
                return counter;
            }
            // The all-negative full-length clause is not subsumed, so the all-positive assignment is a model.
            printSolution(negationOf(counter));

            // Continue enumeration by forcing an increment of 1.
            index = S.numberOfVariables;
            S.bestBlackClause = convertToCaluse(counter);
        }
        addEffectedClause(index, S.bestBlackClause);
        counter[index] = true;
        counterBitSets++;
        int oldIndex = index;
        int lengthOfTheLastIsland = 1;
        int lengthOfTheLastSea = index;
        int lengthOfTheLastJump = 0;
        while(index > 0) {
            numberOfRunsOfTheMainLoop++;
            index = usingBestClause_v4(index, counter);
            if (index == 0) {
                if (!CSFLOC21TU.listAllSolutions) {
                    for(int i=0; i<counter.length; i++) { counter[i] = !counter[i]; }
                    return counter;
                }
                printSolution(negationOf(counter));

                // Continue enumeration:
                // treat the current full-length clause C as subsuming itself, so we can increment by 1.
                index = S.numberOfVariables;
                addEffectedClause(index, convertToCaluse(counter));
            }
            index = increaseCounter_v5(index, true, counter);
            if (index - oldIndex == 1) {
                lengthOfTheLastIsland++;
                lengthOfTheLastSea = 0;
            }
            else {
                islandsLengthSum += lengthOfTheLastIsland;
                islandsCount++;
                lengthOfTheLastIsland = 1;
                lengthOfTheLastSea = index - oldIndex + 1;
            }
            if (lengthOfTheLastSea < 0) {
                lengthOfTheLastJump = oldIndex - index;
                jumpLengthSum += lengthOfTheLastJump;
                jumpCount++;
                lengthOfTheLastSea = 0; // undef
            }
            else {
                lastSeaLengthSum += lengthOfTheLastSea;
                lastSeaCount++;
            }
            if (lengthOfTheLastIsland > islandsMaxLength) {
                islandsMaxLength = lengthOfTheLastIsland;
                //System.out.println("islandsMaxLength: " + islandsMaxLength);
            }
            if (lengthOfTheLastSea > lastSeaMaxLength) {
                lastSeaMaxLength = lengthOfTheLastSea;
            }
            if (lengthOfTheLastJump > jumpMaxLength) {
                jumpMaxLength = lengthOfTheLastJump;
            }
            oldIndex = index;
        }
        return null;
    }
    private int usingBestClause_v4(int index, boolean[] counter) {
        // we try to cancel the last island, i.e.,
        // we try to find a clause which subsumes the counter and
        // its last literal is "+index"
        Clause a = effectedClauses[index][1];
        if (a != null && a.subsumedBy(counter)) {
            effectedCauseHits++;
            return index;
        }
        a = oldEffectedClauses[index][1];
        if (a != null && a.subsumedBy(counter)) {
            oldEffectedCauseHits++;
            addEffectedClause(index, a);
            return index;
        }
        Clause[] clauseList =  S.clauseListOrderdByLastVarIndexPos[index];
        for(Clause c : clauseList) {
            if (c.subsumedBy(counter)) {
                inputClauseHits++;
                addEffectedClause(index, c);
                return index;
            }
        }
        for(int i=0; i<learnedClausesPos[index].length; i++) {
            Clause c = learnedClausesPos[index][i];
            if (c == null) {
                if (i == 0) numberOfCasesWithoutLearnedClauses++;
                break;
            }
            if (c.subsumedBy(counter)) {
                numberOfUsedLearnedClauses++;
                addEffectedClause(index, c);
                return index;
            }
        }
        // we could not cancel the last island, so we have to build a new last one, i.e.,
        // we try to find a clause which subsumes the counter and
        // its last literal is "-index"
        for(index++ ; index<S.numberOfVariables+1; index++) {
            Clause b = effectedClauses[index][0];
            if (b != null && b.subsumedBy(counter)) {
                effectedCauseHits++;
                return index;
            }
            b = oldEffectedClauses[index][0];
            if (b != null && b.subsumedBy(counter)) {
                oldEffectedCauseHits++;
                addEffectedClause(index, b);
                return index;
            }
            clauseList =  S.clauseListOrderdByLastVarIndexNeg[index];
            for(Clause c : clauseList) {
                if (c.subsumedBy(counter)) {
                    inputClauseHits++;
                    addEffectedClause(index, c);
                    return index;
                }
            }
            for(int i=0; i<learnedClausesNeg[index].length; i++) {
                Clause c = learnedClausesNeg[index][i];
                if (c == null) {
                    if (i == 0) numberOfCasesWithoutLearnedClauses++;
                    break;
                }
                if (c.subsumedBy(counter)) {
                    numberOfUsedLearnedClauses++;
                    return useSubsumedClause(index, c, counter);
                }
            }
        }
        return 0;
    }
    private int useSubsumedClause(int index, Clause c, boolean[] counter) {
        if (CSFLOC21TU.learn3ClausesForClauses == 0) {
            addEffectedClause(index, c);
            return index;
        }
        Clause[] learnedClauses = c.learnedClauses;
        for(int i=0; i<learnedClauses.length; i++)
        {
            Clause learnedClause = learnedClauses[i];
            if (learnedClause != null && learnedClause.subsumedByNonLazy(counter)  ) {
                while(index>learnedClause.lastVarIndex)
                {
                    counter[index] = false;
                    clearEffectedClauses(index);
                    index--;
                }
                numberOfUsedLearnedClauses++;
                addEffectedClause(index, learnedClause);
                return index;
            }
        }
        addEffectedClause(index, c);
        return index;
    }
    private int increaseCounter_v5(int index, boolean first, boolean[] counter) {
        Clause union = null;
        if (counter[index]) {
            Clause a = effectedClauses[index][0];
            Clause b = effectedClauses[index][1];
            clearEffectedClauses(index);
            counter[index] = false;
            counterBitClears++;
            index--;
            union = Clause.union_v2(a, b, index);
            unionClausesBuilt++;
            if (first) a.addLearnedClause(union);
            if (first) b.addLearnedClause(union);
            if (first) addLearnedClause_v6(union); // this adds the most speed
        }
        while(counter[index] && union.lastVarIndex > 0) {
            Clause a = effectedClauses[index][0];
            clearEffectedClauses(index);
            counter[index] = false;
            counterBitClears++;
            if (union.lastLiteral == index) {
                Clause b = union;
                union = Clause.union_v2(a, b, index);
                unionClausesBuilt++;
            }
            index--;
        }
        if (union != null) {
            while(index>union.lastVarIndex)
            {
                counter[index] = false;
                counterBitClears++;
                clearEffectedClauses(index);
                index--;
            }
            addEffectedClause(index, union);
            return increaseCounter_v5(index, false, counter);
        }
        counter[index] = true;
        counterBitSets++;
        return index;
    }
    private static void printLong(String name, long value) {
        System.out.printf(Locale.US, "c %-44s : %d%n", name, value);
    }

    private static void printInt(String name, int value) {
        System.out.printf(Locale.US, "c %-44s : %d%n", name, value);
    }

    private static void printBool(String name, boolean value) {
        System.out.printf(Locale.US, "c %-44s : %s%n", name, value);
    }

    private static void printString(String name, String value) {
        System.out.printf(Locale.US, "c %-44s : %s%n", name, value);
    }

    private static void printDouble(String name, double value) {
        System.out.printf(Locale.US, "c %-44s : %.3f%n", name, value);
    }

    public void printStatistics() {
        long affectedSteps = effectedCauseHits + oldEffectedCauseHits;
        long learnedHits = numberOfUsedLearnedClauses;
        long allCategorizedHits = affectedSteps + inputClauseHits + learnedHits;

        System.out.println("c");
        System.out.println("c === CSFLOC statistics ===");
        printString("solver", "CSFLOC21TU");
        printString("counter representation", "boolean[]");
        printBool("uses watched-literal prefix BCP", false);
        printBool("learned cause cache enabled", CSFLOC21TU.learn10ClausesPerLevel == 1);
        printString("variable renaming strategy", CSFLOC21TU.variableRenamingStrategy.isEmpty() ? "NON" : CSFLOC21TU.variableRenamingStrategy);
        printInt("clustering factor", CSFLOC21TU.clusteringFactor);
        printBool("clause list sorting enabled", CSFLOC21TU.clauseListWithSorting == 1);
        printInt("add long tail clauses mode", CSFLOC21TU.addLongTailClauses);

        System.out.println("c");
        System.out.println("c --- input ---");
        printInt("variables", S.numberOfVariables);
        printInt("clauses", S.numberOfClauses);
        printLong("unused original clauses", numberOfUnUsedClauses());

        System.out.println("c");
        System.out.println("c --- comparable CSFLOC counters ---");
        printLong("main loop iterations", numberOfRunsOfTheMainLoop);
        printLong("step discoveries by affected causes", affectedSteps);
        printLong("step discoveries by input clauses", inputClauseHits);
        printLong("step discoveries by learned clauses", learnedHits);
        printLong("step discoveries by prefix propagation", 0);
        printDouble("affected-cause steps / main-loop (%)", percent(affectedSteps, numberOfRunsOfTheMainLoop));
        printDouble("input-clause steps / main-loop (%)", percent(inputClauseHits, numberOfRunsOfTheMainLoop));
        printDouble("learned-clause steps / main-loop (%)", percent(learnedHits, numberOfRunsOfTheMainLoop));

        System.out.println("c");
        System.out.println("c --- subsumption search and cache ---");
        printLong("subsumption candidates checked", subsumptionCandidatesChecked);
        printLong("subsumption literal checks", subsumptionLiteralChecks);
        printDouble("subsumption hit rate (%)", percent(subsumptionCandidateHits, subsumptionCandidatesChecked));
        printLong("learned clauses added", learnedClausesAdded);
        printLong("learned cause hits", learnedHits);
        printLong("learned clause candidates", learnedClauseCandidates);
        printLong("learned clauses rejected dense prefix", learnedClauseRejectedDensePrefix);
        printLong("cases without learned clauses", numberOfCasesWithoutLearnedClauses);
        printDouble("learned hits / all categorized hits (%)", percent(learnedHits, allCategorizedHits));

        System.out.println("c");
        System.out.println("c --- counter and derived-cause operations ---");
        printLong("counter bit sets", counterBitSets);
        printLong("counter bit clears", counterBitClears);
        printLong("effected causes installed", effectedCausesInstalled);
        printLong("effected causes cleared", effectedCausesCleared);
        printLong("union clauses built", unionClausesBuilt);
        printDouble("island length avg", safeDiv(islandsLengthSum, islandsCount));
        printLong("island length max", islandsMaxLength);
        printDouble("sea length avg", safeDiv(lastSeaLengthSum, lastSeaCount));
        printLong("sea length max", lastSeaMaxLength);
        printDouble("jump length avg", safeDiv(jumpLengthSum, jumpCount));
        printLong("jump length max", jumpMaxLength);

        // Keep runtime as the last measurement line to make automated parsing easy.
        System.out.printf(Locale.US, "c %-44s : %.6f%n", "runtime seconds", runtimeNanos / 1_000_000_000.0);
    }

    private static double safeDiv(long numerator, long denominator) {
        return denominator == 0 ? 0.0 : ((double) numerator) / denominator;
    }

    private static double percent(long numerator, long denominator) {
        return denominator == 0 ? 0.0 : 100.0 * ((double) numerator) / denominator;
    }

    public int numberOfUnUsedClauses() {
        int numberOfUnUsed = 0;
        for(int i=0; i<S.clauseListOrderdByLastVarIndexNeg.length; i++) {
            for(int j=0; j<S.clauseListOrderdByLastVarIndexNeg[i].length; j++) {
                if (!S.clauseListOrderdByLastVarIndexNeg[i][j].isEffected) {
                    numberOfUnUsed++;
                }
            }
        }
        for(int i=0; i<S.clauseListOrderdByLastVarIndexPos.length; i++) {
            for(int j=0; j<S.clauseListOrderdByLastVarIndexPos[i].length; j++) {
                if (!S.clauseListOrderdByLastVarIndexPos[i][j].isEffected) {
                    numberOfUnUsed++;
                }
            }
        }
        return numberOfUnUsed;
    }
}

class ClauseSet {
    int numberOfVariables;
    int numberOfClauses;
    int indexOfLastVariableOfBestBlackClause;
    Clause bestBlackClause;
    Clause[][] clauseListOrderdByLastVarIndexNeg;
    Clause[][] clauseListOrderdByLastVarIndexPos;

    public ClauseSet(int numberOfVariables,
                     int numberOfClauses,
                     int indexOfLastVariableOfBestBlackClause,
                     Clause bestBlackClause,
                     ClauseList[] clauseListOrderdByLastVarIndexNeg,
                     ClauseList[] clauseListOrderdByLastVarIndexPos){
        this.numberOfVariables = numberOfVariables;
        this.numberOfClauses = numberOfClauses;
        this.indexOfLastVariableOfBestBlackClause = indexOfLastVariableOfBestBlackClause;
        this.bestBlackClause = bestBlackClause;
        if (CSFLOC21TU.addLongTailClauses == 1) {
            addLongTailClauses(clauseListOrderdByLastVarIndexNeg, clauseListOrderdByLastVarIndexPos);
        }
        this.clauseListOrderdByLastVarIndexNeg = new Clause[numberOfVariables+1][];
        for(int i=0; i<=numberOfVariables; i++) {
            int length = clauseListOrderdByLastVarIndexNeg[i].clauseList.size();
            this.clauseListOrderdByLastVarIndexNeg[i] = new Clause[length];
            for(int j=0; j<length; j++) {
                this.clauseListOrderdByLastVarIndexNeg[i][j] =
                        clauseListOrderdByLastVarIndexNeg[i].clauseList.get(j);
            }
        }
        this.clauseListOrderdByLastVarIndexPos = new Clause[numberOfVariables+1][];
        for(int i=0; i<=numberOfVariables; i++) {
            int length = clauseListOrderdByLastVarIndexPos[i].clauseList.size();
            this.clauseListOrderdByLastVarIndexPos[i] = new Clause[length];
            for(int j=0; j<length; j++) {
                this.clauseListOrderdByLastVarIndexPos[i][j] =
                        clauseListOrderdByLastVarIndexPos[i].clauseList.get(j);
            }
        }
    }
    public void addLongTailClauses(ClauseList[] clauseListOrderdByLastVarIndexNeg,
                                   ClauseList[] clauseListOrderdByLastVarIndexPos) {
        for(int i=numberOfVariables; i>0; i--) {
            if (clauseListOrderdByLastVarIndexNeg[i].clauseList.size() == 0) continue;
            Clause b = clauseListOrderdByLastVarIndexNeg[i].clauseList.get(0);
            for(int j=0; j<clauseListOrderdByLastVarIndexPos[i].clauseList.size(); j++) {
                Clause a = clauseListOrderdByLastVarIndexPos[i].clauseList.get(j);
                Clause c = Clause.resolution_v3(a,b,a.lastVarIndex);
                if (c!=null) {
                    if (c.lastLiteral > 0) { clauseListOrderdByLastVarIndexPos[c.lastVarIndex].insert(c); }
                    else { clauseListOrderdByLastVarIndexNeg[c.lastVarIndex].insert(c); }
                }
            }
        }
        for(int i=numberOfVariables; i>0; i--) {
            if (clauseListOrderdByLastVarIndexPos[i].clauseList.size() == 0) continue;
            Clause a = clauseListOrderdByLastVarIndexPos[i].clauseList.get(0);
            for(int k=1; k<clauseListOrderdByLastVarIndexNeg[i].clauseList.size(); k++) {
                Clause b = clauseListOrderdByLastVarIndexNeg[i].clauseList.get(k);
                Clause c = Clause.resolution_v3(a,b,a.lastVarIndex);
                if (c!=null) {
                    if (c.lastLiteral > 0) { clauseListOrderdByLastVarIndexPos[c.lastVarIndex].insert(c); }
                    else { clauseListOrderdByLastVarIndexNeg[c.lastVarIndex].insert(c); }
                }
            }
        }
    }
}

abstract class ClauseList {
    ArrayList<Clause> clauseList = new ArrayList<Clause>();
    public abstract void insert(Clause c);
}

class ClauseListWithSorting extends ClauseList {
    @Override
    public void insert(Clause c) {
        int i=0;
        while(i<clauseList.size() && (clauseList.get(i).vars[0] < c.vars[0])) i++;
        clauseList.add(i, c);
    }
}

class ClauseListWithoutSorting extends ClauseList {
    @Override
    public void insert(Clause c) { clauseList.add(c); }
}

class Clause {
    boolean isEffected = false;
    int[] vars; // computed
    int[] literals;
    boolean[] isPos; // computed
    int lastLiteral;
    int lastVarIndex;
    Clause[] learnedClauses;
    /**
     * The literals must be ordered by the absolute value of its elements.
     */
    public Clause(int[] literals) {
        this.literals = literals;
        vars = new int[literals.length];
        for(int i=0; i<literals.length; i++) { vars[i] = Math.abs(literals[i]); }
        isPos = new boolean[literals.length];
        for(int i=0; i<literals.length; i++) { isPos[i] = (literals[i] > 0); }
        if (literals.length > 0) {
            lastLiteral = literals[literals.length-1];
            lastVarIndex = Math.abs(lastLiteral);
        }
        if (CSFLOC21TU.learn3ClausesForClauses == 1) learnedClauses = new Clause[3];
    }
    public void addLearnedClause(Clause c) {
        if (CSFLOC21TU.learn3ClausesForClauses == 0) return;
        learnedClauses[2] = learnedClauses[1];
        learnedClauses[1] = learnedClauses[0];
        learnedClauses[0] = c;
    }
    public boolean isBlack() {
        for(int i=0; i<literals.length; i++) { if (literals[i] > 0) return false; }
        return true;
    }
    public boolean subsumedBy(boolean[] counter) {
        CSFLOCSolver.subsumptionCandidatesChecked++;
        for(int i=0; i<literals.length-1; i++) {
            CSFLOCSolver.subsumptionLiteralChecks++;
            if (counter[vars[i]] != isPos[i]) { return false; }
        }
        CSFLOCSolver.subsumptionCandidateHits++;
        return true;
    }
    public boolean subsumedByNonLazy(boolean[] counter) {
        CSFLOCSolver.subsumptionCandidatesChecked++;
        for(int i=0; i<literals.length; i++) {
            CSFLOCSolver.subsumptionLiteralChecks++;
            if (counter[vars[i]] != isPos[i]) { return false; }
        }
        CSFLOCSolver.subsumptionCandidateHits++;
        return true;
    }
    public String toString() {
        String out = "";
        for(int i=0; i<literals.length; i++) {
            out += literals[i] + " ";
        }
        return out;
    }
    public static Clause union_v2(Clause a, Clause b, int uptoIndex) {
        int aIndex = 0;
        int bIndex = 0;
        int[] aLiterals = a.literals;
        int[] bLiterals = b.literals;
        int[] aVarIndices = a.vars;
        int[] bVarIndices = b.vars;
        int[] copyBuffer = new int[aLiterals.length + bLiterals.length-2];
        int index = 0;
        int aLit = aLiterals[aIndex];
        int bLit = bLiterals[bIndex];
        int aVar = aVarIndices[aIndex];
        int bVar = bVarIndices[bIndex];
        while(aLit != -bLit) {
            if (aLit == bLit) {
                copyBuffer[index] = aLit;
                aIndex++;
                bIndex++;
                if (aIndex == aLiterals.length || bIndex == bLiterals.length) break;
                aLit = aLiterals[aIndex];
                bLit = bLiterals[bIndex];
                aVar = aVarIndices[aIndex];
                bVar = bVarIndices[bIndex];
            }
            else if (aVar < bVar) {
                copyBuffer[index] = aLit;
                aIndex++;
                if (aIndex == aLiterals.length) break;
                aLit = aLiterals[aIndex];
                aVar = aVarIndices[aIndex];
            }
            else {
                copyBuffer[index] = bLit;
                bIndex++;
                if (bIndex == bLiterals.length) break;
                bLit = bLiterals[bIndex];
                bVar = bVarIndices[bIndex];
            }
            index++;
        }
        if (aIndex >= aLiterals.length) {
            while(bIndex < bLiterals.length-1) {
                index++;
                copyBuffer[index] = bLiterals[bIndex];
                bIndex++;
            }
        }
        else if (bIndex >= bLiterals.length) {
            while(aIndex < aLiterals.length-1) {
                index++;
                copyBuffer[index] = aLiterals[aIndex];
                aIndex++;
            }
        }
        int[] literals = new int[index];
        for(int i=0; i<index; i++) {
            literals[i] = copyBuffer[i];
        }
        return new Clause(literals);
    }
    @Override
    public boolean equals(Object o) {
        if (o == null) return false;
        Clause other = (Clause)o;
        if (literals.length != other.literals.length) return false;
        for(int i=0; i<literals.length; i++) { if (literals[i] != other.literals[i]) return false; }
        return true;
    }
    public static Clause resolution_v3(Clause a, Clause b, int uptoIndex) {
        int aIndex = 0;
        int bIndex = 0;
        int[] aLiterals = a.literals;
        int[] bLiterals = b.literals;
        int[] copyBuffer = new int[aLiterals.length + bLiterals.length];
        int index = 0;
        int aLit = aLiterals[aIndex];
        int bLit = bLiterals[bIndex];
        while(aLit != -bLit) {
            if (aLit == bLit) {
                copyBuffer[index] = aLit;
                aIndex++;
                bIndex++;
                if (aIndex == aLiterals.length || bIndex == bLiterals.length) break;
                aLit = aLiterals[aIndex];
                bLit = bLiterals[bIndex];
            }
            else if (Math.abs(aLit) < Math.abs(bLit)) {
                copyBuffer[index] = aLit;
                aIndex++;
                if (aIndex == aLiterals.length) break;
                aLit = aLiterals[aIndex];
            }
            else {
                copyBuffer[index] = bLit;
                bIndex++;
                if (bIndex == bLiterals.length) break;
                bLit = bLiterals[bIndex];
            }
            if (Math.abs(copyBuffer[index]) > uptoIndex) { System.out.println("Kell ez a sor!!!"); break; } // kell ez a sor?
            index++;
        }
        if (aIndex >= aLiterals.length) {
            while(Math.abs(copyBuffer[index]) <= uptoIndex) {
                index++;
                copyBuffer[index] = bLiterals[bIndex];
                bIndex++;
            }
        }
        else if (bIndex >= bLiterals.length) {
            while(Math.abs(copyBuffer[index]) <= uptoIndex) {
                index++;
                copyBuffer[index] = aLiterals[aIndex];
                aIndex++;
            }
        }
        if (!(aIndex == aLiterals.length-1 && bIndex == bLiterals.length-1)) {
            return null;
        }
        int[] literals = new int[index];
        for(int i=0; i<index; i++) {
            literals[i] = copyBuffer[i];
        }
        return new Clause(literals);
    }
}

class HighLevelReader {
    int numberOfVariables;
    int numberOfClauses;
    ClauseList[] clauseListOrderdByLastVarIndexNeg;
    ClauseList[] clauseListOrderdByLastVarIndexPos;
    int indexOfLastVariableOfBestBlackClause;
    Clause bestBlackClause;

    ArrayList<int[]> cs;
    int[] translate;

    public HighLevelReader(DIMACSReader dr, String variableRenamingStrategy) {
        numberOfVariables = dr.numberOfVariables;
        cs = dr.cs;
        if (CSFLOC21TU.BCP == 1) if (dr.units.size() > 0) { BCP(cs, dr.units); }

        int[] oldTranslate = null;
        int[] variablePairs = null;

        for(int i = 0; i<variableRenamingStrategy.length(); i++) {
            char c = variableRenamingStrategy.charAt(i);
            switch(c) {
                case 'b':
                case 'B':
                    translate = renameBlackClauses(cs);
                    translateVariables(cs, translate);
                    translate = productOfTranslates(translate, oldTranslate);
                    oldTranslate = translate;
                    break;
                case 'h':
                case 'H':
                    translate = renameDefiniteHornClauses(cs);
                    translateVariables(cs, translate);
                    translate = productOfTranslates(translate, oldTranslate);
                    oldTranslate = translate;
                    break;
                case 'c':
                case 'C':
                    variablePairs = createVariablePairs(cs);
                    int clim = 2; //clustering factor must be at least 2
                    if (CSFLOC21TU.clusteringFactor >= 2) clim =
                            CSFLOC21TU.clusteringFactor;
                    translate = clusterVariables(variablePairs, clim);
                    translateVariables(cs, translate);
                    translate = productOfTranslates(translate, oldTranslate);
                    oldTranslate = translate;
                    break;
                case 'w':
                case 'W':
                    translate = renameWhiteClauses(cs);
                    translateVariables(cs, translate);
                    translate = productOfTranslates(translate, oldTranslate);
                    oldTranslate = translate;
                    break;
                case 'r':
                case 'R':
                    variablePairs = createVariablePairs(cs);
                    translate = simplerVariableRenaming(variablePairs);
                    translateVariables(cs, translate);
                    translate = productOfTranslates(translate, oldTranslate);
                    oldTranslate = translate;
                    break;
                case 'i':
                case 'I':
                    translate = renameIslandClauses(cs);
                    translateVariables(cs, translate);
                    translate = productOfTranslates(translate, oldTranslate);
                    oldTranslate = translate;
                    break;
                case 's':
                case 'S':
                    translate = renameStraitClauses(cs);
                    translateVariables(cs, translate);
                    translate = productOfTranslates(translate, oldTranslate);
                    oldTranslate = translate;
                    break;
                case 't':
                case 'T':
                    translate = renameTowardTwoSATPrefix(cs);
                    translateVariables(cs, translate);
                    translate = productOfTranslates(translate, oldTranslate);
                    oldTranslate = translate;
                    break;
                case 'u':
                case 'U':
                    translate = renameTowardEarlyUnits(cs);
                    translateVariables(cs, translate);
                    translate = productOfTranslates(translate, oldTranslate);
                    oldTranslate = translate;
                    break;
                default:
                    break;
            }
        }
    }
    private void BCP(ArrayList<int[]> cs, ArrayList<Integer> units) {
        while (units.size() > 0) {
            int unit = units.get(0);
            units.remove(0);
            for(int i=cs.size()-1; i>=0; i--) {
                int[] clause = cs.get(i);
                boolean delete = false;
                int delIndex = -1;
                for(int j=0; j<clause.length; j++) {
                    if (clause[j] == unit) { delete = true; break; }
                    if (clause[j] == -unit) { delIndex = j; break; }
                }
                if (delete) { cs.remove(i); }
                if (delIndex > -1) {
                    int[] literals = new int[clause.length-1];
                    int litIndex = 0;
                    for(int j=0; j<clause.length; j++) {
                        if (j == delIndex) { continue; }
                        literals[litIndex] = clause[j];
                        litIndex++;
                    }
                    cs.set(i, literals);
                    if (literals.length == 0) {
                        System.out.println("BINGO!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
                        System.exit(-1);
                    }
                    if (literals.length == 1 && !units.contains(literals[0])) {
                        units.add(literals[0]);
                    }
                }
            }
        }
    }
    private int[] clusterVariables(int[] variablePairs, int clim) {
        int[] var_alloc = new int[numberOfVariables + 1];
        int[] clr_size = new int[numberOfVariables];
        int clr_count = 0;
        ArrayList<int[]> clusterList = new ArrayList<int[]>();
        int[] newCluster = new int[clim];
        clusterList.add(newCluster);
        for(int i=0; i<variablePairs.length; i+=2) {
            int lit_a = variablePairs[i];
            int lit_b = variablePairs[i+1];
            if (var_alloc[lit_a] == 0) { /* lit_a is not clustered */
                if (var_alloc[lit_b] == 0) { /* lit_b is not clustered */
                    /* create a new cluster with lit_a and lit_b */
                    clr_count++;
                    var_alloc[lit_a] = clr_count;
                    var_alloc[lit_b] = clr_count;
                    newCluster = new int[clim];
                    newCluster[0] = lit_a;
                    newCluster[1] = lit_b;
                    clusterList.add(newCluster);
                    clr_size[clr_count] = 2;
                } else { /* lit_b is clustered */
                    /* try to put lit_a in same cluster with lit_b */
                    int j = var_alloc[lit_b];
                    if (clr_size[j] < clim) {
                        var_alloc[lit_a] = j;
                        clusterList.get(j)[clr_size[j]] = lit_a;
                        clr_size[j]++;
                    } else { /* not possible - create another cluster with lit_a only */
                        clr_count++;
                        var_alloc[lit_a] = clr_count;
                        newCluster = new int[clim];
                        newCluster[0] = lit_a;
                        clusterList.add(newCluster);
                        clr_size[clr_count] = 1;
                    }
                }
            } else { /* lit_a is clustered */
                if (var_alloc[lit_b] == 0) { /* lit_b is not clustered */
                    /* try to put lit_b in same cluster with lit_a */
                    int j = var_alloc[lit_a];
                    if (clr_size[j] < clim) {
                        var_alloc[lit_b] = j;
                        clusterList.get(j)[clr_size[j]] = lit_b;
                        clr_size[j]++;
                    } else { /* not possible - create another cluster with lit_b only */
                        clr_count++;
                        var_alloc[lit_b] = clr_count;
                        newCluster = new int[clim];
                        newCluster[0] = lit_b;
                        clusterList.add(newCluster);
                        clr_size[clr_count] = 1;
                    }
                } else { /* lit_b is clustered */
                    /* try to merge the two clusters */
                    int ja = var_alloc[lit_a];
                    int jb = var_alloc[lit_b];
                    if ((ja != jb) && /* they are in different clusters */
                            ((clr_size[ja] + clr_size[jb]) <= clim)) { /* possible */
                        /* put all vars from cluster "jb" into cluster "ja" */
                        for (int j = 0; j <= numberOfVariables; j++) {
                            if (var_alloc[j] == jb) {
                                var_alloc[j] = ja;
                            }
                        }
                        for(int j = 0; j < clr_size[jb]; j++) {
                            clusterList.get(ja)[clr_size[ja]+j] = clusterList.get(jb)[j];
                        }
                        clr_size[ja] += clr_size[jb]; /* update size */
                        /* remove cluster "jb" by setting the size to 0 */
                        clr_size[jb] = 0;
                    } else { /* move to lover index cluster */
                        if (ja < jb && clr_size[ja] < clim) {
                            var_alloc[lit_b] = ja;
                            clusterList.get(ja)[clr_size[ja]] = lit_b;
                            clr_size[ja]++;
                            int j;
                            for(j=0; j<clr_size[jb]; j++) if (clusterList.get(jb)[j] == lit_b) break;
                            clusterList.get(jb)[j] = clusterList.get(jb)[clr_size[jb]-1];
                            clr_size[jb]--;
                        } else if (jb < ja && clr_size[jb] < clim) {
                            var_alloc[lit_a] = jb;
                            clusterList.get(jb)[clr_size[jb]] = lit_a;
                            clr_size[jb]++;
                            int j;
                            for(j=0; j<clr_size[ja]; j++) if (clusterList.get(ja)[j] == lit_a) break;
                            clusterList.get(ja)[j] = clusterList.get(ja)[clr_size[ja]-1];
                            clr_size[ja]--;
                        }
                    }
                }
            }
        }
        int[] translate = new int[numberOfVariables+1];
        int varIndex = 1;
        for (int ic = 1; ic <= clr_count; ic++) {
            int[] cluster = clusterList.get(ic);
            for(int j=0; j < clr_size[ic]; j++) {
                translate[cluster[j]] = varIndex;
                varIndex++;
            }
        }
        if (varIndex < numberOfVariables+1) {
            for(int i=1; i<translate.length; i++) {
                if (translate[i] == 0) {
                    translate[i] = varIndex;
                    varIndex++;
                }
            }
        }
        return translate;
    }
    private int[] simplerVariableRenaming(int[] variablePairs) {
        int[] translate = new int[numberOfVariables+1];
        int nextValue = 1;
        for(int i=0; i<variablePairs.length; i++) {
            int a = variablePairs[i];
            if (translate[a] == 0) {
                translate[a] = nextValue;
                nextValue++;
            }
            if (nextValue == numberOfVariables+1) break;
        }
        if (nextValue < numberOfVariables+1) {
            for(int i=1; i<translate.length; i++) {
                if (translate[i] == 0) {
                    translate[i] = nextValue;
                    nextValue++;
                }
            }
        }
        return translate;
    }
    /**
     * T strategy: Two-SAT-prefix-oriented variable renaming.
     *
     * Goal: give small indices to a greedy prefix of variables such that fixing
     * this prefix reduces every long clause (length > 2) to length at most 2.
     * For 3-SAT this means: choose a hitting set of variables that intersects
     * every 3-clause.
     *
     * Waiting-list idea:
     * - after selecting a variable v, the other variables of the still-uncovered
     *   long clauses containing v are put on a waiting list;
     * - while possible, choose a non-waiting variable with the best residual score;
     * - if every useful remaining variable is waiting-listed, the waiting list is
     *   relaxed and the best waiting-listed variable is selected;
     * - once every long clause is covered enough, append the remaining variables
     *   using the existing R-like pair-frequency order.
     */
    private int[] renameTowardTwoSATPrefix(ArrayList<int[]> cs) {
        int[] translate = new int[numberOfVariables + 1];
        boolean[] selected = new boolean[numberOfVariables + 1];
        boolean[] waiting = new boolean[numberOfVariables + 1];
        int[] selectedInClause = new int[cs.size()];
        int[] totalOccurrence = countVariableOccurrences(cs);
        int nextValue = 1;

        while (hasUncoveredLongClause(cs, selectedInClause)) {
            int best = bestTwoSATPrefixCandidate(cs, selected, waiting, selectedInClause, totalOccurrence, false);
            if (best == 0) {
                // All useful remaining variables are on the waiting list.
                // Now the waiting list must become soft, otherwise the algorithm stops too early.
                best = bestTwoSATPrefixCandidate(cs, selected, waiting, selectedInClause, totalOccurrence, true);
            }
            if (best == 0) {
                // Defensive fallback: this should only happen if there is no useful variable left.
                break;
            }
            translate[best] = nextValue;
            nextValue++;
            selected[best] = true;
            updateTwoSATPrefixState(cs, best, selected, waiting, selectedInClause);
            if (nextValue == numberOfVariables + 1) break;
        }

        // The prefix is complete. The remaining variables are less critical;
        // use the already existing R-like pair-frequency strategy as a stable fallback.
        appendRemainingByPairFrequency(cs, translate, nextValue);
        return translate;
    }

    private boolean hasUncoveredLongClause(ArrayList<int[]> cs, int[] selectedInClause) {
        for (int i = 0; i < cs.size(); i++) {
            int need = variablesNeededForTwoSAT(cs.get(i));
            if (need > 0 && selectedInClause[i] < need) return true;
        }
        return false;
    }

    private int variablesNeededForTwoSAT(int[] clause) {
        return Math.max(0, clause.length - 2);
    }

    private int[] countVariableOccurrences(ArrayList<int[]> cs) {
        int[] count = new int[numberOfVariables + 1];
        for (int[] clause : cs) {
            for (int lit : clause) {
                count[Math.abs(lit)]++;
            }
        }
        return count;
    }

    private int bestTwoSATPrefixCandidate(ArrayList<int[]> cs,
                                          boolean[] selected,
                                          boolean[] waiting,
                                          int[] selectedInClause,
                                          int[] totalOccurrence,
                                          boolean allowWaiting) {
        int bestVar = 0;
        int bestScore = 0;
        int bestTotalOccurrence = -1;
        for (int v = 1; v <= numberOfVariables; v++) {
            if (selected[v]) continue;
            if (!allowWaiting && waiting[v]) continue;
            int score = residualLongClauseScore(cs, selectedInClause, v);
            if (score == 0) continue;
            if (score > bestScore ||
                    (score == bestScore && totalOccurrence[v] > bestTotalOccurrence) ||
                    (score == bestScore && totalOccurrence[v] == bestTotalOccurrence && v < bestVar)) {
                bestVar = v;
                bestScore = score;
                bestTotalOccurrence = totalOccurrence[v];
            }
        }
        return bestVar;
    }

    private int residualLongClauseScore(ArrayList<int[]> cs, int[] selectedInClause, int variable) {
        int score = 0;
        for (int i = 0; i < cs.size(); i++) {
            int[] clause = cs.get(i);
            int need = variablesNeededForTwoSAT(clause);
            if (need == 0 || selectedInClause[i] >= need) continue;
            if (containsVariable(clause, variable)) {
                // The +1 makes long clauses slightly more urgent when more selected
                // variables are still needed from them.
                score += 1 + (need - selectedInClause[i] - 1);
            }
        }
        return score;
    }

    private void updateTwoSATPrefixState(ArrayList<int[]> cs,
                                         int selectedVariable,
                                         boolean[] selected,
                                         boolean[] waiting,
                                         int[] selectedInClause) {
        waiting[selectedVariable] = false;
        for (int i = 0; i < cs.size(); i++) {
            int[] clause = cs.get(i);
            int need = variablesNeededForTwoSAT(clause);
            if (need == 0 || selectedInClause[i] >= need) continue;
            if (!containsVariable(clause, selectedVariable)) continue;

            selectedInClause[i]++;
            for (int lit : clause) {
                int v = Math.abs(lit);
                if (!selected[v]) waiting[v] = true;
            }
        }
    }

    private boolean containsVariable(int[] clause, int variable) {
        for (int lit : clause) {
            if (Math.abs(lit) == variable) return true;
        }
        return false;
    }

    private void appendRemainingByPairFrequency(ArrayList<int[]> cs, int[] translate, int nextValue) {
        int[] pairOrder = simplerVariableRenaming(createVariablePairs(cs));
        int[] originalByPairRank = new int[numberOfVariables + 1];
        for (int originalVar = 1; originalVar <= numberOfVariables; originalVar++) {
            originalByPairRank[pairOrder[originalVar]] = originalVar;
        }
        for (int rank = 1; rank <= numberOfVariables && nextValue <= numberOfVariables; rank++) {
            int originalVar = originalByPairRank[rank];
            if (originalVar != 0 && translate[originalVar] == 0) {
                translate[originalVar] = nextValue;
                nextValue++;
            }
        }
        for (int originalVar = 1; originalVar <= numberOfVariables && nextValue <= numberOfVariables; originalVar++) {
            if (translate[originalVar] == 0) {
                translate[originalVar] = nextValue;
                nextValue++;
            }
        }
    }
    //%%%%%%%%
    /**
     * U-lite strategy: low-cost unit-oriented variable renaming.
     *
     * Variables are visited once in descending clause-frequency order. If a
     * variable is already the sole unselected variable of at least one clause,
     * it is deferred to the high-index suffix. No variable-pair table is built,
     * no complete waiting list is recomputed, and no full clause scan is done
     * after each assignment.
     *
     * With L distinct variable occurrences, n variables, and m clauses, the
     * preprocessing cost is O(L + n + m) time and O(L + n + m) memory.
     */
    private int[] renameTowardEarlyUnits(ArrayList<int[]> cs) {
        int[] translate = new int[numberOfVariables + 1];
        if (numberOfVariables == 0) return translate;

        UnitLiteData data = buildUnitLiteData(cs);
        int[] order = unitLiteFrequencyOrder(data.frequency);
        boolean[] selected = new boolean[numberOfVariables + 1];
        int[] deferred = new int[numberOfVariables];
        int deferredCount = 0;
        int nextValue = 1;

        /*
         * One forward pass. Waiting is monotone for an unselected variable,
         * therefore a variable deferred once never has to be reconsidered.
         */
        for (int variable : order) {
            if (data.waitingCount[variable] > 0) {
                deferred[deferredCount++] = variable;
            } else {
                nextValue = assignUnitLiteVariable(
                        variable,
                        translate,
                        selected,
                        data,
                        nextValue);
            }
        }

        /* Append the deferred unit-producing variables as a suffix. */
        for (int i = 0; i < deferredCount; i++) {
            translate[deferred[i]] = nextValue++;
        }

        return translate;
    }

    /**
     * Builds a compact variable-to-clause incidence index. Repeated literals
     * of the same variable inside one clause are counted only once.
     */
    private UnitLiteData buildUnitLiteData(ArrayList<int[]> cs) {
        int clauseCount = cs.size();
        int[] remaining = new int[clauseCount];
        int[] frequency = new int[numberOfVariables + 1];
        int[] waitingCount = new int[numberOfVariables + 1];
        int[] seen = new int[numberOfVariables + 1];
        int stamp = 1;

        /* First pass: distinct clause sizes and clause frequencies. */
        for (int clauseIndex = 0; clauseIndex < clauseCount; clauseIndex++) {
            if (stamp == Integer.MAX_VALUE) {
                Arrays.fill(seen, 0);
                stamp = 1;
            }

            int distinct = 0;
            int soleVariable = 0;

            for (int literal : cs.get(clauseIndex)) {
                int variable = Math.abs(literal);
                if (variable < 1
                        || variable > numberOfVariables
                        || seen[variable] == stamp) {
                    continue;
                }

                seen[variable] = stamp;
                distinct++;
                soleVariable = variable;
                frequency[variable]++;
            }

            remaining[clauseIndex] = distinct;
            if (distinct == 1) {
                waitingCount[soleVariable]++;
            }
            stamp++;
        }

        /* Prefix offsets for the compressed incidence array. */
        int[] occurrenceStart = new int[numberOfVariables + 2];
        for (int variable = 1;
             variable <= numberOfVariables;
             variable++) {
            occurrenceStart[variable + 1] =
                    occurrenceStart[variable] + frequency[variable];
        }

        int[] clauseIndices =
                new int[occurrenceStart[numberOfVariables + 1]];
        int[] cursor =
                Arrays.copyOf(occurrenceStart, occurrenceStart.length);

        Arrays.fill(seen, 0);
        stamp = 1;

        /* Second pass: fill variable -> incident clause indices. */
        for (int clauseIndex = 0; clauseIndex < clauseCount; clauseIndex++) {
            if (stamp == Integer.MAX_VALUE) {
                Arrays.fill(seen, 0);
                stamp = 1;
            }

            for (int literal : cs.get(clauseIndex)) {
                int variable = Math.abs(literal);
                if (variable < 1
                        || variable > numberOfVariables
                        || seen[variable] == stamp) {
                    continue;
                }

                seen[variable] = stamp;
                clauseIndices[cursor[variable]++] = clauseIndex;
            }
            stamp++;
        }

        return new UnitLiteData(
                cs,
                remaining,
                frequency,
                waitingCount,
                occurrenceStart,
                clauseIndices);
    }

    /**
     * Counting-sort order: descending clause frequency, then ascending
     * original variable index.
     */
    private int[] unitLiteFrequencyOrder(int[] frequency) {
        int maxFrequency = 0;
        for (int variable = 1;
             variable <= numberOfVariables;
             variable++) {
            if (frequency[variable] > maxFrequency) {
                maxFrequency = frequency[variable];
            }
        }

        int[] bucketSize = new int[maxFrequency + 1];
        for (int variable = 1;
             variable <= numberOfVariables;
             variable++) {
            bucketSize[frequency[variable]]++;
        }

        int[] bucketStart = new int[maxFrequency + 1];
        int position = 0;
        for (int frequencyValue = maxFrequency;
             frequencyValue >= 0;
             frequencyValue--) {
            bucketStart[frequencyValue] = position;
            position += bucketSize[frequencyValue];
        }

        int[] cursor = Arrays.copyOf(bucketStart, bucketStart.length);
        int[] order = new int[numberOfVariables];

        for (int variable = 1;
             variable <= numberOfVariables;
             variable++) {
            order[cursor[frequency[variable]]++] = variable;
        }

        return order;
    }

    /**
     * Assigns one non-waiting variable and updates only clauses containing it.
     * Every clause is scanned at most once, on its distinct 2 -> 1 transition.
     */
    private int assignUnitLiteVariable(int variable,
                                       int[] translate,
                                       boolean[] selected,
                                       UnitLiteData data,
                                       int nextValue) {
        selected[variable] = true;
        translate[variable] = nextValue++;

        for (int occurrence = data.occurrenceStart[variable];
             occurrence < data.occurrenceStart[variable + 1];
             occurrence++) {

            int clauseIndex = data.clauseIndices[occurrence];
            int before = data.remaining[clauseIndex];
            if (before <= 0) continue;

            data.remaining[clauseIndex] = before - 1;

            if (before == 2) {
                int last = firstUnselectedUnitLiteVariable(
                        data.clauses.get(clauseIndex), selected);
                if (last != 0) {
                    data.waitingCount[last]++;
                }
            }
        }

        return nextValue;
    }

    private int firstUnselectedUnitLiteVariable(int[] clause,
                                                boolean[] selected) {
        for (int literal : clause) {
            int variable = Math.abs(literal);
            if (variable >= 1
                    && variable <= numberOfVariables
                    && !selected[variable]) {
                return variable;
            }
        }
        return 0;
    }

    private static final class UnitLiteData {
        final ArrayList<int[]> clauses;
        final int[] remaining;
        final int[] frequency;
        final int[] waitingCount;
        final int[] occurrenceStart;
        final int[] clauseIndices;

        UnitLiteData(ArrayList<int[]> clauses,
                     int[] remaining,
                     int[] frequency,
                     int[] waitingCount,
                     int[] occurrenceStart,
                     int[] clauseIndices) {
            this.clauses = clauses;
            this.remaining = remaining;
            this.frequency = frequency;
            this.waitingCount = waitingCount;
            this.occurrenceStart = occurrenceStart;
            this.clauseIndices = clauseIndices;
        }
    }
    //%%%%%%%%
    private int[] renameWhiteClauses(ArrayList<int[]> cs) {
        int varIndex = 1;
        int[] translate = new int[numberOfVariables+1];
        for(int i=0; i<cs.size(); i++) {
            int[] source = cs.get(i);
            boolean allPositive = true;
            for(int j=0; j<source.length; j++) { if (source[j] != Math.abs(source[j])) { allPositive = false; break; } }
            if (!allPositive) continue;
            for(int j=0; j<source.length; j++) {
                if (translate[source[j]]==0) {
                    translate[source[j]] = varIndex;
                    varIndex++;
                    if (varIndex == numberOfVariables+1) break;
                }
            }
            if (varIndex == numberOfVariables+1) break;
        }
        if (varIndex != numberOfVariables+1) {
            for(int i=varIndex; i<=numberOfVariables; i++) {
                int j = 1; while(translate[j]!=0) j++;
                translate[j] = i;
            }
        }
        return translate;
    }
    private int[] renameBlackClauses(ArrayList<int[]> cs) {
        int varIndex = 1;
        int[] translate = new int[numberOfVariables+1];
        for(int i=0; i<cs.size(); i++) {
            int[] source = cs.get(i);
            boolean allNegative = true;
            for(int j=0; j<source.length; j++) { if (source[j] == Math.abs(source[j])) { allNegative = false; break; } }
            if (!allNegative) continue;
            for(int j=0; j<source.length; j++) {
                int index = Math.abs(source[j]);
                if (translate[index]==0) {
                    translate[index] = varIndex;
                    varIndex++;
                    if (varIndex == numberOfVariables+1) break;
                }
            }
            if (varIndex == numberOfVariables+1) break;
        }
        if (varIndex != numberOfVariables+1) {
            for(int i=varIndex; i<=numberOfVariables; i++) {
                int j = 1; while(translate[j]!=0) j++;
                translate[j] = i;
            }
        }
        return translate;
    }
    private int[] renameDefiniteHornClauses(ArrayList<int[]> cs) {
        int varIndex = 1;
        int[] translate = new int[numberOfVariables+1];
        for(int i=0; i<cs.size(); i++) {
            int[] source = cs.get(i);
            int numberOfPoz = 0;
            for(int j = 0; j < source.length; j++) {
                if(source[j] == Math.abs(source[j])) { numberOfPoz++; }
            }
            if(numberOfPoz!=1) continue;
            int numberOfNotRenamedLiterals = 0;
            for(int j = 0; j < source.length; j++) {
                if(translate[Math.abs(source[j])] == 0) { numberOfNotRenamedLiterals++; }
            }
            if(numberOfNotRenamedLiterals != source.length) continue;
            for(int j = 0; j < source.length; j++) {
                if(translate[Math.abs(source[j])] == 0) {
                    translate[Math.abs(source[j])] = varIndex;
                    varIndex++;
                    if(varIndex == numberOfVariables + 1) break;
                }
            }
            if(varIndex == numberOfVariables + 1) break;
        }
        if(varIndex != numberOfVariables + 1) {
            for (int i = varIndex; i<=numberOfVariables; i++) {
                int j = 1;
                while(translate[j] != 0) j++;
                translate[j] = i;
            }
        }
        return translate;
    }
    private int[] renameIslandClauses(ArrayList<int[]> cs) {
        int varIndex = 1;
        int[] translate = new int[numberOfVariables+1];
        for(int i=0; i<cs.size(); i++) {
            int[] source = cs.get(i);
            int numberOfPoz = 0;
            int posIndex = 0;
            for(int j=0; j<source.length; j++) { if (source[j] == Math.abs(source[j])) { numberOfPoz++; posIndex = j; } }
            if (numberOfPoz!=1) continue;
            for(int j=0; j<source.length; j++) {
                if (j == posIndex) continue;
                int index = Math.abs(source[j]);
                if (translate[index]==0) {
                    translate[index] = varIndex;
                    varIndex++;
                    if (varIndex == numberOfVariables+1) break;
                }
            }
            int index = Math.abs(source[posIndex]);
            if (translate[index]==0) {
                translate[index] = varIndex;
                varIndex++;
            }
            if (varIndex == numberOfVariables+1) break;
        }
        if (varIndex != numberOfVariables+1) {
            for(int i=varIndex; i<=numberOfVariables; i++) {
                int j = 1; while(translate[j]!=0) j++;
                translate[j] = i;
            }
        }
        return translate;
    }
    private int[] renameStraitClauses(ArrayList<int[]> cs) {
        int varIndex = 1;
        int[] translate = new int[numberOfVariables+1];
        for(int i=0; i<cs.size(); i++) {
            int[] source = cs.get(i);
            int numberOfNeg = 0;
            int negIndex = 0;
            for(int j=0; j<source.length; j++) { if (source[j] != Math.abs(source[j])) { numberOfNeg++; negIndex = j; } }
            if (numberOfNeg!=1) continue;
            int index = Math.abs(source[negIndex]);
            if (translate[index]==0) {
                translate[index] = varIndex;
                varIndex++;
            }
            for(int j=0; j<source.length; j++) {
                if (j == negIndex) continue;
                int index2 = Math.abs(source[j]);
                if (translate[index2]==0) {
                    translate[index2] = varIndex;
                    varIndex++;
                    if (varIndex == numberOfVariables+1) break;
                }
            }
            if (varIndex == numberOfVariables+1) break;
        }
        if (varIndex != numberOfVariables+1) {
            for(int i=varIndex; i<=numberOfVariables; i++) {
                int j = 1; while(translate[j]!=0) j++;
                translate[j] = i;
            }
        }
        return translate;
    }
    private int[] createVariablePairs(ArrayList<int[]> cs) {
        HashMap<Int2, Integer> count2 = new HashMap<>();
        int bestCount = 1;
        for(int i=0; i<cs.size(); i++) {
            int[] source = cs.get(i);
            if (source.length > 12) continue;
            int[] clause = new int[source.length];
            for(int j=0; j<source.length; j++) {
                int variable = Math.abs(source[j]);
                clause[j] = variable;
            }
            if (clause.length == 1) {
                continue;
            }
            for(int j=0; j<clause.length-1; j++) {
                for(int k=j+1; k<clause.length; k++) {
                    Int2 key2 = new Int2(clause[j], clause[k]);
                    bestCount = increaseKey2(count2, key2, bestCount);
                }
            }
        }
        Set<Int2> keys = count2.keySet();
        int[] counts = new int[bestCount];
        for(Int2 key : keys) {
            int count = count2.get(key);
            counts[bestCount-count]++;
        }
        int[] variablePairs = new int[keys.size()*2];
        int[] indeces = new int[bestCount];
        indeces[0] = 0;
        for(int i=1; i<bestCount; i++) { indeces[i] = indeces[i-1] + counts[i-1]*2; }
        for(Int2 key : keys) {
            int count = count2.get(key);
            int i = indeces[bestCount-count];
            variablePairs[i] = key.getA();
            variablePairs[i+1] = key.getB();
            indeces[bestCount-count] += 2;
        }
        return variablePairs;
    }
    private int increaseKey2(HashMap<Int2, Integer> count2, Int2 key2, int bestCount) {
        if (count2.containsKey(key2)) {
            Integer count = count2.get(key2);
            count++;
            count2.put(key2, count);
            if (count > bestCount) bestCount = count;
        }
        else { count2.put(key2, 1); }
        return bestCount;
    }
    private void translateVariables(ArrayList<int[]> cs, int[] translate) {
        for(int i=0; i<cs.size(); i++) {
            int[] clause = cs.get(i);
            for(int j=0; j<clause.length; j++) {
                int lit = clause[j];
                int var = translate[Math.abs(lit)];
                if (var <= 0) {System.err.println("Unexpected value in translate table. There must be a bug!"); System.exit(-1); }
                if (lit > 0) clause[j] = var; else clause[j] =-var;
            }
        }
    }
    private int[] productOfTranslates(int[] translate, int[] oldTranslate) {
        if (oldTranslate == null) return translate;
        int[] product = new int[translate.length];
        for(int i=0; i<product.length; i++) {
            product[i] = translate[oldTranslate[i]];
        }
        return product;
    }
    private void orderLiterals(ArrayList<int[]> cs) {
        for(int i=0; i<cs.size(); i++) {
            int[] clause = cs.get(i);
            int j = 1;
            int flag = 1;
            while (flag != 0) {
                flag = 0;
                for(int k = 0; k<clause.length-j; k++) {
                    if (Math.abs(clause[k]) > Math.abs(clause[k+1])) {
                        int temp = clause[k];
                        clause[k] = clause[k+1];
                        clause[k+1] = temp;
                        flag = 1;
                    }
                }
                j++;
            }
        }
    }
    private void initDataStructureWithSorting() {
        clauseListOrderdByLastVarIndexNeg = new ClauseList[numberOfVariables+1];
        clauseListOrderdByLastVarIndexPos = new ClauseList[numberOfVariables+1];
        for(int i=0; i<clauseListOrderdByLastVarIndexPos.length; i++) {
            clauseListOrderdByLastVarIndexPos[i] = new ClauseListWithSorting();
        }
        for(int i=0; i<clauseListOrderdByLastVarIndexNeg.length; i++) {
            clauseListOrderdByLastVarIndexNeg[i] = new ClauseListWithSorting();
        }
        indexOfLastVariableOfBestBlackClause = numberOfVariables + 1;
    }
    private void initDataStructureWithoutSorting() {
        clauseListOrderdByLastVarIndexNeg = new ClauseList[numberOfVariables+1];
        clauseListOrderdByLastVarIndexPos = new ClauseList[numberOfVariables+1];
        for(int i=0; i<clauseListOrderdByLastVarIndexPos.length; i++) {
            clauseListOrderdByLastVarIndexPos[i] = new ClauseListWithoutSorting();
        }
        for(int i=0; i<clauseListOrderdByLastVarIndexNeg.length; i++) {
            clauseListOrderdByLastVarIndexNeg[i] = new ClauseListWithoutSorting();
        }
        indexOfLastVariableOfBestBlackClause = numberOfVariables + 1;
    }
    private void fillDataStructure() {
        for(int i=0; i<cs.size(); i++) {
            Clause newClause = new Clause(cs.get(i));
            if (newClause.lastLiteral > 0) { clauseListOrderdByLastVarIndexPos[newClause.lastVarIndex].insert(newClause); }
            else { clauseListOrderdByLastVarIndexNeg[newClause.lastVarIndex].insert(newClause); }
            if (newClause.isBlack() && newClause.lastVarIndex < indexOfLastVariableOfBestBlackClause) {
                indexOfLastVariableOfBestBlackClause = newClause.lastVarIndex;
                bestBlackClause = newClause;
            }
        }
        numberOfClauses = cs.size();
    }
    /* API */
    public ClauseSet getClauseSet() {
        orderLiterals(cs);
        if (CSFLOC21TU.clauseListWithSorting == 1) {
            initDataStructureWithSorting();
        }
        else {
            initDataStructureWithoutSorting();
        }
        fillDataStructure();
        return new ClauseSet(numberOfVariables,
                numberOfClauses,
                indexOfLastVariableOfBestBlackClause,
                bestBlackClause,
                clauseListOrderdByLastVarIndexNeg,
                clauseListOrderdByLastVarIndexPos);
    }
    public ArrayList<int[]> getClauseSetAsArrayListOfIntArray() { return cs; }

}

class DIMACSReader {
    int numberOfVariables;
    private int numberOfClauses;    // not used
    ArrayList<int[]> cs = new ArrayList<>();
    ArrayList<Integer> units = new ArrayList<>();
    int[] copyBuffer;
    public DIMACSReader(String fileName) {
        try {
            BufferedReader file = new BufferedReader(new FileReader(fileName));
            String clause = file.readLine();
            while (clause.charAt(0) != 'p') {
                clause = file.readLine();
            }
            readPLine(clause);
            initDataStructure();
            clause = file.readLine();
            while (clause != null) {
                addCNFClause(clause);
                clause = file.readLine();
            }
            file.close();
        } catch (IOException e) { System.out.println(e); System.exit(-1); }
    }
    private void readPLine(String cnfClause) {
        int i1 = 6;
        int i2 = cnfClause.indexOf(" ", i1);
        numberOfVariables = Integer.parseInt(cnfClause.substring(i1, i2));
        if (CSFLOC21TU.useExtendedResolution > 0)
            numberOfVariables += CSFLOC21TU.useExtendedResolution;
    }
    private void initDataStructure() {
        copyBuffer = new int[numberOfVariables];
    }
    private void addCNFClause(String cnfClause) {
        if (cnfClause.length() == 0 ||
                cnfClause.charAt(0) == '0' ||
                cnfClause.charAt(0) == 'c' ||
                cnfClause.charAt(0) == '%') { return; }
        int i = 0;
        int i1 = 0;
        cnfClause = cnfClause.replace("\t", " ");
        while(i1 < cnfClause.length())  {
            int i2 = cnfClause.indexOf(" ", i1);
            if (i1 == i2) { i1++; continue; }
            if (i2 == -1) break;
            String lit = cnfClause.substring(i1, i2);
            i1 = i2;
            int literal = Integer.parseInt(lit);
            if (literal == 0) break;
            if (CSFLOC21TU.doInvert) literal *= -1;
            if (CSFLOC21TU.useExtendedResolution > 0) {
                copyBuffer[i] = literal > 0 ? literal + CSFLOC21TU.useExtendedResolution :
                        literal - CSFLOC21TU.useExtendedResolution;
                i++;
            }
            else copyBuffer[i] = literal;
            i++;
        }
        int[] literals = new int[i];
        for(int index=0; index<i; index++) {
            literals[index] = copyBuffer[index];
        }
        cs.add(literals);
        if (literals.length == 1 && !units.contains(literals[0])) {
            units.add(literals[0]);
        }
    }
    public void addExtendedResolutionClauses(int numberOfNewVariables) {
        int bb = 2;
        int[] clauseA = {-1, bb};
        int[] clauseB = {1, -bb};
        cs.add(clauseA);
        cs.add(clauseB);
    }
    public void addExtraUnits(int[] extraUnits) {
        for(int extraUnit : extraUnits){
            int[] clause = {extraUnit};
            cs.add(clause);
        }
    }
}

class Int2 {
    private int a, b;
    public int getA() { return a; }
    public int getB() { return b; }
    public Int2(int a, int b) {
        int temp;
        if (a>b) { temp = a; a = b; b = temp; }
        this.a = a; this.b = b;
    }
    @Override
    public boolean equals(Object o) {
        Int2 other = (Int2)o;
        return this.a == other.a && this.b == other.b;
    }
    @Override
    public int hashCode() {
        return a * 11 + b * 3;
    }
    @Override
    public String toString() {
        String s = "(";
        s += a;
        s += ", ";
        s += b;
        s += ")";
        return s;
    }
}

class CheckSolution {
    public static boolean SimpleCheckSolution(ArrayList<int[]> cs, boolean[] solution) {
        for(int i=0; i<cs.size(); i++) {
            int[] clause = cs.get(i);
            boolean satisfied = false;
            for(int j=0; j<clause.length; j++) {
                int lit = clause[j];
                int var = Math.abs(lit);
                if(solution[var] == (lit>0)) { satisfied = true; break; }
            }
            if (!satisfied) return false;
        }
        return true;
    }
}