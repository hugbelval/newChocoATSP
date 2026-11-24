package org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangian;

import org.chocosolver.solver.exception.ContradictionException;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.*;

class EdmondsAlgorithmTest {

    private static final double EPS = 1e-9;
    private static final double BIG = 100; // "large but feasible" entry used to fill matrices

    /** Cycle-size limits under test (the last one, n, is resolved per instance). */
    private static final int[] SMALL_LIMITS = {2, 3, 4};

    // ---------- helpers ----------

    private static double lowerBound(PropFusionAsymUndirectedGraphVar.Result r) {
        return r.lb;
    }

    private static BitSet all(int n) {
        BitSet bs = new BitSet(n);
        bs.set(0, n);
        return bs;
    }

    /** Runs the algorithm with a limit on the size of the cycles that get penalized. */
    private static double run(double[][] m, int[] matching, int tailleMaxCycles) throws ContradictionException {
        int n = m.length;
        return lowerBound(EdmondsAlgorithm.fullEdmondsSCC(m, matching, all(n), all(n), tailleMaxCycles));
    }


    private static double runIncreasing(double[][] m, int[] matching) throws ContradictionException {
        int n = m.length;
        return 0;
        //return lowerBound(EdmondsAlgorithm.increasingEdmonds(m, matching, all(n), all(n)));
    }

    /** Unlimited version: tailleMaxCycles = n, i.e. every cycle is penalized. */
    private static double run(double[][] m, int[] matching) throws ContradictionException {
        return run(m, matching, m.length);
    }

    private static double[][] copy(double[][] m) {
        double[][] c = new double[m.length][];
        for (int i = 0; i < m.length; i++) c[i] = m[i].clone();
        return c;
    }

    /** Min-cost 1-arborescence rooted at 0 by exhaustive search (small n only). */
    private static double bruteForceArborescence(double[][] m) {
        int n = m.length;
        int[] parent = new int[n];
        return bruteRec(m, parent, 1, n);
    }

    private static double bruteRec(double[][] m, int[] parent, int v, int n) {
        if (v == n) {
            for (int u = 1; u < n; u++) {            // every node must reach the root
                int x = u, steps = 0;
                while (x != 0 && steps <= n) { x = parent[x]; steps++; }
                if (x != 0) return Double.POSITIVE_INFINITY;
            }
            double c = 0;
            for (int u = 1; u < n; u++) c += m[parent[u]][u];
            return c;
        }
        double best = Double.POSITIVE_INFINITY;
        for (int p = 0; p < n; p++) {
            if (p == v) continue;
            parent[v] = p;
            best = Math.min(best, bruteRec(m, parent, v + 1, n));
        }
        return best;
    }

    // ---------- tests with no effective limit (tailleMaxCycles = n) ----------

    @Test
    void singleNode_lbIsZero() throws ContradictionException {
        double[][] m = {{0}};
        for (int k : new int[]{2, 3, 4, 1}) {
            assertEquals(0, run(copy(m), new int[]{0}, k), EPS);
        }
    }

    @Test
    void alreadyAnArborescence_noPenalty() throws ContradictionException {
        // 0->1, 1->2 are zero arcs; 2->0 enters the root and is ignored
        double[][] base = {
                {BIG, 0, BIG},
                {BIG, BIG, 0},
                {0, BIG, BIG}
        };
        for (int k : new int[]{2, 3, 4, base.length}) {
            double[][] m = copy(base);
            assertEquals(0, run(m, new int[]{1, 2, 0}, k), EPS, "k=" + k);
            assertArrayEquals(base, m, "k=" + k); // matrix untouched
        }
    }

    @Test
    void singleSourceCycle_penalizedByCheapestEntry() throws ContradictionException {
        // root self-assigned; cycle 1->2->3->1 (size 3) has no incoming arc from outside
        double[][] m = {
                {0, 5, 3, 7},
                {BIG, BIG, 0, BIG},
                {BIG, BIG, BIG, 0},
                {BIG, 0, BIG, BIG}
        };
        double lb = run(m, new int[]{0, 2, 3, 1});

        assertEquals(3, lb, EPS);                       // cheapest entry into {1,2,3}
        assertArrayEquals(new double[]{0, 2, 0, 4}, m[0], EPS);
    }

    @Test
    void forbiddenArcsAreIgnoredWhenAFeasibleEntryExists() throws ContradictionException {
        double bigValue = PropFusionAsymUndirectedGraphVar.bigValue;
        double[][] m = {
                {0, bigValue, 3},
                {BIG, BIG, 0},
                {BIG, 0, BIG}
        };
        assertEquals(3, run(m, new int[]{0, 2, 1}), EPS);
    }

    @Test
    void twoIndependentSourceCycles_penaltiesAdd() throws ContradictionException {
        // cycles {1,2} and {3,4}; only the root can enter them
        double[][] m = {
                {0, 4, 6, 2, 9},
                {BIG, BIG, 0, 50, 50},
                {BIG, 0, BIG, 50, 50},
                {BIG, 50, 50, BIG, 0},
                {BIG, 50, 50, 0, BIG}
        };
        double lb = run(m, new int[]{0, 2, 1, 4, 3});

        assertEquals(4 + 2, lb, EPS);
        assertArrayEquals(new double[]{0, 0, 2, 0, 7}, m[0], EPS);
    }

    @Test
    void cascade_requiresSeveralIterations() throws ContradictionException {
        // X={1,2}, Y={3,4}. Cheap arcs 3->1 (1) and 2->3 (1) merge X and Y into one
        // SCC, which then needs a further penalty (4) from the root.
        double[][] m = cascadeMatrix();
        double lb = run(m, new int[]{0, 2, 1, 4, 3});

        assertEquals(1 + 1 + 4, lb, EPS);
        double[][] expected = {
                {0, 5, 5, 0, 1},
                {BIG, BIG, 0, 49, 49},
                {BIG, 0, BIG, 0, 49},
                {BIG, 0, 99, BIG, 0},
                {BIG, 19, 99, 0, BIG}
        };
        assertArrayEquals(expected, m);
    }

    @Test
    void noWayToEnterACycle_throwsContradiction() {
        double bigValue = PropFusionAsymUndirectedGraphVar.bigValue;
        double[][] m = {
                {0, bigValue, bigValue},
                {BIG, BIG, 0},
                {BIG, 0, BIG}
        };
        assertThrows(ContradictionException.class, () -> run(m, new int[]{0, 2, 1}));
    }

    @Test
    void lowerBoundIsNeverNegative() throws ContradictionException {
        double[][] m = {
                {0, 5, 3, 7},
                {BIG, BIG, 0, BIG},
                {BIG, BIG, BIG, 0},
                {BIG, 0, BIG, BIG}
        };
        assertTrue(run(m, new int[]{0, 2, 3, 1}) >= 0);
    }

    // ---------- tests on tailleMaxCycles ----------

    private static double[][] cascadeMatrix() {
        return new double[][]{
                {0, 10, 10, 5, 6},
                {BIG, BIG, 0, 50, 50},
                {BIG, 0, BIG, 1, 50},
                {BIG, 1, BIG, BIG, 0},
                {BIG, 20, BIG, 0, BIG}
        };
    }

    private static double[][] singleCycle3Matrix() {
        return new double[][]{
                {0, 5, 3, 7},
                {BIG, BIG, 0, BIG},
                {BIG, BIG, BIG, 0},
                {BIG, 0, BIG, BIG}
        };
    }

    private static double[][] twoCycles2Matrix() {
        return new double[][]{
                {0, 4, 6, 2, 9},
                {BIG, BIG, 0, 50, 50},
                {BIG, 0, BIG, 50, 50},
                {BIG, 50, 50, BIG, 0},
                {BIG, 50, 50, 0, BIG}
        };
    }

    /** One cycle of size 3: ignored for k=2 (matrix untouched, lb=0), penalized for k=3, 4, n. */
    @Test
    void singleCycleOfSize3_onlyPenalizedWhenLimitIsAtLeast3() throws ContradictionException {
        int[] matching = {0, 2, 3, 1};

        double[][] m2 = singleCycle3Matrix();
        assertEquals(0, run(m2, matching, 2), EPS);
        assertArrayEquals(singleCycle3Matrix(), m2);    // nothing was modified

        for (int k : new int[]{3, 4}) {
            double[][] m = singleCycle3Matrix();
            assertEquals(3, run(m, matching, k), EPS, "k=" + k);
            assertArrayEquals(new double[]{0, 2, 0, 4}, m[0], EPS, "k=" + k);
        }

    }

    /** Two independent cycles of size 2: every limit >= 2 gives the full penalty. */
    @Test
    void twoCyclesOfSize2_sameResultForAllLimits() throws ContradictionException {
        int[] matching = {0, 2, 1, 4, 3};
        for (int k : new int[]{2, 3, 4, 5}) {
            double[][] m = twoCycles2Matrix();
            assertEquals(6, run(m, matching, k), EPS, "k=" + k);
            assertArrayEquals(new double[]{0, 0, 2, 0, 7}, m[0], EPS, "k=" + k);
        }
    }

    /**
     * Cascade: the two initial cycles have size 2 (penalized for every k >= 2) but they merge
     * into an SCC of size 4. That one is penalized only if k >= 4.
     */
    @Test
    void cascade_mergedSccOfSize4_stoppedByLimits2And3() throws ContradictionException {
        int[] matching = {0, 2, 1, 4, 3};

        // state after the first iteration only (X and Y penalized by 1 each)
        double[][] afterFirstIteration = {
                {0, 9, 9, 4, 5},
                {BIG, BIG, 0, 49, 49},
                {BIG, 0, BIG, 0, 49},
                {BIG, 0, 99, BIG, 0},
                {BIG, 19, 99, 0, BIG}
        };

        for (int k : new int[]{2, 3}) {
            double[][] m = cascadeMatrix();
            assertEquals(1 + 1, run(m, matching, k), EPS, "k=" + k);
            assertArrayEquals(afterFirstIteration, m, "k=" + k);
        }

        double[][] expectedFull = {
                {0, 5, 5, 0, 1},
                {BIG, BIG, 0, 49, 49},
                {BIG, 0, BIG, 0, 49},
                {BIG, 0, 99, BIG, 0},
                {BIG, 19, 99, 0, BIG}
        };
        for (int k : new int[]{4, 5}) {   // 4 and n
            double[][] m = cascadeMatrix();
            assertEquals(1 + 1 + 4, run(m, matching, k), EPS, "k=" + k);
            assertArrayEquals(expectedFull, m, "k=" + k);
        }
    }

    /** A cycle that cannot be entered is a contradiction only if its size is within the limit. */
    @Test
    void unreachableCycle_contradictionOnlyWithinLimit() throws ContradictionException {
        double bigValue = PropFusionAsymUndirectedGraphVar.bigValue;
        double[][] base = {
                {0, bigValue, bigValue, bigValue},
                {BIG, BIG, 0, BIG},
                {BIG, BIG, BIG, 0},
                {BIG, 0, BIG, BIG}
        };
        int[] matching = {0, 2, 3, 1};   // cycle of size 3, no way in

        assertDoesNotThrow(() -> run(copy(base), matching, 2));   // too big: ignored
        for (int k : new int[]{3, 4}) {
            assertThrows(ContradictionException.class, () -> run(copy(base), matching, k), "k=" + k);
        }
    }

    // ---------- property tests ----------

    /**
     * Property test: on a column-reduced matrix whose matching entries are the zeros,
     * the returned lb must equal the cost of the optimal 1-arborescence (brute force)
     * when there is no effective limit (k = n).
     */
    @Test
    void matchesBruteForceOnRandomInstances() throws ContradictionException {
        Random rnd = new Random(42);
        for (int iter = 0; iter < 300; iter++) {
            int n = 3 + rnd.nextInt(4); // 3..6
            int[] matching = randomMatching(n, rnd);
            double[][] m = randomReducedMatrix(n, matching, rnd);

            double expected = bruteForceArborescence(m);
            double lb = run(m, matching);

            assertEquals(expected, lb, EPS, "iteration " + iter + ", n=" + n
                    + ", matching=" + java.util.Arrays.toString(matching));
        }
    }

    @Test
    void increasingSCCSizeEqualsBruteForceOnRandomInstances() throws ContradictionException {
        Random rnd = new Random(42);
        for (int iter = 0; iter < 300; iter++) {
            int n = 50 + rnd.nextInt(4); // 3..6
            int[] matching = randomMatching(n, rnd);
            double[][] m = randomReducedMatrix(n, matching, rnd);
            double[][] m2 = copy(m);

            //double expected = bruteForceArborescence(m);

            double totalIncrementalLb = 0;
            for (int i = 2; i < n; i++) {
               totalIncrementalLb += run(m, matching, i);
            }

            double directLb = run(m2, matching);

            assertEquals(totalIncrementalLb, directLb, EPS);
            /*assertEquals(expected, totalIncrementalLb, EPS, "iteration " + iter + ", n=" + n
                    + ", matching=" + java.util.Arrays.toString(matching));*/
        }
    }


    @Test
    void increasingSCCSizeEqualsRegularOnRandomInstances() throws ContradictionException {
        int seed = 48;
        for (int iter = 0; iter < 300; iter++) {
            Random rnd = new Random(seed+iter);
            int n = 50 + rnd.nextInt(4); // 3..6
            int[] matching = randomMatching(n, rnd);
            double[][] m = randomReducedMatrix(n, matching, rnd);
            double[][] m2 = copy(m);

            //double expected = bruteForceArborescence(m);

            double increaseLb = runIncreasing(m, matching);
            double directLb = run(m2, matching);
            System.out.println("direc" + iter);

            assertEquals(directLb, increaseLb, EPS);
            //assertEquals(directLb == totalIncrementalLb, true);
            /*assertEquals(expected, totalIncrementalLb, EPS, "iteration " + iter + ", n=" + n
                    + ", matching=" + java.util.Arrays.toString(matching));*/
        }
    }

    /**
     * With a limit k in {2,3,4,n}: lb stays a valid lower bound (0 <= lb <= optimal arborescence),
     * and with k = n (or any k >= n) it is exactly the optimum.
     */
    @Test
    void limitedLowerBoundIsValidOnRandomInstances() throws ContradictionException {
        Random rnd = new Random(7);
        for (int iter = 0; iter < 300; iter++) {
            int n = 3 + rnd.nextInt(4); // 3..6
            int[] matching = randomMatching(n, rnd);
            double[][] base = randomReducedMatrix(n, matching, rnd);
            double opt = bruteForceArborescence(base);

            for (int k : SMALL_LIMITS) {
                double lb = run(copy(base), matching, k);
                assertTrue(lb >= -EPS, "negative lb, k=" + k + ", iter=" + iter);
                assertTrue(lb <= opt + EPS,
                        "lb=" + lb + " > opt=" + opt + ", k=" + k + ", n=" + n + ", iter=" + iter);
                if (k >= n) {
                    assertEquals(opt, lb, EPS, "k>=n must be exact, k=" + k + ", iter=" + iter);
                }
            }
            assertEquals(opt, run(copy(base), matching, n), EPS, "k=n, iter=" + iter);
        }
    }

    /**
     * Limiting the size can only make the algorithm stop earlier on the very first iteration:
     * if the matching has no cycle of size <= k other than the root's, nothing is modified.
     */
    @Test
    void limitSmallerThanEverySourceCycle_leavesMatrixUntouched() throws ContradictionException {
        Random rnd = new Random(123);
        for (int iter = 0; iter < 200; iter++) {
            int n = 5 + rnd.nextInt(2); // 5..6
            // one single big cycle on 1..n-1 (size n-1), root self-assigned
            int[] matching = new int[n];
            matching[0] = 0;
            for (int i = 1; i < n; i++) matching[i] = (i % (n - 1)) + 1;
            double[][] base = randomReducedMatrix(n, matching, rnd);

            for (int k = 2; k < n - 1; k++) {
                double[][] m = copy(base);
                assertEquals(0, run(m, matching, k), EPS, "k=" + k + ", n=" + n);
                assertArrayEquals(base, m, "k=" + k + ", n=" + n);
            }
            assertTrue(run(copy(base), matching, n - 1) > 0 || bruteForceArborescence(base) == 0);
        }
    }

    // ---------- random generators ----------

    private static int[] randomMatching(int n, Random rnd) {
        List<Integer> perm = new ArrayList<>();
        for (int i = 0; i < n; i++) perm.add(i);
        Collections.shuffle(perm, rnd);
        return perm.stream().mapToInt(Integer::intValue).toArray();
    }


    private static double[][] randomReducedMatrix(int n, int[] matching, Random rnd) {
        double[][] m = new double[n][n];
        for (int i = 0; i < n; i++)
        {
            for (int j = 0; j < n; j++)
                m[i][j] = 1 + rnd.nextInt(99);
            m[i][i] = PropFusionAsymUndirectedGraphVar.bigValue;
        }
        for (int i = 0; i < n; i++) m[i][matching[i]] = 0; // one zero per column
        return m;
    }
}
