package org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangian;


import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangian.PropFusionAsymUndirectedGraphVar;
import org.chocosolver.solver.exception.ContradictionException;
import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.*;

class ReducedCostsAugmenterTest {

    private static final double EPS = 1e-9;
    private static final double BIG = PropFusionAsymUndirectedGraphVar.bigValue;

    // ---------- helpers ----------

    private double[][] call(int[] matching, double[][] rc) throws ContradictionException {
        int n = matching.length;
        BitSet rows = new BitSet(n); rows.set(0, n);
        BitSet cols = new BitSet(n); cols.set(0, n);
        return ReducedCostsAugmenter.augmentReducedCostsFW(matching, rows, cols, rc);
    }

    /**
     * Independent oracle: Floyd-Warshall on the right-to-right graph
     * (right j -> left matchInv[j] at cost 0 -> right c at cost rc[matchInv[j]][c]),
     * with every value capped at BIG.
     */
    private static double[][] oracle(int[] matching, double[][] rc) {
        int n = matching.length;
        int[] inv = new int[n];
        for (int i = 0; i < n; i++) inv[matching[i]] = i;
        double[][] d = new double[n][n];
        for (int j = 0; j < n; j++)
            for (int c = 0; c < n; c++)
                d[j][c] = (j == c) ? 0 : Math.min(BIG, rc[inv[j]][c]);
        for (int k = 0; k < n; k++)
            for (int a = 0; a < n; a++)
                for (int b = 0; b < n; b++)
                    d[a][b] = Math.min(d[a][b], d[a][k] + d[k][b]);
        double[][] out = new double[n][n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                out[i][j] = Math.min(BIG, rc[i][j] + d[j][matching[i]]);
        return out;
    }

    private static void assertMatrixEquals(double[][] expected, double[][] actual) {
        assertEquals(expected.length, actual.length);
        for (int i = 0; i < expected.length; i++) {
            assertEquals(expected[i].length, actual[i].length);
            for (int j = 0; j < expected[i].length; j++) {
                assertEquals(expected[i][j], actual[i][j], EPS, "cell [" + i + "][" + j + "]");
            }
        }
    }

    private static double[][] deepCopy(double[][] a) {
        double[][] c = new double[a.length][];
        for (int i = 0; i < a.length; i++) c[i] = a[i].clone();
        return c;
    }

    // ---------- hand-computed cases ----------

    @Test
    void twoNodes_forcingASelfLoopIsBig() throws ContradictionException {
        // matching: 0->1, 1->0. Forcing 0->0 forces 1->1: cost BIG + BIG, capped to BIG.
        int[] matching = {1, 0};
        double[][] rc = {
                {BIG, 0},
                {0, BIG}};
        double[][] expected = {
                {BIG, 0},
                {0, BIG}};
        assertMatrixEquals(expected, call(matching, rc));
    }

    @Test
    void threeNodes_handComputed() throws ContradictionException {
        // matching: 0->1, 1->2, 2->0
        int[] matching = {1, 2, 0};
        double[][] rc = {
                {BIG, 0, 4},
                {3, BIG, 0},
                {0, 2, BIG}};
        // e.g. arc 0->2: cycle 0->2->1->0 = 4 + 2 + 3 = 9
        double[][] expected = {
                {BIG, 0, 9},
                {9, BIG, 0},
                {0, 9, BIG}};
        assertMatrixEquals(expected, call(matching, rc));
    }

    @Test
    void allZeroOffDiagonal_staysZeroOffDiagonal() throws ContradictionException {
        int[] matching = {1, 2, 3, 0};
        double[][] rc = new double[4][4];
        for (int i = 0; i < 4; i++) rc[i][i] = BIG;
        assertMatrixEquals(deepCopy(rc), call(matching, rc));
    }

    @Test
    void detourIsPreferredOverExpensiveDirectArc() throws ContradictionException {
        // matching: 0->1, 1->2, 2->3, 3->0
        int[] matching = {1, 2, 3, 0};
        double[][] rc = {
                {BIG, 0, 1, 50},
                {50, BIG, 0, 50},
                {50, 50, BIG, 0},
                {0, 50, 50, BIG}};
        // Forcing 3->1 (rc 50): path from col1 to col0 is
        // col1 -> row0 -> col2 (1) -> row1... = direct 50 vs 1 + 50 + ... : oracle decides.
        assertMatrixEquals(oracle(matching, rc), call(matching, rc));
    }

    // ---------- bigValue behaviour ----------

    @Test
    void selfLoopsStayAtBig() throws ContradictionException {
        int[] matching = {2, 0, 3, 1};
        double[][] rc = randomReducedCosts(matching, new Random(3));
        double[][] result = call(matching, rc);
        for (int i = 0; i < matching.length; i++) assertEquals(BIG, result[i][i], EPS);
    }

    @Test
    void arcWhoseCycleIsImpossible_isBig() throws ContradictionException {
        // The only way back from col 0 to col 1 goes through BIG-cost arcs.
        int[] matching = {1, 2, 0};
        double[][] rc = {
                {BIG, 0, 4},
                {BIG, BIG, 0},
                {0, BIG, BIG}};
        double[][] result = call(matching, rc);
        assertEquals(true, BIG < result[1][0]);
    }

    // ---------- structural properties ----------

    @Test
    void matchingArcsKeepZeroReducedCost() throws ContradictionException {
        int[] matching = {2, 0, 3, 1};
        double[][] rc = randomReducedCosts(matching, new Random(1));
        double[][] result = call(matching, rc);
        for (int i = 0; i < matching.length; i++) assertEquals(0.0, result[i][matching[i]], EPS);
    }

    @Test
    void augmentedCostsAreNeverSmallerThanOriginal() throws ContradictionException {
        int[] matching = {3, 0, 1, 4, 2};
        double[][] rc = randomReducedCosts(matching, new Random(2));
        double[][] result = call(matching, rc);
        for (int i = 0; i < matching.length; i++)
            for (int j = 0; j < matching.length; j++)
                assertTrue(result[i][j] >= rc[i][j] - EPS, "cell [" + i + "][" + j + "]");
    }

    @Test
    void inputArrayIsNotMutated() throws ContradictionException {
        // ASSUMPTION: the method returns a new matrix and leaves the input intact.
        int[] matching = {1, 2, 0};
        double[][] rc = {{BIG, 0, 4}, {3, BIG, 0}, {0, 2, BIG}};
        double[][] copy = deepCopy(rc);
        call(matching, rc);
        assertMatrixEquals(copy, rc);
    }

    // ---------- randomized comparison against the oracle ----------

    @Test
    void randomInstances_matchFloydWarshallOracle() throws ContradictionException {
        Random rnd = new Random(42);
        for (int trial = 0; trial < 200; trial++) {
            int n = 2 + rnd.nextInt(9);
            int[] matching = randomDerangement(n, rnd);
            double[][] rc = randomReducedCosts(matching, rnd);
            assertMatrixEquals(oracle(matching, rc), call(matching, rc));
        }
    }

    @Test
    void resultIsAtLeastTheCheapestAssignmentForcingTheArc() throws ContradictionException {
        // The augmented cost is the cost of one alternating cycle, so it cannot be below
        // the cheapest full assignment containing the arc (compared up to the BIG cap).
        int[] matching = {1, 2, 3, 0};
        double[][] rc = randomReducedCosts(matching, new Random(7));
        double[][] result = call(matching, rc);
        int n = matching.length;
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                double best = Double.MAX_VALUE;
                for (int[] perm : allPermutations(n)) {
                    if (perm[i] != j) continue;
                    double sum = 0;
                    for (int r = 0; r < n; r++) sum += rc[r][perm[r]];
                    best = Math.min(best, sum);
                }
                assertTrue(result[i][j] >= Math.min(best, BIG) - EPS, "cell [" + i + "][" + j + "]");
            }
        }
    }

    // ---------- generators ----------

    /** Random permutation without fixed point (a self-loop can never be matched). */
    private static int[] randomDerangement(int n, Random rnd) {
        int[] p = new int[n];
        boolean ok;
        do {
            for (int i = 0; i < n; i++) p[i] = i;
            for (int i = n - 1; i > 0; i--) {
                int k = rnd.nextInt(i + 1);
                int t = p[i]; p[i] = p[k]; p[k] = t;
            }
            ok = true;
            for (int i = 0; i < n; i++) if (p[i] == i) { ok = false; break; }
        } while (!ok);
        return p;
    }

    /** Non-negative reduced costs: 0 on matching arcs, BIG on the diagonal. */
    private static double[][] randomReducedCosts(int[] matching, Random rnd) {
        int n = matching.length;
        double[][] rc = new double[n][n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++) {
                if (i == j) rc[i][j] = BIG;
                else if (matching[i] == j) rc[i][j] = 0;
                else rc[i][j] = rnd.nextInt(4) == 0 ? 0 : 1 + rnd.nextInt(20);
            }
        return rc;
    }

    private static List<int[]> allPermutations(int n) {
        List<int[]> out = new ArrayList<>();
        permute(new int[n], new boolean[n], 0, out);
        return out;
    }

    private static void permute(int[] cur, boolean[] used, int pos, List<int[]> out) {
        if (pos == cur.length) { out.add(cur.clone()); return; }
        for (int v = 0; v < cur.length; v++) {
            if (used[v]) continue;
            used[v] = true; cur[pos] = v;
            permute(cur, used, pos + 1, out);
            used[v] = false;
        }
    }

    // ---------- larger instances, no oracle ----------

    /**
     * Ring matching i -> (i+1) % n. Diagonal = BIG, matching arcs = 0, every other arc = c.
     *
     * Closed form of the result (n >= 4), for arc (i, j) with m = (i+1) % n:
     *   j == m        -> 0                (matching arc)
     *   j == i        -> BIG              (self-loop)
     *   j == (i+2)%n  -> 3c               (cycle i -> i+2 -> x -> i+1 needs 2 hops back, since
     *                                      the direct arc (i+1, i+1) is the self-loop)
     *   otherwise     -> 2c               (arc itself + one arc back from i+2's row)
     */
    @ParameterizedTest
    @ValueSource(ints = {4, 5, 10, 31, 100})
    void ringMatching_closedFormResult(int n) throws ContradictionException {
        double c = 7;
        int[] matching = new int[n];
        double[][] rc = new double[n][n];
        for (int i = 0; i < n; i++) {
            matching[i] = (i + 1) % n;
            for (int j = 0; j < n; j++) {
                if (i == j) rc[i][j] = BIG;
                else if (j == matching[i]) rc[i][j] = 0;
                else rc[i][j] = c;
            }
        }
        double[][] result = call(matching, rc);
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                double expected;
                if (j == (i + 1) % n) expected = 0;
                else if (j == i) expected = BIG;
                else if (j == (i + 2) % n) expected = 3 * c;
                else expected = 2 * c;
                assertEquals(expected, result[i][j], EPS, "n=" + n + " cell [" + i + "][" + j + "]");
            }
        }
    }

    /**
     * Two zero-cost perfect matchings on an odd n: i -> i+1 and i -> i+2.
     * Forcing an arc of the second one stays free, because the other arcs of that matching
     * (stepping by +2 around the odd ring) form the zero-cost path back.
     */
    @ParameterizedTest
    @ValueSource(ints = {5, 15, 101})
    void twoZeroCostMatchings_secondMatchingStaysZero(int n) throws ContradictionException {
        int[] matching = new int[n];
        double[][] rc = new double[n][n];
        for (int i = 0; i < n; i++) {
            matching[i] = (i + 1) % n;
            for (int j = 0; j < n; j++) {
                if (i == j) rc[i][j] = BIG;
                else if (j == (i + 1) % n || j == (i + 2) % n) rc[i][j] = 0;
                else rc[i][j] = 5;
            }
        }
        double[][] result = call(matching, rc);
        for (int i = 0; i < n; i++) {
            assertEquals(0.0, result[i][(i + 1) % n], EPS, "matching arc " + i);
            assertEquals(0.0, result[i][(i + 2) % n], EPS, "second matching arc " + i);
            assertEquals(BIG, result[i][i], EPS, "self-loop " + i);
        }
    }

    /**
     * Upper bounds that any correct shortest path must respect: the augmented cost can never
     * exceed the cost of an explicit 1-hop or 2-hop cycle through the arc (capped at BIG).
     */
    @Test
    void largeRandom_resultRespectsExplicitCycleUpperBounds() throws ContradictionException {
        int n = 60;
        Random rnd = new Random(123);
        int[] matching = randomDerangement(n, rnd);
        double[][] rc = randomReducedCosts(matching, rnd);
        int[] inv = new int[n];
        for (int i = 0; i < n; i++) inv[matching[i]] = i;

        double[][] result = call(matching, rc);

        for (int i = 0; i < n; i++) {
            int m = matching[i];
            for (int j = 0; j < n; j++) {
                if (j == m) continue;
                // 1 hop back: right j -> left inv[j] -> right m
                double oneHop = rc[i][j] + rc[inv[j]][m];
                assertTrue(result[i][j] <= Math.min(BIG, oneHop) + EPS, "1-hop [" + i + "][" + j + "]");
                // 2 hops back: right j -> left inv[j] -> right x -> left inv[x] -> right m
                for (int x = 0; x < n; x++) {
                    if (x == j || x == m) continue;
                    double twoHops = rc[i][j] + rc[inv[j]][x] + rc[inv[x]][m];
                    assertTrue(result[i][j] <= Math.min(BIG, twoHops) + EPS,
                            "2-hop [" + i + "][" + j + "] via " + x);
                }
            }
        }
    }

    @Test
    void largeInstance_finishesInReasonableTime() {
        int n = 200;
        int[] matching = new int[n];
        double[][] rc = new double[n][n];
        for (int i = 0; i < n; i++) {
            matching[i] = (i + 1) % n;
            for (int j = 0; j < n; j++)
                rc[i][j] = (i == j) ? BIG : (j == matching[i] ? 0 : 3);
        }
        double[][] result = assertTimeoutPreemptively(Duration.ofSeconds(10), () -> call(matching, rc));
        // spot checks from the closed form of the ring test (c = 3)
        assertEquals(0.0, result[0][1], EPS);
        assertEquals(9.0, result[0][2], EPS);
        assertEquals(6.0, result[0][57], EPS);
        assertEquals(BIG, result[5][5], EPS);
    }


}
