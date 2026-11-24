package org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangian;

import org.chocosolver.solver.exception.ContradictionException;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Edge cases complementing EdmondsAlgorithmTest.
 *
 * Assumptions (adapt if your implementation differs):
 *  - an SCC larger than tailleMaxCycles is SKIPPED (it does not stop the whole algorithm);
 *  - penalizing an SCC subtracts its cheapest entering cost from ALL entering arcs (from outside the SCC);
 *  - arcs into the root are ignored and never modified;
 *  - the zero-arc graph is built from every zero of the matrix.
 */
class EdmondsAlgorithmEdgeCasesTest {

    private static final double EPS = 1e-9;
    private static final double BIG = 100;
    private static final double FORBIDDEN = PropFusionAsymUndirectedGraphVar.bigValue;

    // ---------- helpers ----------

    private static BitSet all(int n) {
        BitSet bs = new BitSet(n);
        bs.set(0, n);
        return bs;
    }

    private static double run(double[][] m, int[] matching, int k) throws ContradictionException {
        int n = m.length;
        return EdmondsAlgorithm.fullEdmondsSCC(m, matching, all(n), all(n), k).lb;
    }

    private static double[][] copy(double[][] m) {
        double[][] c = new double[m.length][];
        for (int i = 0; i < m.length; i++) c[i] = m[i].clone();
        return c;
    }

    /** BIG everywhere, 0 on matching arcs (rows >= 1), and the given row for the root (rootRow[0] must be 0). */
    private static double[][] sparse(int[] matching, double[] rootRow) {
        int n = matching.length;
        double[][] m = new double[n][n];
        for (double[] row : m) Arrays.fill(row, BIG);
        for (int i = 1; i < n; i++) m[i][matching[i]] = 0;
        m[0] = rootRow.clone();
        return m;
    }

    private static void forEachArborescence(int n, Consumer<int[]> consumer) {
        arbRec(new int[n], 1, n, consumer);
    }

    private static void arbRec(int[] parent, int v, int n, Consumer<int[]> consumer) {
        if (v == n) {
            for (int u = 1; u < n; u++) {
                int x = u, steps = 0;
                while (x != 0 && steps <= n) { x = parent[x]; steps++; }
                if (x != 0) return;
            }
            consumer.accept(parent);
            return;
        }
        for (int p = 0; p < n; p++) {
            if (p == v) continue;
            parent[v] = p;
            arbRec(parent, v + 1, n, consumer);
        }
    }

    private static double bruteForce(double[][] m) {
        double[] best = {Double.POSITIVE_INFINITY};
        forEachArborescence(m.length, p -> {
            double c = 0;
            for (int u = 1; u < p.length; u++) c += m[p[u]][u];
            best[0] = Math.min(best[0], c);
        });
        return best[0];
    }

    /**
     * Naive reference for the limited algorithm (no forbidden arcs):
     * repeat { zero graph without arcs into the root; every source SCC without the root
     * and with size <= k gets its cheapest entering cost subtracted from all entering arcs }.
     */
    private static double reference(double[][] m, int k) {
        int n = m.length;
        double lb = 0;
        while (true) {
            boolean[][] reach = new boolean[n][n];
            for (int i = 0; i < n; i++) {
                reach[i][i] = true;
                for (int j = 1; j < n; j++) if (i != j && Math.abs(m[i][j]) <= EPS) reach[i][j] = true;
            }
            for (int t = 0; t < n; t++)
                for (int i = 0; i < n; i++)
                    for (int j = 0; j < n; j++)
                        if (reach[i][t] && reach[t][j]) reach[i][j] = true;

            boolean[] done = new boolean[n];
            boolean penalized = false;
            for (int s = 0; s < n; s++) {
                if (done[s]) continue;
                List<Integer> comp = new ArrayList<>();
                for (int v = 0; v < n; v++) if (reach[s][v] && reach[v][s]) { comp.add(v); done[v] = true; }
                if (comp.contains(0)) continue;

                boolean source = true;
                double min = Double.POSITIVE_INFINITY;
                for (int u = 0; u < n; u++) {
                    if (comp.contains(u)) continue;
                    for (int v : comp) {
                        if (Math.abs(m[u][v]) <= EPS) source = false;
                        min = Math.min(min, m[u][v]);
                    }
                }
                if (!source || comp.size() > k) continue;
                for (int u = 0; u < n; u++) {
                    if (comp.contains(u)) continue;
                    for (int v : comp) m[u][v] -= min;
                }
                lb += min;
                penalized = true;
            }
            if (!penalized) return lb;
        }
    }

    private static int[] randomMatching(int n, Random rnd) {
        List<Integer> perm = new ArrayList<>();
        for (int i = 0; i < n; i++) perm.add(i);
        Collections.shuffle(perm, rnd);
        return perm.stream().mapToInt(Integer::intValue).toArray();
    }

    private static double[][] randomReducedMatrix(int n, int[] matching, Random rnd) {
        double[][] m = new double[n][n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                m[i][j] = 1 + rnd.nextInt(9);
        for (int i = 0; i < n; i++) m[i][matching[i]] = 0;
        return m;
    }

    // ---------- mixed sizes: skip, not stop ----------

    /** Source cycles {1,2} (size 2) and {3,4,5} (size 3). With k=2 only the small one is penalized. */
    @Test
    void mixedSizes_smallCycleFirst_bigOneIsSkippedNotBlocking() throws ContradictionException {
        int[] mt = {0, 2, 1, 4, 5, 3};
        double[] root = {0, 4, 6, 5, 7, 9};

        double[][] m = sparse(mt, root);
        assertEquals(4, run(m, mt, 2), EPS);
        assertArrayEquals(new double[]{0, 0, 2, 5, 7, 9}, m[0], EPS);

        for (int k : new int[]{3, 4, 6}) {
            m = sparse(mt, root);
            assertEquals(4 + 5, run(m, mt, k), EPS, "k=" + k);
            assertArrayEquals(new double[]{0, 0, 2, 0, 2, 4}, m[0], EPS, "k=" + k);
        }
    }

    /** Same with the big cycle first ({1,2,3}) so an implementation that "stops at the first big SCC" fails. */
    @Test
    void mixedSizes_bigCycleFirst_smallOneStillPenalized() throws ContradictionException {
        int[] mt = {0, 2, 3, 1, 5, 4};
        double[] root = {0, 5, 7, 9, 4, 6};

        double[][] m = sparse(mt, root);
        assertEquals(4, run(m, mt, 2), EPS);
        assertArrayEquals(new double[]{0, 5, 7, 9, 0, 2}, m[0], EPS);

        for (int k : new int[]{3, 4, 6}) {
            m = sparse(mt, root);
            assertEquals(5 + 4, run(m, mt, k), EPS, "k=" + k);
            assertArrayEquals(new double[]{0, 0, 2, 4, 0, 2}, m[0], EPS, "k=" + k);
        }
    }

    // ---------- non-source SCCs ----------

    /** Y={3,4} is reachable from the root by a zero arc: no penalty, whatever k. */
    @Test
    void nonSourceScc_getsNoPenalty() throws ContradictionException {
        int[] mt = {0, 2, 1, 4, 3};
        for (int k : new int[]{2, 3, 4, 5}) {
            double[][] m = sparse(mt, new double[]{0, 4, 6, 0, 9});
            assertEquals(4, run(m, mt, k), EPS, "k=" + k);
            assertArrayEquals(new double[]{0, 0, 2, 0, 9}, m[0], EPS, "k=" + k);
        }
    }

    /** Y is not enterable from the root (forbidden) but is reachable from X by a zero arc: must NOT throw. */
    @Test
    void nonSourceSccWithoutFeasibleEntry_doesNotThrow() throws ContradictionException {
        int[] mt = {0, 2, 1, 4, 3};
        for (int k : new int[]{2, 3, 4, 5}) {
            double[][] m = sparse(mt, new double[]{0, 4, FORBIDDEN, FORBIDDEN, FORBIDDEN});
            m[1][3] = 0;   // X -> Y
            assertEquals(4, run(m, mt, k), EPS, "k=" + k);
        }
    }

    /** The entering minimum comes from a non-root row (a node of another, root-reachable SCC). */
    @Test
    void cheapestEntryComesFromAnotherScc() throws ContradictionException {
        int[] mt = {0, 2, 1, 4, 3};
        double[][] m = sparse(mt, new double[]{0, 5, 6, 0, 9});
        m[3][1] = 2;
        assertEquals(2, run(m, mt, 5), EPS);
        assertArrayEquals(new double[]{0, 3, 4, 0, 9}, m[0], EPS);
        assertEquals(0, m[3][1], EPS);
        assertEquals(BIG - 2, m[3][2], EPS);
    }

    // ---------- contradictions ----------

    /**
     * X and Y merge after the first iteration, and the merged SCC has no feasible entry.
     * Contradiction only if the merged size (4) is within the limit.
     */
    @Test
    void contradictionInLaterIteration_onlyWithinLimit() throws ContradictionException {
        int[] mt = {0, 2, 1, 4, 3};
        for (int k : new int[]{2, 3}) {
            double[][] m = sparse(mt, new double[]{0, FORBIDDEN, FORBIDDEN, FORBIDDEN, FORBIDDEN});
            m[3][1] = 1;
            m[2][3] = 1;
            assertEquals(2, run(m, mt, k), EPS, "k=" + k);
        }
        for (int k : new int[]{4, 5}) {
            double[][] m = sparse(mt, new double[]{0, FORBIDDEN, FORBIDDEN, FORBIDDEN, FORBIDDEN});
            m[3][1] = 1;
            m[2][3] = 1;
            assertThrows(ContradictionException.class, () -> run(m, mt, 4), "k=" + k);
        }
    }

    // ---------- matrix / arc semantics ----------

    /** Finite non-zero chords inside the SCC and finite arcs into the root must be left untouched. */
    @Test
    void chordsInsideSccAndArcsIntoRoot_areUntouched() throws ContradictionException {
        int[] mt = {0, 2, 3, 1};
        for (int k : new int[]{3, 4}) {
            double[][] m = sparse(mt, new double[]{0, 5, 3, 7});
            m[1][3] = 8;     // chord inside {1,2,3}
            m[3][2] = 6;     // chord inside {1,2,3}
            m[2][0] = 11;    // arc into the root
            assertEquals(3, run(m, mt, k), EPS, "k=" + k);
            assertArrayEquals(new double[]{0, 2, 0, 4}, m[0], EPS, "k=" + k);
            assertEquals(8, m[1][3], EPS);
            assertEquals(6, m[3][2], EPS);
            assertEquals(11, m[2][0], EPS);
        }
    }

    /** Zero arcs INTO the root must not make {1,2} reachable from / merged with the root. */
    @Test
    void zeroArcsIntoRoot_doNotHideSourceCycle() throws ContradictionException {
        int[] mt = {0, 2, 1};
        double[][] m = sparse(mt, new double[]{0, 4, 6});
        m[1][0] = 0;
        m[2][0] = 0;
        assertEquals(4, run(m, mt, 3), EPS);
        assertArrayEquals(new double[]{0, 0, 2}, m[0], EPS);
        assertEquals(0, m[1][0], EPS);
        assertEquals(0, m[2][0], EPS);
    }

    @Test
    void nonIntegerCosts() throws ContradictionException {
        int[] mt = {0, 2, 3, 1};
        double[][] m = sparse(mt, new double[]{0, 0.3, 0.1, 0.2});
        assertEquals(0.1, run(m, mt, 3), EPS);
        assertArrayEquals(new double[]{0, 0.2, 0, 0.1}, m[0], EPS);
    }

    // ---------- tiny instances / degenerate limits ----------

    @Test
    void twoNodes_rootInCycle_noPenalty() throws ContradictionException {
        double[][] m = {{BIG, 0}, {0, BIG}};
        int[] mt = {1, 0};
        for (int k : new int[]{1, 2}) {
            double[][] c = copy(m);
            assertEquals(0, run(c, mt, k), EPS, "k=" + k);
            assertArrayEquals(m, c, "k=" + k);
        }
    }

    /** Fixed point (size-1 cycle): penalized as soon as k >= 1. Not realistic for an assignment, but legal input. */
    @Test
    void twoNodes_fixedPointIsACycleOfSize1() throws ContradictionException {
        int[] mt = {0, 1};
        for (int k : new int[]{1, 2}) {
            double[][] m = sparse(mt, new double[]{0, 5});
            assertEquals(5, run(m, mt, k), EPS, "k=" + k);
            assertEquals(0, m[0][1], EPS);
        }
    }

    /** k <= 1 on cycles of size >= 2 does nothing; k = Integer.MAX_VALUE behaves like k = n. */
    @Test
    void degenerateLimits() throws ContradictionException {
        int[] mt = {0, 2, 3, 1};
        double[] root = {0, 5, 3, 7};
        for (int k : new int[]{Integer.MIN_VALUE, -1, 0, 1}) {
            double[][] m = sparse(mt, root);
            assertEquals(0, run(m, mt, k), EPS, "k=" + k);
            assertArrayEquals(sparse(mt, root), m, "k=" + k);
        }
        double[][] m = sparse(mt, root);
        assertEquals(3, run(m, mt, Integer.MAX_VALUE), EPS);
        assertArrayEquals(new double[]{0, 2, 0, 4}, m[0], EPS);
    }

    // ---------- property tests ----------

    /** Exact comparison (lb and final matrix) against the naive reference, for every limit, up to n = 9. */
    @Test
    void matchesReferenceOnRandomInstances_allLimits() {
        Random rnd = new Random(2024);
        for (int iter = 0; iter < 500; iter++) {
            int n = 3 + rnd.nextInt(7); // 3..9
            int[] matching = randomMatching(n, rnd);
            double[][] base = randomReducedMatrix(n, matching, rnd);
            for (int k : new int[]{1, 2, 3, 4, n - 1, n}) {
                double[][] expected = copy(base);
                double expectedLb = reference(expected, k);
                double[][] actual = copy(base);
                double lb = assertDoesNotThrowValue(() -> run(actual, matching, k));
                String ctx = "iter=" + iter + ", n=" + n + ", k=" + k + ", matching=" + Arrays.toString(matching);
                assertEquals(expectedLb, lb, EPS, ctx);
                assertArrayEquals(expected, actual, ctx);
            }
        }
    }

    private interface ThrowingSupplier { double get() throws ContradictionException; }

    private static double assertDoesNotThrowValue(ThrowingSupplier s) {
        try {
            return s.get();
        } catch (ContradictionException e) {
            fail("unexpected contradiction (no forbidden arcs in the instance)");
            return Double.NaN;
        }
    }

    /** Structural invariants after a run, for every limit. */
    @Test
    void invariantsHoldForAllLimits() throws ContradictionException {
        Random rnd = new Random(99);
        for (int iter = 0; iter < 300; iter++) {
            int n = 3 + rnd.nextInt(6);
            int[] matching = randomMatching(n, rnd);
            double[][] base = randomReducedMatrix(n, matching, rnd);
            for (int k : new int[]{2, 3, 4, n}) {
                double[][] m = copy(base);
                run(m, matching, k);
                for (int i = 0; i < n; i++) {
                    assertEquals(0, m[i][matching[i]], EPS, "matching zero moved");
                    assertEquals(base[i][0], m[i][0], EPS, "arc into root modified");
                    for (int j = 0; j < n; j++) {
                        assertTrue(m[i][j] <= base[i][j] + EPS, "entry increased");
                        assertTrue(m[i][j] >= -EPS, "negative entry");
                    }
                }
            }
        }
    }

    /** lb is a valid dual bound: for EVERY arborescence T, cost(T) >= lb + reducedCost(T). */
    @Test
    void dualBoundHoldsForEveryArborescence() throws ContradictionException {
        Random rnd = new Random(5);
        for (int iter = 0; iter < 100; iter++) {
            int n = 3 + rnd.nextInt(3); // 3..5
            int[] matching = randomMatching(n, rnd);
            double[][] base = randomReducedMatrix(n, matching, rnd);
            for (int k : new int[]{2, 3, 4, n}) {
                double[][] m = copy(base);
                double lb = run(m, matching, k);
                forEachArborescence(n, p -> {
                    double orig = 0, red = 0;
                    for (int u = 1; u < n; u++) { orig += base[p[u]][u]; red += m[p[u]][u]; }
                    assertTrue(red >= -EPS);
                    assertTrue(orig >= lb + red - EPS, "dual bound violated, k=" + k + ", p=" + Arrays.toString(p));
                });
            }
        }
    }

    /** After a full run (k = n) a second run changes nothing and returns 0. */
    @Test
    void fullRunIsIdempotent() throws ContradictionException {
        Random rnd = new Random(31);
        for (int iter = 0; iter < 200; iter++) {
            int n = 3 + rnd.nextInt(6);
            int[] matching = randomMatching(n, rnd);
            double[][] m = randomReducedMatrix(n, matching, rnd);
            run(m, matching, n);
            double[][] snapshot = copy(m);
            assertEquals(0, run(m, matching, n), EPS, "iter=" + iter);
            assertArrayEquals(snapshot, m, "iter=" + iter);
        }
    }

    /** For k >= n the result is the optimum; k = n - 1 on a single big cycle must already be exact. */
    @Test
    void singleBigCycle_limitNMinus1IsExact() throws ContradictionException {
        Random rnd = new Random(77);
        for (int iter = 0; iter < 200; iter++) {
            int n = 4 + rnd.nextInt(3);
            int[] matching = new int[n];
            for (int i = 1; i < n; i++) matching[i] = (i % (n - 1)) + 1;
            double[][] base = randomReducedMatrix(n, matching, rnd);
            double opt = bruteForce(base);
            assertEquals(opt, run(copy(base), matching, n - 1), EPS, "iter=" + iter);
            assertEquals(opt, run(copy(base), matching, n), EPS, "iter=" + iter);
        }
    }
}
