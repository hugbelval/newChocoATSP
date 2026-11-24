package org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangian;

import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.BitSet;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.*;

class HungarianAlgorithmTest {

    private static final double EPS = 1e-9;

    // ------------------------------------------------------------------
    // Adapters for PropFusionAsymUndirectedGraphVar.Result.
    // Adjust these three if the Result class exposes getters instead of fields.
    // ------------------------------------------------------------------
    private static double lb(PropFusionAsymUndirectedGraphVar.Result r) {
        return r.lb;
    }

    private static int[] matching(PropFusionAsymUndirectedGraphVar.Result r) {
        return r.matching;
    }

    private static double[][] reduced(PropFusionAsymUndirectedGraphVar.Result r) {
        return r.array;
    }

    // ------------------------------------------------------------------
    // Helpers
    // ------------------------------------------------------------------
    private static BitSet full(int n) {
        BitSet b = new BitSet(n);
        b.set(0, n);
        return b;
    }

    private static BitSet bits(int... idx) {
        BitSet b = new BitSet();
        for (int i : idx) b.set(i);
        return b;
    }

    private static double[][] copy(double[][] m) {
        double[][] c = new double[m.length][];
        for (int i = 0; i < m.length; i++) c[i] = m[i].clone();
        return c;
    }

    private static PropFusionAsymUndirectedGraphVar.Result solve(double[][] m) {
        int n = m.length;
        return new HungarianAlgorithm(n).execute(copy(m), full(n), full(n));
    }

    private static double costOf(double[][] original, int[] match) {
        double sum = 0;
        for (int w = 0; w < match.length; w++) {
            if (match[w] >= 0) sum += original[w][match[w]];
        }
        return sum;
    }

    private static void assertPermutation(int[] match, int n) {
        boolean[] seen = new boolean[n];
        for (int w = 0; w < n; w++) {
            int j = match[w];
            assertTrue(j >= 0 && j < n, "worker " + w + " has invalid job " + j);
            assertFalse(seen[j], "job " + j + " assigned twice");
            seen[j] = true;
        }
    }

    private static double bruteForce(double[][] m) {
        return bruteForce(m, 0, new boolean[m.length]);
    }

    private static double bruteForce(double[][] m, int w, boolean[] used) {
        if (w == m.length) return 0;
        double best = Double.POSITIVE_INFINITY;
        for (int j = 0; j < m.length; j++) {
            if (!used[j]) {
                used[j] = true;
                best = Math.min(best, m[w][j] + bruteForce(m, w + 1, used));
                used[j] = false;
            }
        }
        return best;
    }

    // ------------------------------------------------------------------
    // Tests
    // ------------------------------------------------------------------
    @Test
    void singleElement() {
        double[][] m = {{7}};
        PropFusionAsymUndirectedGraphVar.Result r = solve(m);
        assertEquals(7, lb(r), EPS);
        assertArrayEquals(new int[]{0}, matching(r));
    }

    @Test
    void myExample() {
        double[][] m = {
                {82, 83, 69, 92},
                {77, 37, 49, 92},
                {11, 69, 5, 86},
                {8, 9, 98, 23},
        };
        PropFusionAsymUndirectedGraphVar.Result r = solve(m);
        assertEquals(140, lb(r), EPS);
        assertArrayEquals(new int[]{2,1,0,3}, matching(r));
    }

    @Test
    void smallThreeByThree() {
        double[][] m = {
                {4, 1, 3},
                {2, 0, 5},
                {3, 2, 2}
        };
        PropFusionAsymUndirectedGraphVar.Result r = solve(m);
        assertEquals(5, lb(r), EPS);
        assertArrayEquals(new int[]{1, 0, 2}, matching(r));
    }

    @Test
    void classicFourByFour() {
        double[][] m = {
                {82, 83, 69, 92},
                {77, 37, 49, 92},
                {11, 69, 5, 86},
                {8, 9, 98, 23}
        };
        PropFusionAsymUndirectedGraphVar.Result r = solve(m);
        assertEquals(140, lb(r), EPS);
        assertPermutation(matching(r), 4);
        assertEquals(140, costOf(m, matching(r)), EPS);
    }

    @Test
    void zeroDiagonalGivesZeroCostIdentityMatching() {
        int n = 4;
        double[][] m = new double[n][n];
        for (double[] row : m) Arrays.fill(row, 10);
        for (int i = 0; i < n; i++) m[i][i] = 0;

        PropFusionAsymUndirectedGraphVar.Result r = solve(m);
        assertEquals(0, lb(r), EPS);
        assertArrayEquals(new int[]{0, 1, 2, 3}, matching(r));
    }

    @Test
    void allEqualCosts() {
        double[][] m = new double[3][3];
        for (double[] row : m) Arrays.fill(row, 5);
        PropFusionAsymUndirectedGraphVar.Result r = solve(m);
        assertEquals(15, lb(r), EPS);
        assertPermutation(matching(r), 3);
    }

    @Test
    void negativeCosts() {
        double[][] m = {
                {-1, 2},
                {3, -4}
        };
        PropFusionAsymUndirectedGraphVar.Result r = solve(m);
        assertEquals(-5, lb(r), EPS);
        assertArrayEquals(new int[]{0, 1}, matching(r));
    }

    @Test
    void reducedMatrixIsNonNegativeAndZeroOnMatching() {
        double[][] m = {
                {82, 83, 69, 92},
                {77, 37, 49, 92},
                {11, 69, 5, 86},
                {8, 9, 98, 23}
        };
        PropFusionAsymUndirectedGraphVar.Result r = solve(m);
        double[][] red = reduced(r);
        int[] match = matching(r);

        for (double[] row : red) {
            for (double v : row) assertTrue(v >= -EPS, "negative reduced cost " + v);
        }
        for (int w = 0; w < 4; w++) {
            assertEquals(0, red[w][match[w]], EPS, "matched edge must have zero reduced cost");
        }
    }

    @Test
    void reducedMatrixIsComputedInPlace() {
        double[][] m = {{4, 1}, {2, 3}};
        HungarianAlgorithm h = new HungarianAlgorithm(2);
        PropFusionAsymUndirectedGraphVar.Result r = h.execute(m, full(2), full(2));
        assertSame(m, reduced(r));
    }

    @Test
    void restrictedRowsAndColumns() {
        double[][] m = {
                {9, 2, 9, 7},
                {9, 9, 9, 9},
                {9, 4, 9, 3},
                {9, 9, 9, 9}
        };
        double[][] original = copy(m);

        HungarianAlgorithm h = new HungarianAlgorithm(4);
        PropFusionAsymUndirectedGraphVar.Result r = h.execute(m, bits(0, 2), bits(1, 3));

        assertEquals(5, lb(r), EPS); // 0->1 (2) + 2->3 (3)
        int[] match = matching(r);
        assertEquals(1, match[0]);
        assertEquals(3, match[2]);
        assertEquals(-1, match[1], "worker outside the remaining set must stay unmatched");
        assertEquals(-1, match[3], "worker outside the remaining set must stay unmatched");

        // Rows/columns outside the sub-problem must be left untouched.
        assertArrayEquals(original[1], m[1], EPS);
        assertArrayEquals(original[3], m[3], EPS);
        for (int w = 0; w < 4; w++) {
            assertEquals(original[w][0], m[w][0], EPS);
            assertEquals(original[w][2], m[w][2], EPS);
        }
    }

    @Test
    void instanceCanBeReusedAcrossCalls() {
        HungarianAlgorithm h = new HungarianAlgorithm(3);

        double[][] a = {{4, 1, 3}, {2, 0, 5}, {3, 2, 2}};
        PropFusionAsymUndirectedGraphVar.Result r1 = h.execute(copy(a), full(3), full(3));
        assertEquals(5, lb(r1), EPS);

        double[][] b = {{1, 9, 9}, {9, 1, 9}, {9, 9, 1}};
        PropFusionAsymUndirectedGraphVar.Result r2 = h.execute(copy(b), full(3), full(3));
        assertEquals(3, lb(r2), EPS);
        assertArrayEquals(new int[]{0, 1, 2}, matching(r2));

        PropFusionAsymUndirectedGraphVar.Result r3 = h.execute(copy(a), full(3), full(3));
        assertEquals(5, lb(r3), EPS);
    }

    @Test
    void matchesBruteForceOnRandomMatrices() {
        Random rnd = new Random(42);
        for (int trial = 0; trial < 300; trial++) {
            int n = 1 + rnd.nextInt(7);
            double[][] m = new double[n][n];
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    m[i][j] = rnd.nextInt(100) - 20; // integers, some negative
                }
            }
            PropFusionAsymUndirectedGraphVar.Result r = solve(m);
            double expected = bruteForce(m);

            assertEquals(expected, lb(r), EPS, "lower bound mismatch, trial " + trial);
            assertPermutation(matching(r), n);
            assertEquals(expected, costOf(m, matching(r)), EPS, "matching cost mismatch, trial " + trial);
        }
    }
}
