package org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangian;

import org.chocosolver.solver.exception.ContradictionException;

import java.util.Arrays;
import java.util.BitSet;

public class ReducedCostsAugmenter {

    static double[][] reducedCosts;
    static double bigValue;
    static int n;

    public static double[][] augmentReducedCostsFW(int[] matching, BitSet remainingRows, BitSet remainingCols, double[][] reducedCosts) throws ContradictionException {
        bigValue = PropFusionAsymUndirectedGraphVar.bigValue;
        int nRemaining = remainingCols.cardinality();
        ReducedCostsAugmenter.reducedCosts = reducedCosts;
        n = reducedCosts.length;

        // build base matrix restricted to remaining rows/cols
        double[][] W = new double[2*nRemaining][2*nRemaining];
        for (double[] row : W) Arrays.fill(row, bigValue);

        // map: row i -> position ki in [0, nRemaining)
        //      col j -> position kj+nRemaining in [nRemaining, 2*nRemaining)
        int ki = 0;
        for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
            int kj = 0;
            for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)) {
                // row i -> column j  (forward arc)
                W[ki][kj + nRemaining] = getCostFlow(i, j + n, matching);
                // column j -> row i  (reverse/matching arc)
                W[kj + nRemaining][ki] = getCostFlow(j + n, i, matching);
                kj++;
            }
            ki++;
        }

        for (int idx = 0; idx < 2*nRemaining; idx++) {
            W[idx][idx] = 0;
        }

        for (int k = 0; k < 2*nRemaining; k++) {
            for (int i = 0; i < 2*nRemaining; i++) {
                for (int j = 0; j < 2*nRemaining; j++) {
                    W[i][j] = Math.min(W[i][j], W[i][k] + W[k][j]);
                }
            }
        }

        double[][] bigReducedCosts = new double[n][n];
        ki = 0;
        for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
            int kj = 0;
            for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)) {
                if (i == j) {
                    bigReducedCosts[i][j] = bigValue;
                } else {
                    // mirrors old: W[j+n][i] + reducedCosts[i][j], with j+n -> kj+nRemaining, i -> ki
                    bigReducedCosts[i][j] = W[kj + nRemaining][ki] + reducedCosts[i][j];
                }
                kj++;
            }
            ki++;
        }
        return bigReducedCosts;
    }


    private static double getCostFlow(int from, int to, int[] matching){
        if(from < n && to < n || from >= n && to >= n){
            return bigValue;
        }
        if (from >= n){
            // Should transpose
            if(matching[to] == from-n){
                return 0;
            }
            return bigValue;
        }else{
            if(matching[from] == to-n){
                return bigValue;
            }
            return reducedCosts[from][to-n];
        }
    }
}
