package org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangian;

import org.chocosolver.solver.exception.ContradictionException;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;


public class EdmondsArbo {
    double bigValue = 999999;

    int n = 0;

    private BitSet createBitsetFromList(List<Integer> list){
        BitSet bs = new BitSet(n);
        for (int i = 0; i < list.size(); i++) {
            bs.set(list.get(i));
        }
        return bs;
    }


    public double getArboBound(int[][] matrix) throws ContradictionException {
        n = matrix.length;
        int[] matching = new int[n];
        double lb = 0;
        lb += fullEdmondsSCC(matrix, false, matching);
        return lb;
    }

    public double fullEdmondsSCC(
            int[][] matrix,
            boolean ignoreStars,
            int[] matching
    ) throws ContradictionException {
        int root = 0;

        double lb = 0;
        if(!ignoreStars){
        } else {
            throw new RuntimeException("Error352");
        }

        BitSet[] A = new BitSet[n];
        for (int i =0; i<n; i++){
            A[i] = new BitSet(n);
            int j = matching[i];
            if (j != root){
                A[i].set(j);
            }
        }

        boolean shouldStop = false;

        while (!shouldStop){
            ArrayList<ArrayList<Integer>> strongComponents;

            strongComponents = SCCFinder.getSCCs(A);

            boolean componentFound = false;

            for(List<Integer> scc : strongComponents){
                boolean validSCC = true;
                BitSet sccBs = createBitsetFromList(scc);
                double minimumInCol = bigValue;

                for (int i = 0; i < n; i++) {
                    if (sccBs.get(i)) continue;
                    if (A[i].intersects(sccBs)) {
                        validSCC = false;
                    }
                }

                if(validSCC && !sccBs.get(root)){
                    for (int i = 0; i < n; i++) {
                        if(!sccBs.get(i)){
                            for (int j = 0; j < n; j++) {
                                if (sccBs.get(j)){
                                    if(matrix[i][j] < minimumInCol){
                                        minimumInCol = matrix[i][j];
                                    }
                                }
                            }
                        }
                    }
                }

                double minimum = minimumInCol; //Math.max(minimumInRow, minimumInCol);
                if(!sccBs.get(root) && validSCC){
                    if (minimum > bigValue*0.9){
                        System.out.println("found inconsistency in edmonds ");
                    }

                    componentFound = true;

                    penalizeCycle(sccBs, matrix, minimum,  A);
                    lb += minimum;
                }
            }
            if(!componentFound){
                shouldStop = true;
            }
        }
        return lb;
    }


    private void penalizeCycle(BitSet cycle, int[][] matrix, double k, BitSet[] A){
        for (int i = 0; i < n; i++) {
            for (int j = cycle.nextSetBit(0); j >= 0; j = cycle.nextSetBit(j + 1)) {
                if (!cycle.get(i))
                    matrix[i][j] -= k;
                if(matrix[i][j] == 0){
                    A[i].set(j);
                }
            }
        }
    }
}
