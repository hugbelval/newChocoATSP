package org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangian;

import org.chocosolver.solver.exception.ContradictionException;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class EdmondsAlgorithm {
    private static BitSet remainingRows;
    private static BitSet remainingCols;

    static int n;

    public static BitSet sccToPenalize;

    public static BitSet[] A = null;

    public static void resetEdmonds(){
       A = null;
    }

    public static PropFusionAsymUndirectedGraphVar.Result increasingEdmonds(
            double[][] matrix,
            int[] matching,
            BitSet remainingRows,
            BitSet remainingCols
    ) throws ContradictionException {
        n = matrix[0].length;
        resetEdmonds();
        double totalIncrementalLb = 0;
        for (int i = 1; i < n; i++) {
            sccToPenalize = new BitSet(n+1);
            sccToPenalize.set(i);
            totalIncrementalLb += fullEdmondsSCC(matrix, matching, remainingRows, remainingCols, -1).lb;
        }
        return new PropFusionAsymUndirectedGraphVar.Result(totalIncrementalLb, matrix, matching);
    }

    public static PropFusionAsymUndirectedGraphVar.Result fullEdmondsSCC(
            double[][] matrix,
            int[] matching,
            BitSet remainingRows,
            BitSet remainingCols,
            int tailleMaxCycles
    ) throws ContradictionException {
        EdmondsAlgorithm.remainingRows = remainingRows;
        EdmondsAlgorithm.remainingCols = remainingCols;
        n = matrix.length;

        int root = 0;

        int n = matrix.length;
        double lb = 0;

        if(tailleMaxCycles != -1){
            sccToPenalize = new BitSet(n+1);
            for (int i = 0; i <= tailleMaxCycles; i++) {
               sccToPenalize.set(i);
            }
        }

        if(A == null || tailleMaxCycles != -1){
            A = new BitSet[n];
            for (int i =0; i<n; i++){
                A[i] = new BitSet(n);
                int j = matching[i];
                if (j != root){
                    A[i].set(j);
                }
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
                double minimumInCol = PropFusionAsymUndirectedGraphVar.bigValue;

                for (int i = 0; i < n; i++) {
                    if (sccBs.get(i)) continue;
                    if (!sccToPenalize.get(scc.size()) || A[i].intersects(sccBs)) {
                        validSCC = false;
                    }
                }

                if(validSCC && !sccBs.get(root)){
                    for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
                        if(!sccBs.get(i)){
                            for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){
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
                    if (minimum > PropFusionAsymUndirectedGraphVar.bigValue*0.9){
                        //System.out.println("found inconsistency in edmonds ");
                        throw new ContradictionException();
                    }

                    componentFound = true;

                    penalizeSCC(sccBs, matrix, minimum, A);
                    lb += minimum;
                }
            }
            if(!componentFound){
                shouldStop = true;
            }
        }
        return new PropFusionAsymUndirectedGraphVar.Result(lb, matrix, null);
    }

    private static void penalizeCycle(BitSet cycle, double[][] matrix, double k, boolean penalizeCols){
        if(!penalizeCols){
            for (int i = cycle.nextSetBit(0); i >= 0; i = cycle.nextSetBit(i + 1)){
                for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){
                    if(remainingRows.get(i) && !cycle.get(j))
                        matrix[i][j] -= k;
                }
            }
        }
        else{
            for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
                for (int j = cycle.nextSetBit(0); j >= 0; j = cycle.nextSetBit(j + 1)) {
                    if (remainingCols.get(j) && !cycle.get(i))
                        matrix[i][j] -= k;
                }
            }
        }
    }

    private static void penalizeSCC(BitSet cycle, double[][] matrix, double k, BitSet[] A){
        for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
            for (int j = cycle.nextSetBit(0); j >= 0; j = cycle.nextSetBit(j + 1)) {
                if (remainingCols.get(j) && !cycle.get(i))
                    matrix[i][j] -= k;
                if(matrix[i][j] == 0){
                    A[i].set(j);
                }
            }
        }
    }

    private static BitSet createBitsetFromList(List<Integer> list){
        BitSet bs = new BitSet(n);
        for (int i = 0; i < list.size(); i++) {
            bs.set(list.get(i));
        }
        return bs;
    }

    private static List<Integer> dfsFindCycle(int[] matching, int node, BitSet visited,
                                             Map<Integer, Integer> parent, Set<Integer> recStack) {
        visited.set(node);
        recStack.add(node);
        int i = matching[node];
        if(i == -1){
            //No outgoing arc
            return null;
        }
        if (recStack.contains(i)) {
            parent.put(i, node);
            List<Integer> cycle = new ArrayList<>();

            int x = node;
            cycle.add(x);
            while (x != i) {
                x = parent.get(x);
                cycle.add(0, x);
            }
            return cycle;
        }

        // If not visited → recurse
        if (!visited.get(i)) {
            parent.put(i, node);
            List<Integer> cycle = dfsFindCycle(matching, i, visited, parent, recStack);
            if (cycle != null && !cycle.isEmpty()) {
                return cycle;
            }
        }

        recStack.remove(node);
        return null;  // no cycle found
    }
}
