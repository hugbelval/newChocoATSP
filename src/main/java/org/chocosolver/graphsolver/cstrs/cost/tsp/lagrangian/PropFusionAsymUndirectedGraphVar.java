/*
 * Copyright (c) 1999-2014, Ecole des Mines de Nantes
 * All rights reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the Ecole des Mines de Nantes nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE REGENTS AND CONTRIBUTORS BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangian;

import org.chocosolver.graphsolver.variables.GraphEventType;
import org.chocosolver.graphsolver.variables.UndirectedGraphVar;
import org.chocosolver.graphsolver.variables.delta.GraphDeltaMonitor;
import org.chocosolver.memory.IStateDouble;
import org.chocosolver.memory.IStateIntVector;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.Variable;
import org.chocosolver.solver.variables.events.IntEventType;
import org.chocosolver.util.ESat;
import org.chocosolver.util.objects.graphs.UndirectedGraph;
import org.chocosolver.util.procedure.PairProcedure;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * TSP Lagrangian relaxation
 * Inspired from the work of Held & Karp
 * and Benchimol et. al. (Constraints 2012)
 *
 * @author Jean-Guillaume Fages
 */
public class PropFusionAsymUndirectedGraphVar extends Propagator<Variable> {

	//***********************************************************************************
	// VARIABLES
	//***********************************************************************************

	protected UndirectedGraph g;
	protected UndirectedGraphVar gV;
	private GraphDeltaMonitor deltaMonitor;
	private PairProcedure onArcRemoved;
	private PairProcedure onArcEnforced;

	protected IntVar costVar;
	protected int n;
	protected int[][] originalSmallCosts;
	protected double[][] costs;
	protected double[][] reducedCosts;
	private IStateDouble[][] reducedCostsState;
	private IStateDouble lowerBoundState;
	private IStateIntVector arcsEnforcedFromState;
	BitSet remainingRows;
	BitSet remainingCols;
	int nRemaining;
	protected boolean waitFirstSol;
	protected int nbSprints;
	private static int bigValue = 2000000000;
	public double firstLb = Double.NEGATIVE_INFINITY;
	public int[] bestMatching;

	private double lowerBound;
	public String graphData;
	private HungarianAlgorithm hung;

	//***********************************************************************************
	// CONSTRUCTORS
	//***********************************************************************************

	public Result hungarianSSP(double[][] costs){
		Result result = hung.execute(costs, remainingRows, remainingCols);
		return result;
	}

	public Result hungarianIteration(double[][] costs){
		Result result = hung.executeOneIter(costs, remainingRows, remainingCols);
		return result;
	}


	private int countStars(int[] matching) {
		int count = 0;
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1))
				if (matching[i] != -1)
					count++;
		return count;
	}


	public static class Result {
		public final double lb;
		public final double[][] array;
		public final int[] matching;

		public Result(double lb, double[][] array, int[] matching) {
			this.lb = lb;
			this.array = array;
			this.matching = matching;
		}
	}

	public static List<Integer> dfsFindCycle(int[] matching, int node, BitSet visited,
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

	int removed = 0;

	public void basicFiltering(double[][] reducedCostsArray, double lowerBound) throws ContradictionException {
		double delta = costVar.getUB() - lowerBound;
		/*System.out.println("[DELTA-CHECK] ub=" + costVar.getUB()
				+ " lowerBound=" + String.format("%.10f", lowerBound)
				+ " delta=" + String.format("%.10f", delta)
				+ " worldindex=" + model.getEnvironment().getWorldIndex());*/
		if (delta < 0){
			this.fails();
		}
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){
				if(arcsEnforcedFromState.quickGet(i) != -1){
					int a =3;
				}
				if (gV.getUB().isArcOrEdge(i+n,j) && i != j && reducedCostsArray[i][j] > delta) {
					if (i == 23 && j == 20) {
						/*System.out.println("[CRITICAL-REMOVE] arc(23,20) reducedCost=" + reducedCostsArray[i][j]
								+ " delta=" + delta + " worldindex=" + model.getEnvironment().getWorldIndex());*/
					}
					reducedCostsArray[i][j] = bigValue;
					if (arcsEnforcedFromState.quickGet(i) == j) {
						System.out.println("[BUG] basicFiltering tried to remove an enforced arc " + i + "->" + j + " world=" + model.getEnvironment().getWorldIndex());
					}
					remove(i+n, j);
				}
			}
		}
		//mandFiltering();
	}

	int count = 0;


	public Result edmonds2cycles(
			double[][] matrix,
			boolean ignoreStars,
			int[] matching
	) throws ContradictionException {
		//TODO pour le moment je pénalise juste un cycle par itération
		//for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
		//	for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){

		count++;

		int n = matrix.length;
		double lb = 0;
		if(!ignoreStars){
		} else {
			throw new RuntimeException("Error352");
		}

		for (int i = remainingRows.nextClearBit(0); i < n; i = remainingRows.nextClearBit(i + 1)){
			//Met les zéros des arcs obligatoires
			matching[i] = arcsEnforcedFromState.quickGet(i);
		}

		BitSet visited = new BitSet(n);
		List<List<Integer>> cycles = new ArrayList<>();

		// Find cycle
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
			if (!visited.get(i) /*&& cycle == null*/) {
				List<Integer> cycle = dfsFindCycle(matching, i, visited,
						new HashMap<>(), new HashSet<>());
				int k = 5;
				if (cycle != null && cycle.size() < n && cycle.size() <= tailleMaxCycles /*&& (cycle.size() < nRemaining/k || cycle.size() > nRemaining-nRemaining/k)*/ ) {
					cycles.add(cycle);
				}
			}
		}


		for(List<Integer> cycle : cycles){
			BitSet cycleBs = createBitsetFromList(cycle);
			double minimumInCol = bigValue;
			for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
				if(!cycleBs.get(i)){
					for (int j = cycleBs.nextSetBit(0); j >= 0; j = cycleBs.nextSetBit(j + 1)){
						if(remainingCols.get(j)){
							minimumInCol = Math.min(minimumInCol, matrix[i][j]);
						}
					}
				}
			}

			double minimumInRow = bigValue;
			for (int i = cycleBs.nextSetBit(0); i >= 0; i = cycleBs.nextSetBit(i + 1)){
				if(remainingRows.get(i)){
					for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){
						if (!cycleBs.get(j)){
							minimumInRow = Math.min(minimumInRow, matrix[i][j]);
						}
					}
				}
			}

			double minimum;
			boolean penalizeCols;
			if(minimumInCol > minimumInRow){
				minimum = minimumInCol;
				penalizeCols = true;
			}
			else {
				minimum = minimumInRow;
				penalizeCols = false;
			}

			if(minimumInRow > bigValue*0.9 || minimumInCol > bigValue*0.9) {
				System.out.println("found inconsistency in edmonds ");
				this.fails();
			}

			//System.out.println("penalized " + cycle + "amount " + minimum);
			penalizeCycle(cycleBs, matrix, minimum, penalizeCols);
			lb += minimum;
		}

		return new Result(lb, matrix, null);
	}


	public Result fullEdmondsSCC(
			double[][] matrix,
			boolean ignoreStars,
			int[] matching
	) throws ContradictionException {
		count++;

		int root = 0;

		int n = matrix.length;
		double lb = 0;
		if(!ignoreStars){
		} else {
			throw new RuntimeException("Error352");
		}


		for (int i = remainingRows.nextClearBit(0); i < n; i = remainingRows.nextClearBit(i + 1)){
			matching[i] = arcsEnforcedFromState.quickGet(i);
		}

		List<Integer>[] A = new List[n];
		for (int i =0; i<n; i++){
			A[i] = new ArrayList<>();
			int j = matching[i];
			if (j != root){
				A[i].add(j);
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
				int minimumi = -1;
				int minimumj = -1;

				for (int i = 0; i < n; i++) {
					if (sccBs.get(i)) continue;
					for (int j : A[i]) {
						if (sccBs.get(j)) {
							validSCC = false;
						}
					}
				}

				if(validSCC && !sccBs.get(root)){
					for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
						if(!sccBs.get(i)){
							for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){
								if (sccBs.get(j)){
									if(matrix[i][j] < minimumInCol){
										minimumInCol = matrix[i][j];
										minimumi = i;
										minimumj = j;
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
						this.fails();
					}

					A[minimumi].add(minimumj);
					componentFound = true;

					penalizeCycle(sccBs, matrix, minimum, true);
					lb += minimum;
				}
			}
			if(!componentFound){
				shouldStop = true;
			}
		}
		return new Result(lb, matrix, null);
	}

	private void penalizeCycle(BitSet cycle, double[][] matrix, double k, boolean penalizeCols){
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

	private BitSet createBitsetFromList(List<Integer> list){
		BitSet bs = new BitSet(n);
		for (int i = 0; i < list.size(); i++) {
			bs.set(list.get(i));
		}
		return bs;
	}


	////////////////////////////////////////
	int M;
	int[][] originalCostMatrix;
	protected PropFusionAsymUndirectedGraphVar(Variable[] vars, int[][] costMatrix) {
	super(vars, PropagatorPriority.QUADRATIC, true);
		graphData = "";
		n = costMatrix.length / 2;
		nRemaining = n;
		originalSmallCosts = new int[n][n];
		originalCostMatrix = costMatrix;
		hung = new HungarianAlgorithm(n);
		M = costMatrix[n][0];
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				if (i == j){
					originalSmallCosts[i][j] = bigValue;
				} else {
					originalSmallCosts[i][j] = costMatrix[i+n][j];
				}
			}
		}


		reducedCostsState = new IStateDouble[n][n];
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				reducedCostsState[i][j] = model.getEnvironment().makeFloat();
			}
		}

		arcsEnforcedFromState = model.getEnvironment().makeIntVector(n, -1);
		lowerBoundState = model.getEnvironment().makeFloat(0);

		costs = new double[n][n];
		reducedCosts = new double[n][n];
		this.onArcRemoved = this::arcRemovedPropagation;
		this.onArcEnforced = this::arcEnforcedPropagation;
	}
	boolean interleave;

	int tailleMaxCycles;

	public PropFusionAsymUndirectedGraphVar(UndirectedGraphVar graph, IntVar cost, int[][] costMatrix, boolean interleave) {
		this(new Variable[]{graph, cost}, costMatrix);
		g = graph.getUB();
		gV = graph;
		costVar = cost;
		this.deltaMonitor = gV.monitorDelta(this);
		if(interleave){
			tailleMaxCycles = 2;
		}else{
			tailleMaxCycles=n;
		}
		this.interleave = true;

	}


	//***********************************************************************************
	// HK Algorithm(s)
	//***********************************************************************************

	//////////////////////UTILS/////////////

	boolean firstProp = true;
	////////////////////////////////////////
	double baseLowerBound = 0;
	private void enforceInitial() throws ContradictionException {
		 for (int i = 0; i < n; i++) {
        //System.out.println("[FUSION][INIT-ENFORCE] " + (i+n) + " -> " + i);
        gV.enforceArc(i+n, i, this);
        baseLowerBound += M;
        for (int j = 0; j < n; j++) {
            //System.out.println("[FUSION][INIT-REMOVE] " + i + " -> " + j);
            gV.removeArc(i,j, this);
            //System.out.println("[FUSION][INIT-REMOVE] " + (i+n) + " -> " + (j+n));
            gV.removeArc(i+n,j+n, this);
        }
    }
	}

	private void arcRemovedPropagation(int from, int to) throws ContradictionException {
		if (from >= n && to < n) {
			from = from % n;
		}
		else if (from < n && to >= n) {
			int temp = to;
			to = from;
			from = temp % n;
		}
		else{
			return;
			//C'est ok, c'est un arc dans les zones infini
		}
		if(from == to) return;
		reducedCosts[from][to] = bigValue;
	}

	private void arcEnforcedPropagation(int from, int to) throws ContradictionException {
		if(g.getNeighOf(from).size() != 2){
			for (int neigh: g.getNeighOf(from).toArray()) {
				if(neigh != to && neigh != from+n && neigh != from-n){
					remove(from, neigh);
					arcRemovedPropagation(from, neigh);
				}
			}
		}
		if(!g.edgeExists(from, to)){
			System.out.println(from + "->" + to + " is enforced but dont exist");
		}

		if (from >= n && to < n) {
			from = from % n;
		}
		else if (from < n && to >= n) {
			int temp = to;
			to = from;
			from = temp % n;
		}
		else{
			//TODO pas normal d'arriver ici
			System.out.println("Error42");
			throw new RuntimeException();
		}

		if(from == to) return;
		if (arcsEnforcedFromState.quickGet(from) == to) return;
		if (!remainingRows.get(from) || !remainingCols.get(to)) return;

		arcsEnforcedFromState.set(from, to);
		if(remainingRows.get(from) && remainingCols.get(to)){
			remainingRows.clear(from);
			remainingCols.clear(to);
			nRemaining--;
			lowerBound += reducedCosts[from][to];
		}
	}

	private void setReducedCostsFromState(){
		remainingRows = new BitSet(n);
		remainingCols = new BitSet(n);
		remainingRows.flip(0,n);
		remainingCols.flip(0,n);

		for (int i = 0; i < n; i++) {
			if(arcsEnforcedFromState.quickGet(i) != -1){
				remainingRows.clear(i);
				remainingCols.clear(arcsEnforcedFromState.quickGet(i));
			}
		}
		nRemaining = remainingRows.cardinality();
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)) {
				reducedCosts[i][j] = reducedCostsState[i][j].get();
			}
		}
		lowerBound = lowerBoundState.get();
	}

	public void propagate(int idVar, int evtMask) throws ContradictionException {
		setReducedCostsFromState();
		updateRemaining();
		deltaMonitor.freeze();
		try{
			if(GraphEventType.isRemArc(evtMask)){
				deltaMonitor.forEachArc(onArcRemoved, GraphEventType.REMOVE_ARC);
			}

			if(GraphEventType.isAddArc(evtMask)){
				deltaMonitor.forEachArc(onArcEnforced, GraphEventType.ADD_ARC);
			}
		}
		finally {
			deltaMonitor.unfreeze();
		}

		logState();
		removed = 0;
		justHungFW();

		if(interleave){
			fusionRelaxationAsym();
		}
	}

	public void propagate(int evtmask) throws ContradictionException {
		setReducedCostsFromState();
		remainingRows = new BitSet(n);
		remainingCols = new BitSet(n);
		remainingRows.flip(0,n);
		remainingCols.flip(0,n);
		nRemaining = remainingRows.cardinality();

		if (firstProp){
			enforceInitial();
			firstProp = false;
		}

		if (waitFirstSol && getModel().getSolver().getSolutionCount() == 0) {
			return;//the UB does not allow to prune
		}
		// initialisation
		setCosts();
		reducedCosts = Arrays.stream(costs).map(double[]::clone).toArray(double[][]::new);
		lowerBound = M*n;
		justHungFW();
		if(interleave){
			fusionRelaxationAsym();
		}

		if(firstLb == Double.NEGATIVE_INFINITY){
			firstLb = costVar.getLB();
		}
	}


	int iter = 0;

	int fwRemoves = 0;
	private void filterFloydWarshallNew(double lowerBound, int[] matching) throws ContradictionException {
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
		int before = removed;
		//System.out.println("bigReduced " + Arrays.deepToString(bigReducedCosts));
		basicFiltering(bigReducedCosts, lowerBound);
		fwRemoves += removed - before;
	}

	private double getCostFlow(int from, int to, int[] matching){
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

	double lbBegin = 0;

	protected void justHungFW() throws ContradictionException{
		nbSprints = n;
		lbBegin = lowerBound;


		Result result = hungarianSSP(reducedCosts);
		lowerBound += result.lb;
		reducedCosts = result.array;

		basicFiltering(reducedCosts, lowerBound);

		if (lowerBound - Math.floor(lowerBound) < 0.001) {
			lowerBound = Math.floor(lowerBound);
		}

		costVar.updateLowerBound((int) Math.ceil(lowerBound), this);

		if (result.matching!= null){
			bestMatching = result.matching;
		}

		logState();

		matching = result.matching;
		if((removed > 0)){
			filterFloydWarshallNew(lowerBound, matching);
		}

		removed = 0;
		iter++;
	}

	int[] matching;

	protected void fusionRelaxationAsym() throws ContradictionException {
		double maxLb = Double.NEGATIVE_INFINITY;
		Result result;
		nbSprints = n;
		int i = 0;
		lbBegin = lowerBound;
		removed = 0;

		result = hungarianSSP(reducedCosts);
		lowerBound += result.lb;
		reducedCosts = result.array;

		basicFiltering(reducedCosts, lowerBound);
		if (lowerBound > maxLb) {
			maxLb = lowerBound;
			if (result.matching!= null){
				bestMatching = result.matching;
			}
		}

		try{
			if(tailleMaxCycles > 2){
				result = fullEdmondsSCC(reducedCosts, false, result.matching);
			} else{
				result = edmonds2cycles(reducedCosts, false, result.matching);
			}
		}
		catch (ContradictionException e){
			System.out.println("edmondsThrow");
			throw e;
		}
		lowerBound += result.lb;
		reducedCosts = result.array;

		if (lowerBound > maxLb) {
			maxLb = lowerBound;
		}

		//System.out.println("lb before floor : " + lowerBound);
		if (lowerBound - Math.floor(lowerBound) < 0.001) {
			lowerBound = Math.floor(lowerBound);
		}

		basicFiltering(reducedCosts, lowerBound);
		//if(removed > 0)
		//System.out.println("removed " + removed + " at iter " + iter);
		/*if((removed > 0)){
			filterFloydWarshallNew(lowerBound, matching);
		}*/

		costVar.updateLowerBound((int) Math.ceil(maxLb), this);

		removed = 0;

	}

	private void logState() throws ContradictionException {
		updateRemaining();
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)) {
				reducedCostsState[i][j].set(reducedCosts[i][j]);
			}
		}
		lowerBoundState.set(lowerBound);
	}

	private void updateRemaining() throws ContradictionException {
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			if(g.getNeighOf(i+n).size() == 2){
				int neigh = g.getNeighOf(i+n).min();
				if (neigh == i)
					neigh = g.getNeighOf(i+n).max();

				for (int j = 0; j < n; j++) {
					if(arcsEnforcedFromState.quickGet(j) == neigh){
						//TODO optimize this, detect this case earlier?
						System.out.println("Error12");
						this.fails();
					}
				}
				gV.enforceArc(i+n, neigh, this);
				if(reducedCosts[i][neigh] != 0){
					int a =3;
				}
			}
		}
	}


	//***********************************************************************************
	// DETAILS
	//***********************************************************************************

	protected void setCosts() {
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				//TODO à tester ci-dessous
				if(i != j && gV.getUB().isArcOrEdge(i+n,j) /*&& !gV.getLB().arcExists(j,i)*/){
					costs[i][j] = originalSmallCosts[i][j];
				}
				else {
					costs[i][j] = bigValue;
				}
			}
		}
	}

	//***********************************************************************************
	// INFERENCE
	//***********************************************************************************
	public void remove(int from, int to) throws ContradictionException {
		removed++;
		gV.removeArc(from, to, this);
	}

	public void enforce(int from, int to) throws ContradictionException {
		gV.enforceArc(from, to, this);
	}

	public void contradiction() throws ContradictionException {
		fails();
	}

	//***********************************************************************************
	// PROP METHODS
	//***********************************************************************************

	@Override
	public int getPropagationConditions(int vIdx) {
		if (vIdx == 0) {
			return GraphEventType.REMOVE_ARC.getMask() + GraphEventType.ADD_ARC.getMask();
		} else {
			return IntEventType.boundAndInst();
		}
	}

	@Override
	public ESat isEntailed() {
		return ESat.TRUE;// it is just implied filtering
	}
}
