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
		if(iter == 5){
			int a =3;
		}
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

	public static List<Integer> dfsFindCycle(int[] matching, int node, Set<Integer> visited,
											 Map<Integer, Integer> parent, Set<Integer> recStack) {
		visited.add(node);
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
		if (!visited.contains(i)) {
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
		//TODO check je fais quoi avec ça, est-ce que j'exécute juste si countStars est n? ou >n/2? ou 3n/4 ?
		if(matching == null && !ignoreStars || countStars(matching) < nRemaining){
			//System.out.println("ShouldntHappen");
			return new Result(0, matrix, null);
		}
		//for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
		//	for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){

		count++;

		if(count == 1){
			int a =3;
		}
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
		//Force 1-tree, maybe not necessary
			/*	new int[n - 1][n - 1];
		for (int i = 1; i < n; i++)
			System.arraycopy(starZeros[i], 1, edges[i - 1], 0, n - 1);*/

		Set<Integer> visited = new HashSet<>();
		List<List<Integer>> cycles = new ArrayList<>();

		// Find cycle
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
			if (!visited.contains(i) /*&& cycle == null*/) {
				List<Integer> cycle = dfsFindCycle(matching, i, visited,
						new HashMap<>(), new HashSet<>());
				int k = 5;
				if (cycle != null && cycle.size() < n && cycle.size() == 2 /*&& (cycle.size() < nRemaining/k || cycle.size() > nRemaining-nRemaining/k)*/ ) {
					cycles.add(cycle);
				}
			}
		}

		boolean foundZeroCol = false;
		boolean foundZeroRow = false;

		for(List<Integer> cycle : cycles){
			BitSet cycleBs = createBitsetFromList(cycle);
			double minimumInCol = bigValue;
			for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
				if(!cycleBs.get(i)){
					for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){
						if (cycleBs.get(j)){
							minimumInCol = Math.min(minimumInCol, matrix[i][j]);
						}
					}
				}
			}

			double minimumInRow = bigValue;
			for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
				if(cycleBs.get(i)){
					for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){
						if (!cycleBs.get(j)){
							minimumInRow = Math.min(minimumInRow, matrix[i][j]);
						}
					}
				}
			}

			double minimum = Math.max(minimumInRow, minimumInCol);

			if (minimum > bigValue*0.9){
				if(minimumInRow > bigValue*0.9 && minimumInCol > bigValue*0.9){
					if(!foundZeroRow || !foundZeroCol){
						System.out.println("found inconsistency in edmonds ");
						this.fails();
					}
					minimum = 0;
				} else{
					minimum = Math.min(minimumInRow,minimumInCol);
				}
			}

			if(minimum > 0){
			//	System.out.println("penalized " + cycle + " amount " + minimum);
			}
			//System.out.println("rc before " + Arrays.deepToString(reducedCosts));
			lb -= penalizeCycle(cycle, matrix, minimum);

			//TODO faire ça plus concis dans penalizeCycle
			for (int col = remainingCols.nextSetBit(0); col >= 0; col = remainingCols.nextSetBit(col + 1)){
				double min = Double.POSITIVE_INFINITY;
				for (int row = remainingRows.nextSetBit(0); row >= 0; row = remainingRows.nextSetBit(row + 1))
					min = Math.min(min, matrix[row][col]);

				lb += min;

				for (int row = remainingRows.nextSetBit(0); row >= 0; row = remainingRows.nextSetBit(row + 1))
					matrix[row][col] -= min;
			}

			//System.out.println("rc after " + Arrays.deepToString(reducedCosts));
		}


		// Column reduction USELESS



		//System.out.println("rc after all " + Arrays.deepToString(reducedCosts));
		return new Result(lb, matrix, null);
	}


	private double penalizeCycle(List<Integer> cycle, double[][] matrix, double k){
		int rowsPenalized = 0;
		for (int i : cycle){
			if(remainingRows.get(i)){
				rowsPenalized++;
				for(int j : cycle){
					if (remainingCols.get(j) && i != j) {
						matrix[i][j] += k;
						/*if (i == 23 && j == 20 || i == 20 && j == 23) {
							System.out.println("[CRITICAL-PENALIZE] cycle=" + cycle + " arc(" + i + "," + j + ") k=" + k
									+ " newValue=" + matrix[i][j] + " worldindex=" + model.getEnvironment().getWorldIndex());
						}
						System.out.println("[PENALIZE] cycle=" + cycle + " i=" + i + " j=" + j
								+ " k=" + k + " worldindex=" + model.getEnvironment().getWorldIndex());*/
					}
				}
			}
		}
		return (rowsPenalized-1) * k;
	}

	private BitSet createBitsetFromList(List<Integer> list){
		BitSet bs = new BitSet(n);
		for (int i = 0; i < list.size(); i++) {
			bs.set(list.get(i));
		}
		return bs;
	}

	int boundDecreased = 0;

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
			//cyclesState[i] = model.getEnvironment().makeBitSet(n);
			//penaltiesState[i] = model.getEnvironment().makeFloat();
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

	public PropFusionAsymUndirectedGraphVar(UndirectedGraphVar graph, IntVar cost, int[][] costMatrix, boolean interleave) {
		this(new Variable[]{graph, cost}, costMatrix);
		g = graph.getUB();
		gV = graph;
		costVar = cost;
		this.deltaMonitor = gV.monitorDelta(this);
		this.interleave = interleave;
	}

	private void undoEdmondsPenality(int from, int to){

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
		// TODO
		/*if(gV.getPotNeighOf(from).size() == 2){
			if(g.getNeighOf(from).size() == 2){
				int neigh = g.getNeighOf(from).min();
				if (neigh == from - n)
					neigh = g.getNeighOf(from).max();
				arcEnforcedPropagation(from, neigh);
			}
		}*/

		//System.out.println("arcRemovedProp " + from + " -> " + to);

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
			//throw new RuntimeException();
		}
		if(from == to) return;
		if (arcsEnforcedFromState.quickGet(from) != -1){
			int a =3;
		}

		if(reducedCosts[from][to] >= bigValue*0.9){
			int a =3;
		}
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

	int setRedCount = 0;
	private void setReducedCostsFromState(){
		setRedCount++;
		if(setRedCount == 13){
			int a =3;
		}
		remainingRows = new BitSet(n);
		remainingCols = new BitSet(n);
		remainingRows.flip(0,n);
		remainingCols.flip(0,n);

		for (int i = 0; i < n; i++) {
			if(arcsEnforcedFromState.quickGet(i) != -1){
				if(remainingCols.cardinality() != remainingRows.cardinality()){
					int a =3;
				}
				remainingRows.clear(i);
				remainingCols.clear(arcsEnforcedFromState.quickGet(i));
				if(remainingCols.cardinality() != remainingRows.cardinality()){
					int a =3;
				}
			}
		}
		if(iter == 4){
			int a = 3;
		}
		if(iter == 5){
			int a =3;
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
		//System.out.println("graph iter "+ iter + " " +gV.toString());
		//System.out.println("worldindex " + model.getEnvironment().getWorldIndex());
		//System.out.println("graph " + g.toString());
		//System.out.println("nremaining " + nRemaining);
		//System.out.println(model.getSolver().getDecisionPath());
		deltaMonitor.freeze();
		try{
			//System.out.println("lowerbound " + lowerBound);
			//System.out.println("iter " + iter + "reduced costs " + Arrays.deepToString(reducedCosts));
			//System.out.println("remainingRows " + remainingRows.toString());
			//System.out.println("remainingCols " + remainingCols.toString());

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

		//System.out.println("befHung iter " + iter + "reduced costs " + Arrays.deepToString(reducedCosts));
		if(iter == 5){
			int a =3;
		}
		justHungFW();

		if(interleave){
			fusionRelaxationAsym();
		}
		int a =3;

		//propagate(evtMask);
	}

	public void propagate(int evtmask) throws ContradictionException {
	//	deltaMonitor.unfreeze();
		//System.out.println("iter " + iter + "reduced costs " + Arrays.deepToString(reducedCosts));
		setReducedCostsFromState();
		remainingRows = new BitSet(n);
		remainingCols = new BitSet(n);
		remainingRows.flip(0,n);
		remainingCols.flip(0,n);
		nRemaining = remainingRows.cardinality();

		//graphData += gV.graphVizExport() + "\n---\n";
		if (firstProp){
			enforceInitial();
			firstProp = false;
		}

		if (waitFirstSol && getModel().getSolver().getSolutionCount() == 0) {
			return;//the UB does not allow to prune
		}
		// initialisation
		setCosts();
		int lb;
		lb = costVar.getLB();
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

	int getNb2Cycles(int[] matching){
		Set<Integer> visited = new HashSet<>();
		List<List<Integer>> cycles = new ArrayList<>();
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
			if (!visited.contains(i) /*&& cycle == null*/) {
				List<Integer> cycle = dfsFindCycle(matching, i, visited,
						new HashMap<>(), new HashSet<>());
				int k = 5;
				if (cycle != null && cycle.size() < n && cycle.size() == 2/* && (cycle.size() < nRemaining/k || cycle.size() > nRemaining-nRemaining/k)*/ ) {
					cycles.add(cycle);
				}
			}
		}
		return cycles.size();
	}

	double lbBegin = 0;

	protected void justHungFW() throws ContradictionException{
		//System.out.println("start");

		double maxLb;
		maxLb = Double.NEGATIVE_INFINITY;
		Result result = null;
		int maxNonImprove = 1;
		nbSprints = n;
		int nonImprove = 0;
		int i = 0;
		lbBegin = lowerBound;
		boolean shouldContinue = true;
		int hungIters = 0;

		//undoAllCycles();

		if(iter ==5){
			int a =3;
		}
		result = hungarianSSP(reducedCosts);
		lowerBound += result.lb;
		reducedCosts = result.array;

		basicFiltering(reducedCosts, lowerBound);

		if (lowerBound - Math.floor(lowerBound) < 0.001) {
			lowerBound = Math.floor(lowerBound);
		}

		if((lowerBound - M*n) == 1845){
			int a = 3;
		}
		try{
			costVar.updateLowerBound((int) Math.ceil(lowerBound), this);
		}
		catch(ContradictionException e) {
			//System.out.println("pruned node due to AP bound " + (lowerBound - M*n));
			throw e;
		}
		//System.out.println(i);

		result = hungarianSSP(reducedCosts);

		if(iter == 537){
			int a =3;
		}

		if((lowerBound - M*n) == 1845){
			int a = 3;
		}
		lowerBound += result.lb;
		reducedCosts = result.array;

		if (result.matching!= null){
			bestMatching = result.matching;
		}

		logState();

		if(interleave){
			//undoAllCycles();
		}

		if((removed > 0)){
			filterFloydWarshallNew(lowerBound, result.matching);
		}

		if((lowerBound - M*n) == 1845){
			int a = 3;
		}

		//System.out.println("lb after AP : " +(lowerBound - M*n));
		if(removed > 0){
			//System.out.println("at iter " + iter + " removed by AP : " + removed);
		}
		removed = 0;
		boundDecreased = 0;

		iter++;
	}

	protected void fusionRelaxationAsym() throws ContradictionException {
		//System.out.println("start");
		double maxLb = lowerBound;
		maxLb = Double.NEGATIVE_INFINITY;
		Result result = null;
		int maxNonImprove = 1;
		nbSprints = n;
		int nonImprove = 0;
		int i = 0;
		lbBegin = lowerBound;
		boolean shouldContinue = true;

		//undoAllCycles();
		while (shouldContinue && i < nbSprints && nonImprove < maxNonImprove){
			result = hungarianSSP(reducedCosts);
			lowerBound += result.lb;
			reducedCosts = result.array;

			basicFiltering(reducedCosts, lowerBound);
			if (lowerBound > maxLb /*+ bonusPen*/) {
				if(i == 1){
					int a =3;
				}
				//System.out.println("at iter " + i + " lowerbound increased");
				maxLb = lowerBound;
				if (result.matching!= null){
					bestMatching = result.matching;
				}
				nonImprove = 0;
			}
			else {
				nonImprove++;
			}
			//System.out.println(getNb2Cycles(result.matching));

			if(interleave){
				try{
					result = edmonds2cycles(reducedCosts, false, result.matching);
				}
				catch (ContradictionException e){
					System.out.println("edmondsThrow");
					throw e;
				}
				if(result.lb < 0){
					int a =3;
				}
				lowerBound += result.lb;
				/*if(result.lb == 0){
					shouldContinue = false;
				}*/
			} else {
				/*while(result.lb > 0) {
					//TODO doesnt work for now, should ignoreStars
					result = edmondsIteration(reducedCosts, false, result.matching);
					lowerBound += result.lb;
					basicFiltering(reducedCosts, lowerBound);
					if(result.lb > 0){
						int a =3;
					}
				}*/
			}

			//System.out.println("lb before floor : " + lowerBound);
			if (lowerBound - Math.floor(lowerBound) < 0.001) {
				lowerBound = Math.floor(lowerBound);
			}
			//System.out.println("lb after floor : " + lowerBound);

			//System.out.println(maxLb - lbBegin);

			try{
				costVar.updateLowerBound((int) Math.ceil(maxLb), this);
			}
			catch(ContradictionException e) {
				//System.out.println("at iter " + iter + " pruned node due to AP+1arbo bound " + (maxLb - M*n));
			}
			i++;
		}
        //System.out.println(i);

		if(costVar.getUB() - maxLb < maxLb/2){
			//filterBigReducedCosts(maxLb, bestReducedCosts);
		}

		/*result = hungarianSSP(reducedCosts);
		lowerBound += result.lb;
		reducedCosts = result.array;

		//logState();

		if(interleave){
			//undoAllCycles();
		}

		//TODO put back here whats on top of interleave)

		if(removed > 0){
		//	System.out.println("Before FW removed " + removed + " at iter " + iter);
		}
		//System.out.println("RealLowerBound : " + getRealLowerBound(result.zeros)+ " ReportedLowerBound : " + (lowerBound-M*n));
		if((removed > 0)){
			filterFloydWarshallNew(lowerBound, result.matching);
		}

		//System.out.println("lb after AP + 1-arbo : " + (maxLb - M*n));
		if(removed > 0) {
			//System.out.println("at iter " + iter + "removed by AP + 1-arbo : " + removed);
		}*/
		removed = 0;
		boundDecreased = 0;
		//count = 0;
	}

	private void logState() throws ContradictionException {
		updateRemaining();
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)) {
				reducedCostsState[i][j].set(reducedCosts[i][j]);
			}
		}
		//hungarianIteration(reducedCosts);
		if(lowerBound > lbBegin){
			int a =3;
		}
		lowerBoundState.set(lowerBound);
	}

	private void updateRemaining() throws ContradictionException {
        boolean justAssigned = false;
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			if(g.getNeighOf(i+n).size() == 2){
				boolean mirrorPresent = g.getNeighOf(i+n).contains(i);
				if (!mirrorPresent) {
					System.out.println("mirrorNotPresent");
					// two genuine candidates remain — NOT forced, don't enforce
				} else{
					int neigh = g.getNeighOf(i+n).min();
					if (neigh == i)
						neigh = g.getNeighOf(i+n).max();

					if(i == 20 && neigh == 18){
						justAssigned = true;
					}
					for (int j = 0; j < n; j++) {
						if(arcsEnforcedFromState.quickGet(j) == neigh){
							//TODO optimize this, detect this case earlier?
							int a =3;
							System.out.println("Error12");
							this.fails();
						}
					}
					//System.out.println("[FUSION][UPDATEREMAINING-ENFORCE] " + (i+n) + " -> " + neigh);

					if(i == 23){
						int a =3;
					}
					gV.enforceArc(i+n, neigh, this);
					//arcEnforcedPropagation(i+n, neigh);
					if(reducedCosts[i][neigh] != 0){
						int a =3;
					}
				}
			}
		}
	}

	public int getRealLowerBound(int[] matching){
		int lb = 0;
		for (int i = 0; i < n; i++) {
			if(arcsEnforcedFromState.quickGet(i) != -1){
				lb += originalSmallCosts[i][arcsEnforcedFromState.quickGet(i)];
			}
			else{
				lb += originalSmallCosts[i][matching[i]];
			}

		}
		return lb;
	}


	//OLD*********************


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
		//System.out.println("[FUSION][REMOVE] " + from + " -> " + to);
		removed++;
		//System.out.println("reduced cost before removing " + Arrays.deepToString(reducedCosts));
		//System.out.println("removed " + from + " -> " + to);
		gV.removeArc(from, to, this);
	}

	public void enforce(int from, int to) throws ContradictionException {
		//System.out.println("[FUSION][ENFORCE] " + from + " -> " + to);
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

	public boolean isMandatory(int i, int j) {
		return gV.getMandNeighOf(i).contains(j);
	}
}
