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
import org.chocosolver.memory.IStateBitSet;
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

import java.util.Arrays;
import java.util.BitSet;

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

	protected IntVar costVar;
	protected int n;
	protected double[][] originalSmallCosts;
	protected double[][] reducedCosts;
	BitSet remainingRows;
	BitSet remainingCols;
	private IStateDouble[][] reducedCostsState;
	private IStateDouble lowerBoundState;
	private IStateIntVector arcsEnforcedFromState;
	int nRemaining;
	public static int bigValue = 2000000000;
	public static boolean executeFW = false;
	public double firstLb = Double.NEGATIVE_INFINITY;
	public int[] bestMatching;
	private double lowerBound;
	public String graphData;
	private HungarianAlgorithm hung;

	//***********************************************************************************
	// CONSTRUCTORS
	//***********************************************************************************
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

	int removed = 0;

	public void basicFiltering(double[][] reducedCostsArray, double lowerBound) throws ContradictionException {
		double delta = costVar.getUB() - lowerBound;
		if (delta < 0){
			this.fails();
		}
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)){
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)){
				if (gV.getUB().isArcOrEdge(i+n,j) && i != j && reducedCostsArray[i][j] > delta + 1e-6) {
					assert arcsEnforcedFromState.quickGet(i) != j;
					assert arcsEnforcedFromState.quickGet(i) == -1;
					reducedCostsArray[i][j] = bigValue;
					remove(i+n, j);
				}
			}
		}
	}

	////////////////////////////////////////
	int M;
	int[][] originalCostMatrix;
	protected PropFusionAsymUndirectedGraphVar(Variable[] vars, int[][] costMatrix) {
	super(vars, PropagatorPriority.QUADRATIC, false);
		graphData = "";
		n = costMatrix.length / 2;
		nRemaining = n;
		originalSmallCosts = new double[n][n];
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

		arcsEnforcedFromState = getModel().getEnvironment().makeIntVector(n, -1);
		lowerBoundState = getModel().getEnvironment().makeFloat(0);
		reducedCosts = new double[n][n];
	}
	boolean interleave;

	int tailleMaxCycles;

	ABmode abMode;

	public PropFusionAsymUndirectedGraphVar(UndirectedGraphVar graph, IntVar cost, int[][] costMatrix, ABmode abMode) {
		this(new Variable[]{graph, cost}, costMatrix);
		g = graph.getUB();
		gV = graph;
		costVar = cost;
		this.abMode = abMode;
		if(abMode == ABmode.PenIncreasingCycles){
			tailleMaxCycles = -1;
			this.interleave = true;
		}else if(abMode == ABmode.Pen2Cycles){
			tailleMaxCycles = 2;
			this.interleave = true;
		}
		else if (abMode == ABmode.PenAllCycles){
			tailleMaxCycles=n;
			this.interleave = true;
		}else if(abMode == ABmode.JustHung){
			this.interleave = false;
		}
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

	private void setReducedCosts(){
		remainingRows = new BitSet(n);
		remainingCols = new BitSet(n);
		remainingRows.flip(0,n);
		remainingCols.flip(0,n);

		nRemaining = remainingRows.cardinality();
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)) {
				reducedCosts[i][j] = originalSmallCosts[i][j];
			}
		}
		lowerBound = M * n;
	}

	private void syncWithGraph() throws ContradictionException {
		//Removed edges
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			for (int j = remainingCols.nextSetBit(0); j >= 0; j = remainingCols.nextSetBit(j + 1)) {
				if (i != j && !g.edgeExists(i + n, j)) {
					reducedCosts[i][j] = bigValue;
				}
			}
		}

		//Enforced edges
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			assert gV.getLB().getNeighOf(i + n).contains(i): "Enforced arcs don't contain negative infinite Jonker Volgenant arc";
			assert gV.getLB().getNeighOf(i + n).size() <= 2: "More than 2 adjacent arcs enforced";
			for (int j : gV.getLB().getNeighOf(i + n).toArray()) {
				if (j < n && j != i && remainingCols.get(j)) {
					enforceMatch(i, j);
					break;
				}
			}
		}
	}

	private void enforceInReducedCosts(int from, int to){
		for (int i = 0; i < n; i++) {
			reducedCosts[i][to] = bigValue;
		}

		for (int j = 0; j < n; j++) {
			reducedCosts[from][j] = bigValue;
		}
		reducedCosts[from][to] = 0;
	}

	private void enforceMatch(int i, int j) throws ContradictionException {
		//Ceci ne fait rien, probablement car un autre propagateur a déja fait ce cleanup.
		removeAlternativesForEnforcedEdges(i + n, j);
		removeAlternativesForEnforcedEdges(j, i + n);
		if (!remainingRows.get(i) || !remainingCols.get(j)) return;
		//remainingRows.clear(i);
		//remainingCols.clear(j);
		//nRemaining--;
		assert reducedCosts[i][j] == originalSmallCosts[i][j];
		lowerBound += reducedCosts[i][j];
		enforceInReducedCosts(i, j);
	}

	private void removeAlternativesForEnforcedEdges(int from, int to) throws ContradictionException {
		if (g.getNeighOf(from).size() != 2) {
			for (int nb : g.getNeighOf(from).toArray()) {
				if (nb != to && nb != from + n && nb != from - n){
					remove(from, nb);
				}
			}
		}
	}

	public void propagate(int evtmask) throws ContradictionException {
		if (firstProp) {
			remainingRows = new BitSet(n);
			remainingCols = new BitSet(n);
			remainingRows.flip(0, n);
			remainingCols.flip(0, n);
			nRemaining = n;

			enforceInitial();            // enforces (i+n,i), removes the infinite zones
			lowerBound = M * n;
			//logState();                // trailed copy of reducedCosts and lowerBound
			firstProp = false;
		}
		setReducedCosts();

		updateEnforcedArcs();
		syncWithGraph();  // cleanup() in enforceMatch can remove edges, so sync again

		//logState();
		removed = 0;

		//Pour le moment pas de réduction de remainingRows.
		assert remainingRows.cardinality() == n;
		assert remainingCols.cardinality() == n;
		justHungFW();
		if (interleave){
			edmonds();
		}
	}

	int iter = 0;

	int fwRemoves = 0;



	protected void justHungFW() throws ContradictionException{
		Result result = hung.execute(reducedCosts, remainingRows, remainingCols);
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

		matching = result.matching;
		if(executeFW){
			filterAugmentedReducedCosts();
		}

		removed = 0;
		iter++;
	}

	private void filterAugmentedReducedCosts() throws ContradictionException {
		double[][] augmentedRc = ReducedCostsAugmenter.augmentReducedCostsFW(matching, remainingRows, remainingCols, reducedCosts);
		basicFiltering(augmentedRc, lowerBound);
	}

	int[] matching;


	public PropFusionAsymUndirectedGraphVar.Result increasingEdmonds(
			double[][] matrix,
			int[] matching
	) throws ContradictionException {
		EdmondsAlgorithm.resetEdmonds();
		removed = 0;
		double totalIncrementalLb = 0;
		for (int i = 1; i < n; i++) {
			EdmondsAlgorithm.sccToPenalize = new BitSet(n+1);
			EdmondsAlgorithm.sccToPenalize.set(i);
			lowerBound += EdmondsAlgorithm.fullEdmondsSCC(matrix, matching, remainingRows, remainingCols, -1).lb;
			basicFiltering(matrix, lowerBound);
			if(removed > 0){
				//System.out.println("at iteration " + i + " removed " + removed);
			}
			removed = 0;
		}
		return new PropFusionAsymUndirectedGraphVar.Result(totalIncrementalLb, matrix, matching);
	}

	protected void edmonds() throws ContradictionException {
		Result result;
		removed = 0;
		if(abMode == ABmode.PenIncreasingCycles){
			result = increasingEdmonds(reducedCosts, matching);
		}
		else{
			result = EdmondsAlgorithm.fullEdmondsSCC(reducedCosts, matching, remainingRows, remainingCols, tailleMaxCycles);
		}
		lowerBound += result.lb;
		reducedCosts = result.array;

		if (lowerBound - Math.floor(lowerBound) < 0.001) {
			lowerBound = Math.floor(lowerBound);
		}

		basicFiltering(reducedCosts, lowerBound);

		costVar.updateLowerBound((int) Math.ceil(lowerBound), this);

		removed = 0;
	}

	private void updateEnforcedArcs() throws ContradictionException {
		for (int i = remainingRows.nextSetBit(0); i >= 0; i = remainingRows.nextSetBit(i + 1)) {
			if(g.getNeighOf(i+n).size() == 2){
				int neigh = g.getNeighOf(i+n).min();
				if (neigh == i)
					neigh = g.getNeighOf(i+n).max();
				gV.enforceArc(i+n, neigh, this);
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
