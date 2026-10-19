package org.chocosolver.graphsolver.cstrs.cost.tsp.lagrangian;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;
import java.util.Arrays;

// Algorithm from https://www.geeksforgeeks.org/dsa/tarjan-algorithm-find-strongly-connected-components/
public class SCCFinder {
    // A recursive DFS based function used by getSCCs()
    // u        -> The vertex to be visited next
    // disc[]   -> Stores discovery times of visited vertices
    // low[]    -> Earliest visited vertex that can be reached
    //             from subtree rooted with current vertex
    // st       -> Stack to store all active DFS vertices
    // inSt[]   -> Boolean array to check whether a node is in stack
    // timer    -> Global time counter for discovery times
    // allSCCs  -> Stores all strongly connected components
    static void findSCC(int u, List<Integer>[] adj, int[] disc, int[] low, boolean[] inSt,
                        Stack<Integer> st, int[] timer, ArrayList<ArrayList<Integer>> allSCCs) {

        // Initialize discovery time and low value
        disc[u] = low[u] = ++timer[0];

        // Push current vertex to stack and mark it as in stack
        st.push(u);
        inSt[u] = true;

        // Go through all vertices adjacent to this
        for (int v : adj[u]) {

            // If v is not visited yet, then recur for it
            // Case 1: Tree edge
            if (disc[v] == -1) {

                findSCC(v, adj, disc, low, inSt, st, timer, allSCCs);

                // Check if the subtree rooted with v has a
                // connection to one of the ancestors of u
                low[u] = Math.min(low[u], low[v]);
            }

            // Update low value of u only if v is still in stack
            // Case 2: Back edge (not cross edge)
            else if (inSt[v]) {
                low[u] = Math.min(low[u], disc[v]);
            }
        }

        // If u is head node of SCC, pop the stack and store the SCC
        if (low[u] == disc[u]) {

            ArrayList<Integer> scc = new ArrayList<>();

            // Pop all vertices from stack till u is found
            while (true) {

                int x = st.pop();
                inSt[x] = false;

                scc.add(x);

                if (x == u)
                    break;
            }

            // Store one strongly connected component
            allSCCs.add(scc);
        }
    }

    // The function to do DFS traversal.
    // It uses findSCC() to find all strongly connected components
    static ArrayList<ArrayList<Integer>> getSCCs(List<Integer>[] adj) {
        int n = adj.length;

        int[] disc = new int[n];
        int[] low = new int[n];
        boolean[] inSt = new boolean[n];
        Arrays.fill(disc, -1);

        Stack<Integer> st = new Stack<>();
        int[] timer = new int[1];

        ArrayList<ArrayList<Integer>> allSCCs = new ArrayList<>();

        // Call the recursive helper function to find SCCs
        // in DFS tree with vertex i
        for (int i = 0; i < n; i++) {

            if (disc[i] == -1) {
                findSCC(i, adj, disc, low, inSt, st, timer, allSCCs);
            }
        }

        //Partie ajoutée par moi

        ArrayList<ArrayList<Integer>> multipleVertexSCCs = new ArrayList<>();

        for (int i = 0; i < allSCCs.size(); i++) {
            if(allSCCs.get(i).size() > 1) {
                multipleVertexSCCs.add(allSCCs.get(i));
            }
        }

        return multipleVertexSCCs;
        //return allSCCs;
    }

    /*
    public static void main(String[] args) {
        List<Integer>[] adj = new int[6][];
        adj[0] = new int[]{1};
        adj[1] = new int[]{2};
        adj[2] = new int[]{0, 3};
        adj[3] = new int[]{4};
        adj[4] = new int[]{3, 5};
        adj[5] = new int[]{};

        ArrayList<ArrayList<Integer>> sccs = getSCCs(adj);

        System.out.println("Strongly Connected Components:");

        for (ArrayList<Integer> scc : sccs) {
            for (int x : scc) {
                System.out.print(x + " ");
            }
            System.out.println();
        }
    }
    */
}
