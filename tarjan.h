/* tarjan.h
 *
 * Implementation of Tarjan's algorithm to determine if a 
 * subshift of finite type is transitive.
 * This code is adapted from pseudocode in the Wikipedia article
 * on Tarjan's algorithm.
 */

#pragma once
#include <vector>
#include <stack>
#include <iostream>
#include <fstream>
#include <cassert>

// A class representing a directed graph
class Graph {
public:
    /* A vector of length exactly N.
     * adj[i] is a list of integers j
     * where there is a directed edge from i to j.
     */
    std::vector< std::vector<int> > adj;

    // We keep track of self-edges separately.
    std::vector<bool> selfedge;

    Graph(int N) : adj(N), selfedge(N, false) {}

    size_t size() { return adj.size(); }

    void addEdge(size_t i, size_t j) {
        assert(i >= 0);
        assert(i < adj.size());
        assert(j >= 0);
        assert(j < adj.size());

        if (i == j)
            selfedge[i] = true;
        else
            adj[i].push_back(j);
    }

    bool hasEdge(size_t i, size_t j) {
        if (i == j)
            return selfedge[i];

        return find(adj[i].begin(), adj[i].end(), j) != adj[i].end();
    }

    // Export adjacency matrix as a csv file
    void exportAdjMatrix(const std::string& filename) {
        std::ofstream f(filename);
        assert(f.is_open());

        size_t N = adj.size();
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < N; ++j) {
                if (j > 0)
                    f << ",";
                f << (hasEdge(i,j) ? "1" : "0");
            }
            f << std::endl;
        }
    }
};


// Data structures associated to Tarjan's algorithm.
class Tarjan {
public:
    Graph& G;
    int index;
    std::stack<int> S;
    std::vector<bool> onStack;
    std::vector<int> discovery;
    std::vector<int> lowlink;

    std::vector<std::vector<int> > components;

    static const int NIL = -1;

    Tarjan(Graph& G) :
        G(G), index(0), S(),
        onStack(G.size(), false),
        discovery(G.size(), NIL),
        lowlink(G.size(), NIL) {}

    void push(int v) {
        S.push(v);
        onStack[v] = true;
    }

    int pop() {
        assert(not S.empty());
        int w = S.top();
        S.pop();
        onStack[w] = false;
        return w;
    }

    // Pop SCC rooted at v from the stack and into components
    void makeSCC(int v) {
        std::vector<int> scc;
        int w;
        // Pop vertices up to and including v
        do {
            assert(not S.empty());
            w = pop();
            scc.push_back(w);
        } while (w != v);
        components.push_back(scc);
    }

    // The core recursive function in Tarjan's algorithm
    void strongconnect(int v) {
        discovery[v] = index;
        lowlink[v] = index;
        ++index;
        push(v);

        // Consider successors of v
        for (int w : G.adj[v]) {
            if (discovery[w] == NIL) {
                // Successor w has not yet been visited; recurse on it
                strongconnect(w);
                lowlink[v] = std::min(lowlink[v], lowlink[w]);
            }
            else if (onStack[w]) {
                // Successor w is in stack S and hence in the current SCC
                lowlink[v] = std::min(lowlink[v], discovery[w]);
            }

            // If w is not on stack, then (v, w) is an edge pointing
            // to an SCC already found and must be ignored.
        }

        // If v is a root node, pop the stack and generate an SCC
        if (lowlink[v] == discovery[v])
            makeSCC(v);
    }

    // Populate the components vector with all of the SCCs
    void run() {
        // Test to ensure we only run this once.
        assert(discovery[0] == NIL);

        int N = G.size();
        for (int v = 0; v < N; ++v)
            if (discovery[v] == NIL)
                strongconnect(v);
    }
};


// Tests if a subshift of finite type is transitive.
inline bool isTransitive(Graph& G) {
    Tarjan T(G);
    T.run();

    /* Determine the number of non-trivial connected components.
     * These are components which either have multiple vertices,
     * or a single vertex with a self-edge which would correspond
     * a fixed point in the subshift of finite type.
     */
    int count = 0;
    for (auto scc : T.components)
        if (scc.size() > 1 or G.selfedge[scc[0]])
            ++count;

    assert (count > 0);
    return count == 1;
}

// Print diagnostic output about the strongly connected components.
inline void diagnoseTransitivity(Graph &G) {
    Tarjan T(G);
    T.run();

    using std::cout, std::endl;

    int n = G.size();

    int self = 0;
    int nonself = 0;
    for (int i = 0; i < n; ++i) {
        if (G.selfedge[i])
            ++self;
        nonself += G.adj[i].size();
    }

    cout << "    vertices: " << n << endl;
    cout << "    self edges: " << self << endl;
    cout << "    non-self edges: " << nonself << endl;


    /* Determine the number of non-trivial connected components.
     * These are components which either have multiple vertices,
     * or a single vertex with a self-edge. The latter corresponds
     * to a fixed point in the subshift of finite type.
     */
    int count = 0;
    for (auto scc : T.components) {
        if (scc.size() > 1) {
            cout << "    non-trivial scc with " << scc.size()
                 << " vertices" << endl;
            ++count;
        }
        if (scc.size() == 1 and G.selfedge[scc[0]]) {
            cout << "    non-trivial scc with " << scc.size()
                 << " vertex, index = " << scc[0] << endl;
            ++count;
        }
    }

    cout << "    total count " << count << " non-trivial "
         << (count == 1 ? "scc" : "sccs" ) << endl;
}

// Return indices that are not in a large scc.
inline std::vector<int> badIndices(Graph &G) {
    Tarjan T(G);
    T.run();

    // Determine the number vectices in the largest scc.
    int big = 0;
    for (auto scc : T.components) {
        int size = scc.size();
        if (size > big)
            big = size;
    }

    // Accumulate vertices from all smaller non-trivial sccs.
    std::vector<int> acc;
    for (auto scc : T.components) {
        int size = scc.size();
        assert(size <= big);
        if (size == big)
            continue;
        if (size == 1 and not G.selfedge[scc[0]])
            continue;
        acc.insert(acc.end(), scc.begin(), scc.end()); 
    }

    return acc;
}
