"""Strong clique numbers of all connected 4-regular graphs on 5 <= n <= N vertices.

Reads route-c/data/quartic/graphs_n<n>.txt (produced by enumerate_quartic.py; the counts agree
with OEIS A006820) and computes the largest set of pairwise conflicting edges exactly, as a
maximum clique of the conflict graph.  Usage: python route-c/scripts/quartic_clique_numbers.py N"""
import collections
import json
from pathlib import Path
import sys

import networkx as nx

DATA = Path(__file__).resolve().parents[1] / "data" / "quartic"


def conflict_graph(G):
    E = [tuple(sorted(e)) for e in G.edges()]
    H = nx.Graph()
    H.add_nodes_from(range(len(E)))
    for i in range(len(E)):
        a, b = E[i]
        for j in range(i + 1, len(E)):
            c, d = E[j]
            if {a, b} & {c, d} or any(G.has_edge(x, y) for x in (a, b) for y in (c, d)):
                H.add_edge(i, j)
    return H


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    c52 = nx.Graph([((i, p), ((i + 1) % 5, q)) for i in range(5) for p in range(2) for q in range(2)])
    c9 = nx.circulant_graph(9, [1, 3])
    summary = {}
    for n in range(5, N + 1):
        hist = collections.Counter()
        large = []
        for line in (DATA / f"graphs_n{n}.txt").read_text().splitlines():
            G = nx.Graph([tuple(map(int, t.split("-"))) for t in line.split()])
            w = nx.max_weight_clique(conflict_graph(G), weight=None)[1]
            hist[w] += 1
            if w >= 18:
                large.append({"strong_clique_number": w, "is_C5[2]": nx.is_isomorphic(G, c52),
                              "is_C9(1,3)": nx.is_isomorphic(G, c9)})
        summary[n] = {"graphs": sum(hist.values()), "distribution": dict(sorted(hist.items())),
                      "strong_clique_at_least_18": large}
        print(n, summary[n], flush=True)
    out = Path(__file__).resolve().parents[1] / "results" / "quartic-clique-numbers.json"
    out.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
