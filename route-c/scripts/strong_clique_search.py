"""Exhaustive SAT search for strong cliques in graphs of maximum degree at most four.

Instance I_n (manuscript Section 5): a graph H on n labelled vertices with maximum degree at most
four and an edge set F of size s such that every vertex is an endpoint of F and any two disjoint
edges of F are joined by an edge of H.  Only edges inside V(F) can witness a conflict, and
dropping edges that leave V(F) only relaxes the degree bound, so UNSAT is conclusive.  With
--not-c52 (used for n = 10) some vertex must have at most three neighbours, which excludes
exactly the 4-regular ten-vertex case of Lemma 4.1.

Optional sound strengthenings (UNSAT stays conclusive):
  --sym    relabel so that F-degrees are non-increasing (instead of fixing the F-edge {0,1});
  --count  the incidence inequality C(s,2) <= (3/2) sum_x d_F(x)^2 of the manuscript (Lemma 3.1);
  --lex    (with --sym) for i < j of equal F-degree, row i of the F-adjacency matrix without columns
           i, j is lexicographically <= row j (Codish-Miller-Prosser-Stuckey); the lex-least labelling
           among degree-ordered ones satisfies it, so it is compatible with --sym.
  --regular-check  instance R: n = 10, every vertex has degree exactly 4, s = 19 edges of F pairwise
           conflict, and the twentieth edge fails to conflict with some edge of F.

Usage: python route-c/scripts/strong_clique_search.py n s [--not-c52] [--sym] [--count] [--lex]
       [--regular-check] [--solver cadical|glucose]"""
import itertools
import sys
import time

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical153, Glucose4


def build(n, s, not_c52, sym=False, count=False, lex=False, regular=False):
    pool = IDPool()
    P = list(itertools.combinations(range(n), 2))
    a = {p: pool.id(("a",) + p) for p in P}
    f = {p: pool.id(("f",) + p) for p in P}
    cl = []
    for p in P:
        cl.append([-f[p], a[p]])
    for x in range(n):
        inc = [a[p] for p in P if x in p]
        cl += CardEnc.atmost(inc, 4, vpool=pool, encoding=EncType.seqcounter).clauses
        cl.append([f[p] for p in P if x in p])            # x is an endpoint of F
    cl += CardEnc.equals([f[p] for p in P], s, vpool=pool, encoding=EncType.seqcounter).clauses
    e = lambda x, y: a[(min(x, y), max(x, y))]
    for p, q in itertools.combinations(P, 2):
        if set(p) & set(q):
            continue
        (x, y), (z, w) = p, q
        cl.append([-f[p], -f[q], e(x, z), e(x, w), e(y, z), e(y, w)])
    if sym or count:
        # unary F-degree literals ge[x][k] <-> d_F(x) >= k  (k = 1..4)
        ge = {}
        for x in range(n):
            lits = [f[p] for p in P if x in p]
            prev = {}
            for i, l in enumerate(lits):
                cur = {}
                for k in range(1, min(4, i + 1) + 1):
                    v = pool.id(("ge", x, i, k))
                    cur[k] = v
                    aa = prev.get(k)
                    bb = prev.get(k - 1) if k > 1 else None
                    if aa is not None:
                        cl.append([-aa, v])
                    if k == 1:
                        cl.append([-l, v])
                        cl.append([-v, l] + ([aa] if aa else []))
                    else:
                        if bb is not None:
                            cl.append([-bb, -l, v])
                            cl.append([-v, bb] + ([aa] if aa else []))
                            cl.append([-v, l] + ([aa] if aa else []))
                        else:
                            cl.append([-v] + ([aa] if aa else []))
                prev = cur
            ge[x] = {k: prev[k] for k in prev}
    if lex:
        assert sym
        fe = lambda x, y: f[(min(x, y), max(x, y))]
        for i in range(n):
            for j in range(i + 1, n):
                eq = pool.id(("eqdeg", i, j))      # eq -> d(i) = d(j)  (given d(i) >= d(j): d(i)>=k -> d(j)>=k)
                for k in ge[i]:
                    cl.append([-eq, -ge[i][k]] + ([ge[j][k]] if k in ge[j] else []))
                # conversely d(i) = d(j) -> eq   (so that the constraint is imposed whenever degrees tie)
                diff = []
                for k in ge[i]:
                    dk = pool.id(("dk", i, j, k))   # dk <-> ge_i[k] and not ge_j[k]
                    cl.append([-dk, ge[i][k]])
                    if k in ge[j]:
                        cl.append([-dk, -ge[j][k]])
                        cl.append([dk, -ge[i][k], ge[j][k]])
                    else:
                        cl.append([dk, -ge[i][k]])
                    diff.append(dk)
                cl.append([eq] + diff)
                cols = [c for c in range(n) if c not in (i, j)]
                prev = None                          # prefix-equality literal
                for c in cols:
                    ai, bj = fe(i, c), fe(j, c)
                    pre = [-eq] + ([-prev] if prev else [])
                    cl.append(pre + [-ai, bj])       # lex: at the first difference, row i has 0, row j has 1
                    e = pool.id(("lexeq", i, j, c))
                    # e -> prefix equal so far and ai == bj
                    if prev:
                        cl.append([-e, prev])
                    cl.append([-e, -ai, bj]); cl.append([-e, ai, -bj])
                    cl.append([e] + ([-prev] if prev else []) + [-ai, -bj])
                    cl.append([e] + ([-prev] if prev else []) + [ai, bj])
                    prev = e
    if regular:
        # every vertex has exactly 4 neighbours; some non-F edge fails to conflict with some F-edge
        for x in range(n):
            cl += CardEnc.atleast([a[p] for p in P if x in p], 4, vpool=pool, encoding=EncType.seqcounter).clauses
        bad = []
        for p, q in itertools.combinations(P, 2):
            for g, h in ((p, q), (q, p)):
                if set(g) & set(h):
                    continue
                (x, y), (z, w) = g, h
                u = pool.id(("bad",) + g + h)    # u -> g non-F edge, h F-edge, no witness
                cl += [[-u, a[g]], [-u, -f[g]], [-u, f[h]],
                       [-u, -e(x, z)], [-u, -e(x, w)], [-u, -e(y, z)], [-u, -e(y, w)]]
                bad.append(u)
        cl.append(bad)
    if sym:
        for x in range(n - 1):
            for k in range(1, 5):
                if k in ge[x + 1]:
                    cl.append([-ge[x + 1][k]] + ([ge[x][k]] if k in ge[x] else []))
    else:
        cl.append([f[(0, 1)]])
    if count:
        # sum_x d^2 = sum_x sum_k (2k-1)[d >= k] >= ceil(2/3 * C(s,2))
        need = -(-2 * (s * (s - 1) // 2) // 3)
        lits = [ge[x][k] for x in range(n) for k in ge[x] for _ in range(2 * k - 1)]
        cl += CardEnc.atleast(lits, need, vpool=pool, encoding=EncType.seqcounter).clauses
    if not_c52:
        low = []
        for x in range(n):
            lx = pool.id(("low", x))
            am = CardEnc.atmost([a[p] for p in P if x in p], 3, vpool=pool, encoding=EncType.seqcounter)
            cl += [[-lx] + c for c in am.clauses]
            low.append(lx)
        cl.append(low)
    return cl, a, f, P


def main():
    n, s = int(sys.argv[1]), int(sys.argv[2])
    not_c52 = "--not-c52" in sys.argv
    solver = Glucose4 if "glucose" in sys.argv else Cadical153
    sym, count, lex = "--sym" in sys.argv, "--count" in sys.argv, "--lex" in sys.argv
    regular = "--regular-check" in sys.argv
    cl, a, f, P = build(n, s, not_c52, sym, count, lex, regular)
    t0 = time.time()
    S = solver(bootstrap_with=cl)
    ok = S.solve()
    tag = (f"n={n} s={s}{' not-C5[2]' if not_c52 else ''}{' sym' if sym else ''}"
           f"{' count' if count else ''}{' lex' if lex else ''}{' R' if regular else ''} [{solver.__name__}]")
    print(f"{tag}: {'SAT' if ok else 'UNSAT'}  clauses={len(cl)}  [{time.time()-t0:.1f}s]", flush=True)
    if ok:
        mod = set(l for l in S.get_model() if l > 0)
        print("   F =", [p for p in P if f[p] in mod])
        print("   graph =", [p for p in P if a[p] in mod])


if __name__ == "__main__":
    main()
