"""Check Proposition 1.1: all eighteen edges of C9(1,3) pairwise conflict, so nu_s = 1 = m/18.

Pure Python; prints the counts and exits with status 1 if a check fails."""
import itertools
import sys


def circulant(n, steps):
    return sorted({tuple(sorted((i, (i + s) % n))) for i in range(n) for s in steps})


def main():
    edges = circulant(9, (1, 3))
    adj = {v: set() for v in range(9)}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)

    def conflict(e, f):
        return bool(set(e) & set(f)) or any(y in adj[x] for x in e for y in f)

    pairs = list(itertools.combinations(edges, 2))
    missing = [(e, f) for e, f in pairs if not conflict(e, f)]
    degrees = sorted(len(adj[v]) for v in adj)
    nu = max(k for k in range(1, 4) for S in itertools.combinations(edges, k)
             if all(not conflict(e, f) for e, f in itertools.combinations(S, 2)))
    print(f"edges={len(edges)} degrees={set(degrees)} conflicting_pairs={len(pairs) - len(missing)}/{len(pairs)} "
          f"nu_s={nu}")
    ok = len(edges) == 18 and degrees == [4] * 9 and not missing and nu == 1
    print("OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
