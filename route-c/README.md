# Route C: strong cliques and the eighteen bound

Route C follows the corrected nineteen theorem of Route B. It studies the eighteen-fold bound
$|F|\le 18\nu_s^G(F)+\tau_G(F)$ for prescribed edge sets in graphs of maximum degree at most four.
Here $\tau_G(F)$ adds $\max\{0,|F\cap E(C)|-18\}$ over the original components $C$ isomorphic to
$C_5[2]$.

- [Manuscript (PDF)](manuscript/eighteen.pdf)
- [Editable mathematical source](manuscript/eighteen.md)
- [PDF build provenance](manuscript/pdf-build.json)
- [Lean formalization of Proposition 1.1](lean/README.md)

## Results and their status

| Result | Statement | Status |
| --- | --- | --- |
| Proposition 1.1 | All eighteen edges of $C_9(1,3)$ pairwise conflict, so $\nu_s=m/18$. This refutes Joos's conjecture $\nu_s\ge m/17$ (arXiv:1407.8336v1, Conjecture 2). | Paper proof, a direct check, and a Lean formalization ([route-c/lean](lean/README.md)) |
| Theorem 1.2 | Every strong clique with at least nineteen edges lies inside a $C_5[2]$ component. | Paper reduction plus an exhaustive SAT search with two independent solvers |
| Corollary 1.3 | Without $C_5[2]$ components the strong clique number is at most eighteen, attained by $C_9(1,3)$. | Follows from Theorem 1.2 and Proposition 1.1 |
| Theorem 1.5 | The eighteen bound holds for $F=E(G)$ and whenever $\nu_s^G(F)\le 1$; it is sharp. | Paper proof using Joos's theorem and Theorem 1.2 |
| Proposition 1.6 | The eighteen bound implies the nineteen bound of Route B. | Paper proof |
| Conjecture 1.4 | The eighteen bound for every prescribed edge set. | **Open** |

Theorem 1.2 removes the conflict-degree hypothesis from Route B's nineteen-clique rigidity theorem
([manuscript Theorem 6.1](../route-b/manuscript/packing19.md#6-stage-3-nineteen-clique-rigidity-through-a-closed-support)).

**Not established.**
- Only Proposition 1.1 is formalized in Lean ([route-c/lean](lean/README.md)). Theorem 1.2 and the results that depend on it are not.
- The SAT results carry no DRAT or LRAT certificates.
- The search is trustworthy only to the extent that the encoder is correct. For this reason the
  manuscript reports positive and negative controls.

## Reproduce

Python 3.12 or later with `python-sat` (tested with 1.9.dev17) and `networkx`. Run from the repository root:

```sh
python route-c/scripts/check_circulant.py
python route-c/scripts/run_search.py --jobs 12
python route-c/scripts/quartic_clique_numbers.py 13
python route-c/scripts/enumerate_quartic.py 10
```

The scripts do the following:
- `check_circulant.py` checks Proposition 1.1 in pure Python.
- `run_search.py` runs every instance of manuscript Section 5 with CaDiCaL 1.5.3 and Glucose 4.
  It writes [sat-results.json](results/sat-results.json) and [the logs](results/logs/); about 20
  minutes with 12 parallel jobs.
- `quartic_clique_numbers.py` computes the strong clique number of every connected 4-regular graph
  with at most thirteen vertices and writes [quartic-clique-numbers.json](results/quartic-clique-numbers.json).
- `enumerate_quartic.py` regenerates the graph lists in [data/quartic](data/quartic/), whose counts
  agree with OEIS A006820.

To rebuild the PDF, use the dependencies of Route B's PDF builder; see the
[Route B manuscript guide](../route-b/manuscript/README.md). Then run:

```sh
python route-c/scripts/build-manuscript-pdf.py
```

## Provenance

The search programs, the enumeration and the manuscript were developed with Claude Opus 5.5
(Anthropic), used through Claude Code under Congyue Mao's direction. They began as exploratory
scripts (`exp10`, `exp17*`) in the research archive
[strong-edge-colouring-research](https://github.com/congyuemao/strong-edge-colouring-research).
The scripts in this directory are the maintained versions, and the published logs were produced
with them. External human peer review is not claimed.
