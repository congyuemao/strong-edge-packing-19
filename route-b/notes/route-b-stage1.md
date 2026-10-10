# Route B: exact compensation and critical configurations

Date: 11 October 2026 (Australia/Sydney).

For the consolidated proof matching the optimized Lean source, see the [complete English manuscript](../manuscript/packing19.md). This note retains the Stage 1 research sequence.

**Evidence status.** Section 1 identifies existing Lean results. Sections 2-7 were originally paper derivations. The [new Lean extension](../lean/README.md) now checks the exact compensation identity, tertiary optimization, critical degree range, full-degree witness, and full-neighbourhood closure. Other derivations retain their paper status unless explicitly listed there. Section 8 records the tasks proposed at the end of Stage 1. No 39-edge enumeration was performed in Stage 1, and Stage 1 did not prove the 19 bound or exclude any of its five critical parameter rows.

## 1. Pinned source, definitions, and theorem interfaces

Upstream: [strong-edge-packing-195](https://github.com/congyuemao/strong-edge-packing-195), commit `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`.

The README and English manuscript were read, together with the following definitions, theorem interfaces, and relevant structural proofs:

| Subject | Lean source and declarations |
| --- | --- |
| Full original-graph conflicts and candidate restriction | `Basic.lean`: `StrongConflict`, `conflictGraph`, `candidateConflictGraph` |
| Private sets containing their centres | `Basic.lean`: `IsPrivate`, `private_centre`, `private_isClique` |
| Secondary optimization and private degree monotonicity | `PrivateExchange.lean`: `IsOptimal`, `private_degree_mono` |
| Closed-neighbourhood counting | `DoubleCount.lean`: `covering`, `sum_covering`, `sum_privateOwners`, `private_double_count` |
| The local 39 bound without twenty-cliques | `MinimalPacking195.lean`: `local39_of_clique_bounds` |
| Five full-conflict-degree thresholds | `Bounds/High20Improved.lean`, `High21Improved.lean`, `High22Improved.lean`, `High23Improved.lean`, `High24.lean` |
| Saturation, conflict closure, and doubled-cycle structure | `Bounds/TwentyCliqueComponent.lean`, `TwentyCliqueRigidity.lean` |
| Removal of complete exceptional components | `Packing195Unconditional.lean`, `TightComponents.lean` |

An important interface distinction: `CliqueBounds195.high24` only requires an upper bound of **14**, sufficient for the local 39 estimate. The actual theorem `high24_clique_card_le_thirteen` proves **13**. Excluding degree 24 from the zero-deficit cases below uses the stronger theorem, not merely the weaker record field.

In `StrongConflict`, the intermediate edge ranges over the full `G.edgeSet`. The candidate conflict graph is formed by restricting the vertices of the complete conflict graph. Closed private neighbourhoods include their centres.

The final theorem `induced_matching_packing195_with_connected_component_count` assumes original maximum degree at most four, in addition to the usual finite and decidable instances, and concludes

\[
\exists M\subseteq F:\quad M\text{ is an induced matching in }G,
\qquad 2|F|\le39|M|+t_G(F).
\]

Its final interface asserts existence, not optimality of the returned matching. The optimized maximum independent sets used here are supplied by the intermediate `optimal_exists` and private-neighbourhood arguments.

The 75 Lean files and four environment/launcher files were compared byte for byte with the existing local project used for verification. See [verification scope](../verification/README.md). An incremental build is not a clean-cache rebuild.

## 2. Notation and optimization

Write

\[
\widehat H=L(G)^2,\quad H=\widehat H[F],\quad
c(x)=d_{\widehat H}(x),\quad d(x)=d_H(x).
\]

Thus `c` denotes full conflict degree and `d` denotes candidate conflict degree, with `d(x) <= c(x) <= 24`.

Choose a maximum independent set `M`, and among such sets minimize

\[
\sum_{e\in M}d(e).
\]

This secondary objective uses degrees in **H**, not full degrees in the original conflict graph. Replacing it by a full-degree objective would not justify the candidate-degree monotonicity needed below.

Define

\[
P_e=\{x\in F:N_H[x]\cap M=\{e\}\},\quad
m(x)=|N_H[x]\cap M|,
\]

\[
L(e)=d(e)+1+|P_e|,\quad \delta(e)=39-L(e),\quad
R=\sum_{x\in F,\ m(x)\ge3}(m(x)-2).
\]

Before removing complete exceptional components, `delta` is an integer: neither nonnegativity nor truncated natural-number subtraction may be assumed.

The standard exchange arguments give:

1. `m(x) >= 1`. Maximality alone suffices for this.
2. `e` belongs to `P_e`, and `P_e` is contained in `N_H[e]`.
3. `P_e` is a clique. Otherwise two nonadjacent private vertices replace its centre and increase the independent-set size.
4. `d(x) >= d(e)` for `x` in `P_e`. Otherwise a one-vertex exchange preserves cardinality and lowers the secondary objective.

Items 3 and 4 correspond to existing Lean lemmas.

## 3. Exact compensation identity

The private sets are disjoint, and their union consists exactly of the vertices with `m(x)=1`. Therefore

\[
\sum_{e\in M}|P_e|=|\{x\in F:m(x)=1\}|. \tag{3.1}
\]

Counting incidences `(x,e)` with `e` in `M` and `x` in `N_H[e]` gives

\[
\sum_{e\in M}(d(e)+1)=\sum_{x\in F}m(x). \tag{3.2}
\]

For every integer `m >= 1`,

\[
m+\mathbf1_{m=1}=2+
\begin{cases}
0,&m=1,2,\\
m-2,&m\ge3.
\end{cases} \tag{3.3}
\]

Summing yields the exact identity

\[
\boxed{\sum_{e\in M}L(e)=2|F|+R,} \tag{3.4}
\]

and hence

\[
\boxed{2|F|=39|M|-\sum_{e\in M}\delta(e)-R.} \tag{3.5}
\]

These equalities hold for any maximal independent set in any finite simple graph. They do not require the original-degree bound, the structural clique bounds, cardinality optimality, or the secondary optimization.

If the independent set is not maximal, uncovered vertices contribute an additional term:

\[
\sum_eL(e)=2|F|+R-2|\{x:m(x)=0\}|.
\]

This identifies exactly where the covering assumption is needed.

Upstream `DoubleCount.lean` provides the summation interfaces underlying (3.1)-(3.2) and proves `2|F| <= sum L(e)`. Keeping the excess coverage explicitly as `R` is a new paper derivation here, not an assertion that (3.5) is already formalized upstream.

## 4. Exceptional components and the correction term

For `G=C5[2]` and `F=E(G)`, the candidate conflict graph is `K20`. A maximum independent set has one member and

\[
d(e)=19,\quad |P_e|=20,\quad L(e)=40,\quad
\delta(e)=-1,\quad R=0.
\]

Equation (3.5) remains correct: `40=39-(-1)`. Thus universal nonnegativity of the deficits is false before removing full exceptional components. This is a counterexample to an incorrectly stated nonnegativity premise, not to the corrected 19 conjecture.

Let `t=t_G(F)`, and remove from the candidate set all edges of those complete exceptional components, obtaining `F_0`. Keep the original graph `G` throughout. Component rigidity and conflict closure give

\[
|F_0|=|F|-20t,\quad
\nu_s^G(F_0)=\nu_s^G(F)-t,\quad t_G(F_0)=0. \tag{4.1}
\]

Each removed component contributes exactly one matching member, independently of all other components. Consequently

\[
|F|\le19\nu_s^G(F)+t
\quad\Longleftrightarrow\quad
|F_0|\le19\nu_s^G(F_0). \tag{4.2}
\]

Without this reduction, the correct equivalence is

\[
\boxed{|F|\le19|M|+t
\quad\Longleftrightarrow\quad
\sum_e\delta(e)+R\ge|M|-2t.} \tag{4.3}
\]

An optimized maximum set has one member of deficit `-1` in each complete exceptional component. The remaining set inherits candidate-degree-sum optimality. Equivalently, define

\[
\widetilde\delta(e)=\delta(e)+
\mathbf1_{e\text{ lies in a fully selected exceptional component}}.
\]

Then all adjusted deficits are nonnegative, and the target becomes `sum adjusted_delta + R >= |M|-t`.

The remaining sections work after reduction to `t=0`, without changing the original graph.

## 5. Nonnegativity, budgets, and the invariant total

Twenty-clique rigidity implies that `H` contains no twenty-clique. Every private clique therefore has size at most nineteen. Using `c(x) >= d(x) >= d(e)` allows the original-graph threshold theorems to be applied to each private clique:

| Centre degree `d(e)` | Private-clique upper bound | Upper bound for `L(e)` |
| --- | --- | --- |
| at most 18 | `d(e)+1` | `2d(e)+2 <= 38` |
| 19 | 19 | 39 |
| 20 | 18 | 39 |
| 21 | 17 | 39 |
| 22 | 16 | 39 |
| 23 | 15 | 39 |
| 24 | 13 | 38 |

Thus every deficit is nonnegative, and

\[
\delta(e)=0\Longrightarrow
 d(e)\in\{19,20,21,22,23\},\qquad |P_e|=38-d(e). \tag{5.1}
\]

Put `k=|M|` and `Z={e in M: delta(e)=0}`. The target is equivalently

\[
\boxed{R+\sum_{e\in M\setminus Z}(\delta(e)-1)\ge|Z|.} \tag{5.2}
\]

This is the correct discharging budget: a positive-deficit centre must first retain one unit for itself; only the excess beyond one is available for zero-deficit centres.

For fixed `G,F`, every maximum independent set satisfies

\[
\sum_e\delta(e)+R=39\alpha(H)-2|F|. \tag{5.3}
\]

Exchanges between maximum independent sets cannot increase this total. They can normalize structure or redistribute its terms. A new lower bound still requires structural reasoning, or a contradiction that produces a larger independent set.

Also `sum delta + R` has the same parity as `k`. This arithmetic constraint does not prove the 19 bound.

## 6. A full-degree witness in every zero-deficit private clique

### 6.1. Paper lemma: an exact full-degree witness

If `delta(e)=0` and `d=d(e)`, then some `x` in `P_e` satisfies

\[
\boxed{c(x)=d(x)=d.} \tag{6.1}
\]

**Proof.** Every member satisfies `c(x) >= d(x) >= d`. If every full degree were at least `d+1`, the next threshold would give the respective bounds

\[
|P_e|\le18,17,16,15,13
\]

for `d=19,20,21,22,23`. These contradict the required respective sizes

\[
19,18,17,16,15.
\]

Some member therefore has `c(x) <= d`; combining the inequalities proves the claim.

This does not assert equality of the full degree for every private member or for an arbitrary initial centre.

### 6.2. Paper corollary: tertiary optimization closes every critical centre's neighbourhood

Among maximum independent sets minimizing `sum d(e)`, additionally minimize

\[
\sum_{e\in M}c(e). \tag{6.2}
\]

Such a choice exists by finiteness. For a zero-deficit centre, choose the witness in (6.1). Swapping the centre for that witness preserves independence, cardinality, and the candidate-degree sum. Tertiary optimality gives `c(e) <= c(x)=d(e)`, with the reverse inequality automatic. The case `x=e` is immediate.

Hence

\[
\boxed{\delta(e)=0\Longrightarrow c(e)=d(e),} \tag{6.3}
\]

and equality of the nested finite neighbourhoods gives

\[
\boxed{N_{\widehat H}[e]\subseteq F\qquad(e\in Z).} \tag{6.4}
\]

Every original edge conflicting with a zero-deficit centre is already a candidate. Original edges outside `F` have not been deleted: they may still witness conflicts between other candidate edges.

This normalization applies for arbitrary `k`. It uses the structural thresholds for maximum-degree-four original graphs, beyond the abstract counting identity.

## 7. The 39-edge, independence-number-two configuration

Assume

\[
|F|=39,\qquad \alpha(H)=2,\qquad t_G(F)=0,
\]

and choose `M={e_1,e_2}` under the first two optimization rules. Since `m(x) <= 2`, we have `R=0`. The identity and nonnegativity imply

\[
\delta(e_1)=\delta(e_2)=0. \tag{7.1}
\]

Write `P_i=P_{e_i}`, `p_i=|P_i|`, `d_i=d(e_i)`, and

\[
B=\{x\in F:m(x)=2\},\qquad s=|B|.
\]

The candidate set is the disjoint union of `P_1,P_2,B`, and the closed neighbourhood of centre `e_i` is the disjoint union of `P_i` and `B`. Thus

\[
d_i+1=p_i+s,\qquad p_i=38-d_i.
\]

Eliminating `p_i` gives `2d_i=37+s`, so

\[
\boxed{d_1=d_2=d,\quad p_1=p_2=38-d,\quad s=2d-37.} \tag{7.2}
\]

The five Stage 1 parameter rows are:

| `d` | `|P_1|=|P_2|` | `|B|` |
| --- | --- | --- |
| 19 | 19 | 1 |
| 20 | 18 | 3 |
| 21 | 17 | 5 |
| 22 | 16 | 7 |
| 23 | 15 | 9 |

These candidate-degree conclusions hold for every set satisfying the first two optimization rules. Adding the third rule gives

\[
c(e_1)=c(e_2)=d,\qquad
\boxed{F=N_{\widehat H}[e_1]\cup N_{\widehat H}[e_2].} \tag{7.3}
\]

Maximality proves one inclusion, and (6.4) proves the other. The intersection of the two full closed neighbourhoods is exactly `B`.

Moreover, `H` must be connected. Otherwise independence number two forces exactly two nonempty components, each a clique. Each clique has at most nineteen vertices, contradicting `|F|=39`. In particular, all candidate edges belong to one original component.

### Endpoint-neighbour cover formulation

For an original edge `e=uv`, let

\[
C(e)=(N_G(u)\setminus\{v\})\cup(N_G(v)\setminus\{u\}),
\qquad |C(e)|\le6.
\]

Let `E_G(C(e))` denote the set of original edges meeting this vertex set, rather than only its internal edges. The upstream exact-cover lemma gives

\[
N_{\widehat H}(e)=E_G(C(e)).
\]

Consequently the normalized configuration satisfies

\[
\boxed{F=\{e_1,e_2\}\cup E_G(C(e_1))\cup E_G(C(e_2)).} \tag{7.4}
\]

The centres are nonconflicting original edges. Any remaining original edge outside `F` avoids both cover sets and conflicts with neither centre.

## 8. Tasks proposed at the end of Stage 1

1. **Joint-cover structure.** For the five parameter rows, use the two original cover sets, each of size at most six, together with maximum original degree four and the private-clique sizes. Seek either a contradiction or a genuine original-graph realization.
2. **Preserve all witnesses.** Any SAT or CP-SAT model must construct the original graph before defining candidate conflicts. Equation (7.3) is a proved normalization under tertiary optimization; it does not authorize deleting other original edges.
3. **Global compensation.** Use (6.4) as an additional constraint when attempting to assign one unit of the budget in (5.2) to each zero-deficit centre. The existence of such an assignment remains unproved.
4. **Larger independent sets.** For `k=3`, the first possible uncorrected counterexample has `|F|=58` and total compensation one. Excluding `k=2` would not settle the general problem.

The identity, corrected equivalence, exact-degree witness, tertiary normalization, and two-centre parameter reduction are candidates for later Lean modules. Stage 1 introduced no Lean proof and changed no verified upstream source.
