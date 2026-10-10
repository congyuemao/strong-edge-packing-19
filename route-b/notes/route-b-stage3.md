# Route B, Stage 3: rigidity of critical private cliques

Date: 11 October 2026 (Australia/Sydney).

**Status: the full corrected packing theorem and the core rigidity theorem are now Lean-verified.** The [new Lean extension](../lean/README.md) proves Theorems 1.1 and 1.2, including the required Stage 2 structural improvements, all critical-degree exclusions, compensation, and the literal original connected-component correction. Its [build and axiom audit](../verification/lean-extension/README.md) is separate from the historical upstream build and the finite checks. The pinned upstream source is unchanged.

## 1. Result and proof dependencies

> **Theorem 1.1 (now also Lean-verified).** For every finite simple graph `G` of maximum degree at most four and every candidate set `F subset E(G)`,
>
> `|F| <= 19 nu_s^G(F) + t_G(F)`.

Throughout the structural lemmas below, `G` is finite and simple with maximum degree at most four. All conflicts are evaluated in the complete original graph. In particular, an original edge outside `F` can witness a conflict.

The new structural step is:

> **Theorem 1.2 (nineteen-clique rigidity at full degree nineteen).** In a finite simple graph `G` of maximum degree at most four, let `Q` be a strong clique of nineteen original edges. If every `x in Q` has full conflict degree `c(x) >= 19`, then `Q` is a nineteen-edge subset of the twenty edges of an original connected component isomorphic to `C5[2]`.

The full-degree hypothesis is part of the theorem and is not being omitted. A nineteen-clique alone only gives full conflict degrees at least eighteen.

Here is the dependency chain for Theorem 1.1:

1. The [pinned upstream manuscript](../../upstream/packing195/manuscript/packing195.md) supplies the original-graph cover formulas, root counting tools, the selected-subcubic bound seventeen, the five high-degree clique bounds, private-set exchange, and twenty-clique rigidity.
2. [Stage 1](route-b-stage1.md) gives the exact compensation identity and the tertiary normalization of zero-deficit centres.
3. [Stage 2](route-b-stage2.md), Sections 3-6, proves on paper that every tertiary-optimal zero-deficit centre has `d(e)=c(e)=19`, private size nineteen, and its full closed conflict neighbourhood contained in `F`.
4. Sections 2-5 below prove Theorem 1.2. Section 6 excludes every such zero-deficit centre and proves the compensation inequality for arbitrary matching number.

The general theorem depends on new arguments from **both** Stages 2 and 3. They are certified by the independent extension, which imports the unchanged upstream Lean development.

## 2. Root notation and a stronger triangle obstruction

For a strong clique `Q`, write `q=|Q|` and `d_Q(v)` for selected degree. The upstream selected-subcubic bound gives a vertex `r` with `d_Q(r)=4` whenever `q >= 18`. Put `A=N_G(r)`. It has four vertices, and all four root edges belong to `Q`.

Call a vertex `x` external if `x notin A union {r}`. For every vertex `x != r`, define its **original** type

\[
T(x)=N_G(x)\cap A.
\]

Let `O` be the selected edges with both endpoints external, and let `o=|O|`. Every outer edge `xy` satisfies

\[
T(x)\cup T(y)=A,\qquad d_O(x)+|T(x)|\le4. \tag{2.1}
\]

The first assertion follows by requiring `xy` to conflict with all four selected root edges. Neither external endpoint is adjacent to `r`. Every selected edge either meets `A` or belongs to `O`; hence, even before independence of `A` is established,

\[
q\le\sum_{a\in A}d_G(a)-e_G(A)+o\le16-e_G(A)+o. \tag{2.2}
\]

### Lemma 2.1: independent neighbourhoods at every selected-degree-four root

If `q >= 18` and every member of `Q` has full conflict degree at least nineteen, then the original neighbourhood of every selected-degree-four root is independent.

**Proof.** Fix such a root and suppose `ab` is an original edge inside `A`. The selected triangle edges `ra` and `rb` each have a cover of size at most five. For an original edge `uv`, the upstream exact cover identity is

\[
c(uv)+e_G(C(uv))=\sum_{z\in C(uv)}d_G(z),
\quad C(uv)=(N_G(u)\setminus\{v\})\cup(N_G(v)\setminus\{u\}).
\]

Consequently

\[
e_G(C(ra))\le1,\qquad e_G(C(rb))\le1. \tag{2.3}
\]

If an external type contains `a`, each other label in that type supplies a distinct original edge inside `C(ra)`. Thus its size is at most two. The same holds for a type containing `b`. A type containing neither `a` nor `b` is contained in the other two labels, so every external type has size at most two.

Moreover, **at most one external double vertex has `a` in its type**: each such vertex supplies a different internal edge of `C(ra)`, and (2.3) permits at most one.

By (2.1), every outer edge joins two complementary double types. It must therefore meet that sole possible double vertex containing `a`. That vertex has at most two neighbours outside `A`. Hence `o <= 2`. Equation (2.2) now gives

\[
q\le16-1+2=17,
\]

contrary to `q >= 18`. The root was arbitrary, proving the lemma.

The internal edges used in (2.3) are original edges; they need not be selected. This is why missing candidate witnesses do not invalidate the argument.

## 3. The independent-root equations

Now assume the hypotheses of Theorem 1.2. Choose a selected-degree-four root, and apply Lemma 2.1 to obtain an independent four-element set `A`.

Let `K` be the selected edges from `A` to external vertices, with `k=|K|`. Then

\[
19=4+k+o,\qquad k\le12,\qquad o\ge3. \tag{3.1}
\]

All vertices of nonempty type are external. Original degree at most four gives the type-incidence bound

\[
\sum_{x\ne r}|T(x)|\le12. \tag{3.2}
\]

For each root label, the upstream original load inequality at threshold nineteen gives

\[
\sum_{x\ne r:\ a\in T(x)}(|T(x)|-1)\le5
\quad(a\in A). \tag{3.3}
\]

We use the following upstream root facts, with their precise hypotheses:

- With only types of size at most two, a clique with independent four-edge root has `q <= 17` (manuscript Lemma 3.6).
- With exactly one triple type and no quadruple, it has `q <= 18` (Lemma 3.7).
- Four fully selected double tips have two type classes of size two. Each tip has exactly the other class as its original neighbours outside `A` (Lemma 3.4).

Thus either a quadruple exists, or at least two triples exist. A quadruple already uses all four original neighbour slots and cannot meet an outer edge. An outer edge with a zero-type endpoint would need a quadruple partner to cover `A`, which is likewise impossible. Outer endpoints therefore have nonempty types. Outer edges avoiding triples and quadruples join complementary doubles.

There can be at most two triple vertices: any three three-element subsets of a four-element set have a common label, where those three vertices would contribute six to (3.3).

## 4. A quadruple forces an actual doubled-cycle component

Suppose there is a quadruple. Let `h` count quadruples, `a` triples, and `b` doubles. These counts concern all original types, whether their type edges are selected or not. Equation (3.2) gives

\[
4h+3a+2b\le12. \tag{4.1}
\]

Each triple is incident with at most one outer edge. Edges avoiding the triples join complementary doubles. Among at most three double vertices, this latter graph has at most two edges: it is simple, and each component is bipartite between a pair of complementary types. Among two double vertices it has at most one edge.

If `h >= 2`, at most four type incidences remain after two quadruples. There is either at most one triple and no double, or no triple and at most two doubles. In either case `o <= 1`, contradicting (3.1).

Thus `h=1`. If `a=2`, then `b<=1` and `o<=2`. If `a=1`, then `b<=2` and again `o<=2`. Both are impossible. Consequently `a=0`, and at least three outer edges require `b>=4`. Equation (4.1) forces `b=4`.

There is exactly one quadruple `z` and exactly four doubles. They use all twelve type incidences, so there are no other nonempty types and each root label has original degree four. Every outer edge joins two of the four doubles. Their outer degree is at most two, so `o<=4`. By (3.1), only two cases remain.

**Case `o=4`.** Four simple edges of maximum degree two on these four vertices form a four-cycle. Along each edge the two types are complementary, so the types alternate between two complementary pairs, with two vertices of each type. Every double has its two type neighbours and its two cycle neighbours as its full original neighbourhood. Together with the four root edges and the four edges at `z`, these edges form `C5[2]`.

**Case `o=3`.** Equation (3.1) gives `k=12`: every original type edge is selected, so all four doubles are fully selected. The upstream saturation lemma partitions them into two equal-type classes of size two and forces exactly the four cross-edges between the classes as their original edges outside `A`. Their two types must be disjoint: a shared label would be adjacent to `r`, `z`, and all four doubles, exceeding original degree four. Thus the types are complementary, and the same `C5[2]` structure follows. One of its four double-to-double edges is unselected; it remains an original edge.

For explicit component verification, write `U,V` for the complementary label pairs and `X,Y` for the corresponding two double classes. The five pairs in cyclic order are

\[
\{r,z\},\ U,\ X,\ Y,\ V.
\]

The consecutive pairs are completely joined. Each of these ten vertices has four specified original neighbours. The degree bound forbids all additional neighbours, inside or outside this set. The graph is connected, so it is a whole original connected component, not merely a candidate subgraph. Its twenty edges contain `Q`.

## 5. Two triples and no quadruple are impossible

Suppose there is no quadruple. The root facts in Section 3 and the load bound show that there are exactly two triple vertices, say `x,z`. There are at most three doubles by (3.2).

At most two outer edges meet triples. The remaining outer edges lie among at most three doubles and number at most two. Thus `o<=4`, and (3.1) again leaves two cases.

### Case `o=3`: saturation at all four root labels

Here `k=12`. All original type edges are selected, and every root label has selected degree four. Lemma 2.1 therefore applies with **each label as a new root**: its original neighbourhood is independent.

Any two nonempty original types are nested or disjoint. To see this, suppose `T(v),T(w)` intersect but neither contains the other. Choose labels

\[
a\in T(v)\setminus T(w),\qquad b\in T(w)\setminus T(v).
\]

The type edges `av,bw` are selected. Since `A` is independent and the two cross-type incidences are absent, their required conflict forces the original edge `vw`. At a common label of the two types, this is an edge inside its original neighbourhood, a contradiction.

The two triples must consequently have identical type `S`. Every other multiple type intersects `S`, so nesting and the absence of quadruples imply that it is contained in `S`. Let `b` be the missing label. Its three neighbours other than `r` are therefore three distinct singleton tips of type `{b}`, and all three type edges are selected.

Each of those singleton tips must be adjacent to the triple `x`: compare its selected edge at `b` to any selected type edge at `x` and apply the same witness rule. This gives `x` at least three neighbours outside `A`, although its triple type leaves room for only one. Contradiction.

### Case `o=4`: four outer edges cannot themselves be a strong clique

The two upper bounds on outer edges are both tight. Exactly two outer edges meet the triples, and exactly two avoid them. The latter two edges form a path on three double vertices, say

\[
v_1-v_2-v_3.
\]

The two triples and three doubles use all twelve type incidences. There are no other nonempty types. Each triple meets exactly one of the two remaining outer edges. Those edges cannot join the triples to each other, since that would use both triples but give only one edge. They must join triples to doubles.

The middle double `v_2` already has two type neighbours and two outer neighbours. Each endpoint double has only one remaining neighbour slot outside `A`. Thus the two triple edges attach to different endpoints. Interchanging `x,z` if necessary, the outer graph is exactly the path

\[
x-v_1-v_2-v_3-z.
\]

All five vertices are now saturated in the original graph: the triples have three type neighbours and one path neighbour, and each double has two type neighbours and two path neighbours. The selected first and last edges `xv_1` and `v_3z` are disjoint and have no original cross-edge between their endpoints. They do not conflict, contradicting the clique property of `Q`.

This excludes the last case without a quadruple. Section 4 now proves Theorem 1.2.

## 6. Compensation for arbitrary matching number

First remove the candidates of every fully selected original `C5[2]` component, keeping the original graph fixed. Stage 1 proves that this reduces the desired statement to `t_G(F)=0`. Work with this reduced set for now.

Choose a maximum independent set `M` in `H=L(G)^2[F]` minimizing the candidate-degree sum and then the full-degree sum. Use the Stage 1 definitions

\[
P_e=\{x\in F:N_H[x]\cap M=\{e\}\},\quad
\delta(e)=39-d_H(e)-1-|P_e|,
\]

\[
R=\sum_{x:\ |N_H[x]\cap M|\ge3}(|N_H[x]\cap M|-2).
\]

The upstream local bound gives integer `delta(e)>=0`. Suppose some `delta(e)=0`. Stage 2, Corollary 6.2, gives

\[
d_H(e)=c(e)=19,\qquad |P_e|=19,
\qquad N_{\widehat H}[e]\subseteq F. \tag{6.1}
\]

Every `x in P_e` has `d_H(x)>=d_H(e)=19` by private-set exchange, hence `c(x)>=19`. Apply Theorem 1.2 to the private clique `P_e`. It is contained in the twenty-edge set of a whole original `C5[2]` component `D`.

Since `e in P_e`, it lies in `D`. Every edge of `D` conflicts with `e` or equals `e`. Equation (6.1) therefore implies `E(D) subset F`. This contradicts `t_G(F)=0`.

There are consequently **no zero-deficit centres**, and integrality yields

\[
\delta(e)\ge1\quad(e\in M). \tag{6.2}
\]

The exact Stage 1 identity now proves the requested global compensation inequality:

\[
\boxed{\sum_{e\in M}\delta(e)+R\ge |M|.} \tag{6.3}
\]

Equivalently,

\[
2|F|=39|M|-\sum_e\delta(e)-R\le38|M|.
\]

This treats every matching number, including `k>=3`. No induction on `k`, abstract conflict-graph realization assumption, or finite-search extrapolation is used.

Restore the removed components. If there were `t` of them, then `|F|=|F_0|+20t` and `nu_s^G(F)=nu_s^G(F_0)+t`. Thus

\[
|F|\le19\nu_s^G(F_0)+20t
=19\nu_s^G(F)+t.
\]

This proves Theorem 1.1 on paper. The general global compensation problem resolves here because the original-graph rigidity excludes the zero-deficit class entirely. It does not require assigning transfers among surviving zero-deficit centres.

### Consequences and sharpness

- The `19,19,18` configuration left in Stage 2 is impossible: each of its two nineteen-edge private cliques would force a fully selected exceptional component. This excludes the remaining 58-edge, matching-number-three case and simultaneously handles larger matching numbers.
- A proper nineteen-edge selection in an original `C5[2]` component has matching number one, correction zero, and equality in the new bound. Its candidate centre degree is eighteen, private size nineteen, and deficit one, consistent with (6.2).
- Before exceptional-component removal, a fully selected `C5[2]` has deficit minus one. The unreduced compensation form remains `sum delta + R >= |M|-2t`, as in Stage 1; (6.2) is asserted only after reduction.

## 7. Finite checks and completed formalization

The [Stage 3 checker](../scripts/check_stage3.py) enumerates labelled root templates for the two saturated type families in this proof: one quadruple with four doubles, and two triples with three doubles. It retains every original core edge, including edges outside the candidates, and completes unused original degree slots with fresh branches. It checks nineteen-edge candidate cliques, full degrees, and the actual doubled-cycle component conclusion. It also checks the residual deficit in doubled-cycle boundary examples. See the [saved results](../results/stage3-checks.json) for exact scope, counts, source hashes, and outcomes.

These checks support specific proof steps. They are not an exhaustive search over all original graphs or a formal proof of either theorem. The independent Lean extension now supplies the universal formal proofs, without using the finite checkers as proof certificates.

The completed formalization covers:

1. Independent root neighbourhoods, original type loads, and the triple-type exclusions.
2. A closed original support on at most ten vertices and completion of a high19 nineteen-clique to a twenty-clique. Upstream rigidity supplies its component certificate; the potentially unselected twentieth edge is preserved.
3. The stronger Stage 2 root bounds, the unconditional high20 seventeen-clique bound, and the closed private-centre lemma.
4. Exclusion of all zero-deficit centres under tertiary optimization after fully selected twenty-cliques are removed.
5. Exact compensation, the corrected matching-witness theorem, and the independence-number statement with the literal original connected-component count.

See the [formalization record](lean-formalization-progress.md) for proof adaptations and exact scope. The older Stage 2 `k=2` and `k=3` exchange exclusions are not dependencies of the final formal theorem. The explicit sharpness construction has not been separately formalized.
