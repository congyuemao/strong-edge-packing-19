# Route B, Stage 2: excluding the 39-edge obstruction

Date: 11 October 2026 (Australia/Sydney).

**Status: paper proof, not Lean-formalized.** The arguments below use the pinned upstream structural lemmas and the Stage 1 normalization. The accompanying finite checks validate specific obstruction templates and boundary examples; they are not an exhaustive search over original graphs and do not certify this proof in Lean.

## 1. Results and their limits

The five Stage 1 rows for `|F|=39`, `alpha(H)=2`, and `t_G(F)=0` can all be excluded on paper. Consequently:

> **Theorem.** If `G` is a finite simple graph of maximum degree at most four and `nu_s^G(F) <= 2`, then
>
> `|F| <= 19 nu_s^G(F) + t_G(F)`.

The proof first establishes additional local facts. In the notation of Stage 1, every zero-deficit centre in a tertiary-optimal maximum independent set must have

\[
d(e)=c(e)=19,\qquad |P_e|=19. \tag{1.1}
\]

This partial structural conclusion holds for arbitrary matching number. It does not prove the general compensation inequality.

For `k=3`, the first possible uncorrected counterexample has 58 candidates. Section 8 excludes its `R=1` case and reduces its `R=0` case to a specific configuration with private-clique sizes `19,19,18` and exactly two shared candidates. That last configuration is not excluded here.

## 2. Root notation and existing tools

Let `Q` be a strong clique in the complete original graph. Write `q=|Q|` and `d_Q(v)` for its selected degree. Choose a vertex `r` with `d_Q(r)=4`. Original maximum degree four gives `A=N_G(r)`, with `|A|=4`, and all four root edges belong to `Q`.

When `A` is independent, let:

- `K` be selected edges from `A` to vertices outside `A union {r}`, with `k=|K|`;
- `O` be selected edges having both endpoints outside `A union {r}`, with `o=|O|`;
- `T(x)=N_G(x) intersect A` be an original type;
- `B` be the tips of the edges in `K`;
- `D` be the double tips with both type edges selected.

Then

\[
q=4+k+o,\qquad q=\sum_{a\in A}d_Q(a)+o. \tag{2.1}
\]

An outer edge has endpoint types whose union is `A`. Every type incidence is an original edge, selected or not. Thus

\[
\sum_{x\ne r}|T(x)|\le12,\qquad d_O(x)+|T(x)|\le4. \tag{2.2}
\]

For `c(f)>=t` on `Q`, each root-label load satisfies

\[
\sum_{x\ne r,\ a\in T(x)}(|T(x)|-1)\le24-t. \tag{2.3}
\]

We use the following results from the [pinned English manuscript](../../upstream/packing195/manuscript/packing195.md), all with original-graph conflicts:

- Lemmas 2.1-2.2: the exact endpoint cover and its full-degree bound; an edge of full conflict degree at least 21 has original endpoint degrees four and belongs to no original triangle.
- Proposition 4.2: a strong clique of selected maximum degree at most three has at most seventeen edges.
- Lemma 3.3: a selected singleton tip implies `|B|<=6`.
- Lemma 3.4: `|D|<=4`; when `|D|=4` and every type has size at most two, `B=D`, so `k=8`.
- Lemmas 3.5-3.6: with only types of size at most two, `o<=4` and `q<=17`.
- Lemma 3.7: with a unique triple type and no quadruple, `k<=10` and `o<=4`.
- Proposition 5.4: at threshold 21, a four-selected-edge root with a type of size at least three has `q<=16`.
- Theorem 5.1: the existing high20 bound `q<=18`.

The witness rule is used repeatedly: for selected `ax,by` with independent `A`, if `a` is not in `T(y)` and `b` is not in `T(x)`, their required conflict forces the original edge `xy`.

## 3. Two elementary root obstructions

### Lemma 3.1: a complementary-double four-cycle contains a low-conflict outer edge

Suppose four double vertices support four distinct outer edges. Each has outer degree at most two. They therefore form a four-cycle, and their types alternate between complementary pairs of `A`.

Every vertex of this cycle has its two type neighbours and two cycle neighbours as its complete original neighbourhood. For a cycle edge `uv`, the endpoint cover is the four root labels together with the other two cycle vertices `w,z`. Inside that cover are the two type edges at `w`, the two type edges at `z`, and the opposite cycle edge `wz`. Thus there are at least five internal original edges, and

\[
c(uv)\le24-5=19. \tag{3.1}
\]

In fact this applies to each cycle edge. Arbitrary additional original edges cannot remove these five witnesses or change the already saturated endpoint neighbourhoods.

### Lemma 3.2: at threshold 21, small types give `k<=8`

Assume `A` is independent, every type has size at most two, and every selected edge has full conflict degree at least 21. Then

\[
k\le8. \tag{3.2}
\]

**Proof.** If a selected singleton occurs, the singleton lemma gives `|B|<=6`. Otherwise every selected tip is a double and the type-incidence bound gives the same conclusion. Since a double contributes a second selected type edge exactly when it belongs to `D`,

\[
k=|B|+|D|.
\]

The cases `|D|<=2` and `|D|=4` follow immediately from the listed upstream tools. Consider `|D|=3`.

Distinct types among fully selected doubles must be disjoint. Otherwise the witness rule makes the two tips adjacent, and their common label gives an original triangle containing selected edges, impossible at threshold 21. On four labels, the three fully selected doubles consequently have either one common type or two complementary types with class sizes two and one.

If all three have one type `S`, each label of `S` is already adjacent to the root and those three tips. Every additional selected tip therefore has its type in the complementary pair. The witness rule makes it adjacent to all three fully selected doubles. Each of those doubles has at most two original neighbours outside `A`, so there can be at most two additional tips. Thus `|B|<=5` and `k<=8`.

In the two-plus-one case, let `x,y` have type `S`, and let `z` have the complementary type. The neighbours of `z` outside `A` are exactly `x,y`. An additional selected tip `w` cannot have a selected label in `S`: its type has at most two labels, so one label of the complementary pair is missing, and the witness rule would force `zw`. All its selected labels are therefore in the complementary pair. The same rule then forces both `xw` and `yw`. Each of `x,y` has only one remaining neighbour slot outside `A`, after its edge to `z`. Hence there is at most one additional tip, giving `|B|<=4` and `k<=7`. This completes the proof.

## 4. Improved root bounds at thresholds 21, 22, and 23

### Proposition 4.1: high21 with a four-selected-edge root gives `q<=16`

All selected edges are triangle-free in the original graph, so `A` is independent. If any type has size at least three, upstream Proposition 5.4 already gives `q<=16`. Otherwise Lemma 3.2 gives `k<=8`, and the existing complementary-double bound gives `o<=4`. Equation (2.1) proves `q<=16`.

This proposition does not assert that every high21 clique has at most sixteen edges; the selected-subcubic case is not covered by the root hypothesis.

### Proposition 4.2: high22 with a four-selected-edge root gives `q<=15`

The root neighbourhood is independent and each load in (2.3) is at most two. A quadruple type is impossible. If a triple exists, it is the only multiple type: every other multiple type would intersect it and exceed a load of two. Every outer edge must consequently meet that triple, whose remaining original degree is at most one. Thus `o<=1`; the existing unique-triple bound `k<=10` gives `q<=15`.

Otherwise all types have size at most two. Summing the four load bounds shows that there are at most four double vertices. Four outer edges would force exactly the complementary-double four-cycle of Lemma 3.1, contrary to high22. Therefore `o<=3`. Lemma 3.2 gives `k<=8`, so `q<=15` again.

### Proposition 4.3: high23 with a four-selected-edge root gives `q<=13`

The loads are at most one. All multiple types are doubles, and distinct double vertices cannot share a label. There are at most two of them. Every outer edge joins complementary doubles, so simplicity gives `o<=1`. Lemma 3.2 applies and gives `k<=8`, whence `q<=13`.

## 5. The high20 eighteen-edge boundary is impossible

### Lemma 5.1: a large high20 clique has an independent neighbourhood at every four-selected-edge root

Assume `q>=17` and all selected edges have full conflict degree at least 20. Suppose `a,b` are adjacent labels at a four-selected-edge root `r`. The selected triangle edges `ra,rb` have covers of size at most five. Their conflict degree being at least twenty forces those covers to have no internal original edge.

An external type containing `a` must then be the singleton `{a}`: any additional label would give an internal edge in the cover of `ra`. The same holds for `b`. An outer edge would need its endpoint types to cover all four root labels. Covering both `a` and `b` would already require two singleton endpoints, which cannot cover the other labels. Hence there is no outer edge, and all selected edges meet `A`. This gives `q<=16`, a contradiction. Therefore `A` is independent.

### Lemma 5.2: a unique triple in a high20 clique permits at most three outer edges

Let `x` be the unique triple, with all other types of size at most two. The existing bound is `o<=4`, so suppose `o=4`. There are at most four double vertices because the triple uses three of the twelve available type incidences.

If no outer edge meets `x`, four outer edges on those doubles force the four-cycle of Lemma 3.1, impossible at threshold 20.

Otherwise exactly one outer edge is `xy`, and three avoid `x`. Their double endpoints form a simple graph of maximum degree at most two on at most four vertices. An outer triangle is impossible, since types across each outer edge are complementary pairs. Thus these three edges form a four-vertex path `v1-v2-v3-v4`, with alternating complementary types.

The internal path vertices already have their two type neighbours and two outer neighbours, so they are saturated in the original graph. The triple `x` has its three type neighbours and `y`, and is also saturated. If `y` were outside the path, the selected edge `xy` would be disjoint from and have no cross-adjacency to the selected middle edge `v2v3`. This contradicts the clique condition.

Thus `y` is an endpoint of the path; reverse the path if necessary so that `y=v1`. The cover of the selected edge `v1v2` is exactly `A union {x,v3}`. It contains the three original type edges of `x` and the two original type edges of `v3`. Hence `c(v1v2)<=19`, again impossible. Therefore `o<=3`.

### Proposition 5.3: every all-high20 strong clique has at most seventeen edges

The existing theorem gives `q<=18`. Suppose `q=18`. The existing selected-subcubic bound forces a four-selected-edge root. Its neighbourhood is independent by Lemma 5.1. Each label load is at most four.

**A quadruple exists.** It uses three load units at every label and has no outer neighbour. Every other multiple vertex must be a double; two such vertices cannot share a label. Consequently there are at most two other multiple vertices and at most one outer edge. The bound `q<=sum_A d_Q+o<=17` is a contradiction.

**At least two triples exist and no quadruple exists.** Choose triples `x,y` and two common labels `a,b`. Their contributions exhaust the loads at those labels. An outer edge avoiding `x,y` would have to cover `a,b` using two singleton endpoints, which is impossible. Thus every outer edge meets `x` or `y`, and `o<=2`.

Equality `q=18` now forces `o=2` and `d_Q(a)=4` at every root label. All original edges at those labels are selected. Lemma 5.1, applied at each label as a new four-selected-edge root, shows that every one of their original neighbourhoods is independent.

Original tip types must therefore be nested or disjoint. Indeed, intersecting nonnested types give selected edges at labels in their two differences; the witness rule forces adjacency of the tips, contradicting independence at a common label. The two triple types are consequently equal, say to `S`. Every other multiple type is contained in `S`, since it intersects `S`, nesting holds, and no quadruple exists.

Let `b` be the missing label. Its three original neighbours other than `r` are selected singleton tips of type `{b}`. Each must be adjacent to the triple `x` by the witness rule. That requires three neighbours of `x` outside `A`, but only one is available. This contradiction excludes the case.

**There is a unique triple and no quadruple.** The existing bound gives `k<=10`, and Lemma 5.2 gives `o<=3`. Hence `q<=17`.

**All types have size at most two.** Existing Lemma 3.6 gives `q<=17` directly.

All possibilities contradict `q=18`, proving the proposition.

## 6. Private cliques force a four-selected-edge root

### Lemma 6.1: a closed high-degree private centre cannot have a large selected-subcubic private clique

Let `M` be a maximum independent set and `e=uv` one of its centres. Suppose

\[
c(e)\ge21,\quad N_{\widehat H}[e]\subseteq F,
\quad \max_x d_{P_e}(x)\le3.
\]

Then `|P_e|<=13`.

**Proof.** The full degree assumption forces `u,v` to have original degree four and the selected edge `uv` to be triangle-free. Since their private selected degrees are at most three, there are original edges `uz` and `vw` outside `P_e`. Both are candidates because they conflict with the centre and its full closed neighbourhood lies in `F`.

Each of these candidates is covered by some other centre. For `uz`, the endpoint `u` cannot meet or be adjacent to an endpoint of another centre, since that would make `e` conflict with that centre. The conflict must therefore be witnessed at `z`. Every candidate edge through `z` would also conflict with that other centre, so no edge of `P_e` can use `z`. Thus `d_{P_e}(z)=0`, and similarly `d_{P_e}(w)=0`.

The vertices `z,w` are distinct, since a common neighbour would form a triangle on `uv`. They both lie in its six-vertex cover. The other four cover vertices have private selected degree at most three. The exact selected cover identity yields

\[
|P_e|-1\le\sum_{a\in C(e)}d_{P_e}(a)\le12.
\]

This proves the claim. All original witness edges are retained throughout.

### Corollary 6.2: every zero-deficit centre has degree nineteen

Work with `t_G(F)=0` and the tertiary-optimal maximum independent set of Stage 1. Its zero-deficit centres have candidate and full degree equal, and their complete conflict neighbourhoods belong to `F`.

The five possible degrees are reduced as follows:

| Centre degree | Required private size | Contradiction |
| --- | --- | --- |
| 20 | 18 | Proposition 5.3 gives at most 17 |
| 21 | 17 | Lemma 6.1 forces a four-selected-edge root; Proposition 4.1 gives at most 16 |
| 22 | 16 | Lemma 6.1 forces a four-selected-edge root; Proposition 4.2 gives at most 15 |
| 23 | 15 | Lemma 6.1 forces a four-selected-edge root; Proposition 4.3 gives at most 13 |

Thus only degree nineteen remains, with private size nineteen. Its closed candidate neighbourhood has twenty vertices, exactly nineteen of which are private. It has a unique nonprivate neighbour, denoted by `b_e`, with `m(b_e)>=2`.

This is a paper corollary for arbitrary matching number, not a general 19-packing theorem.

## 7. The remaining degree-nineteen obstruction

### Lemma 7.1: a twice-covered vertex cannot serve two zero-deficit centres

In a tertiary-optimal set, suppose a candidate `b` has `m(b)=2` and covers two zero-deficit centres `e,f`. Their private sets `P,Q` are disjoint nineteen-cliques. Let

\[
A=P\setminus N_H(b),\qquad B=Q\setminus N_H(b).
\]

Both sets are nonempty: otherwise `b` together with one private clique would form a twenty-clique, forbidden by `t=0`.

Every cross-pair in `A x B` must be adjacent. Otherwise its two vertices and `b` would replace `e,f`, preserve nonadjacency to every other member of `M`, and increase the matching size. A vertex of `A` already has eighteen neighbours in `P`, so the maximum conflict degree 24 forces `|B|<=6`. Symmetrically `|A|<=6`.

Consequently `b` is adjacent to at least

\[
(19-6)+(19-6)=26
\]

vertices in the two private cliques, contradicting degree at most 24.

### Theorem 7.2: no uncorrected 39-edge, matching-number-two instance exists

Suppose `|F|=39`, `alpha(H)=2`, and `t=0`. Stage 1 gives two zero-deficit centres. Corollary 6.2 makes both their degrees nineteen. Their two private sets have nineteen members each, and the sole remaining candidate is covered by both centres. Its multiplicity is two, contradicting Lemma 7.1.

For arbitrary `F` with `alpha(H)=2` and `t=0`, the verified 19.5 bound gives `|F|<=39`; the excluded equality improves this to `|F|<=38`. Independence number one gives a clique of size at most nineteen, and independence number zero forces `F` to be empty. Removing and restoring fully selected exceptional components, as in Stage 1, proves the theorem in Section 1 for `nu_s^G(F)<=2`.

The constant is sharp already for two disjoint original `C5[2]` components with nineteen candidates chosen from each: there are 38 candidates, matching number two, and correction zero. Keeping all twenty candidates in one component and nineteen in the other gives 39 candidates and correction one; it is not a counterexample to the corrected bound.

## 8. Continuing beyond two matching members

The general target is still

\[
R+\sum_{\delta(e)>0}(\delta(e)-1)\ge |Z|.
\]

Corollary 6.2 associates every member of `Z` with its unique nonprivate neighbour. Lemma 7.1 shows that a vertex of multiplicity two receives at most one such association. Higher multiplicities and the excess deficits still require control.

### 8.1. The 58-edge, three-centre case with `R=1` is impossible

For `|F|=58`, `k=3`, and `t=0`, the exact identity gives `sum delta + R=1`. If `R=1`, all three deficits vanish. Each centre has one nonprivate neighbour, and the vertex of multiplicity three must be that same neighbour `b` for all three. Hence `F` consists of three private nineteen-cliques `P_1,P_2,P_3` and `b`.

Put `A_i=P_i\setminus N_H(b)` and `a_i=|A_i|`. Each `a_i` is between one and eighteen, and

\[
a_1+a_2+a_3\ge57-24=33.
\]

Every private vertex has at most six neighbours outside its own private clique. Relabel so that `a_1=a` is smallest. Each of `a_2,a_3` is at least seven: this is immediate if `a>=7`; if `a<=6`, the upper bound eighteen on the other part gives `a_2,a_3>=15-a>=9`.

Also `a_2+a_3>=max(33-a,2a)>=22`. Choose any `x` in `A_1`. After deleting its neighbours from `A_2,A_3`, both remaining sets are nonempty and their combined size is at least sixteen. They cannot be complete to each other, since each vertex has at most six neighbours outside its own clique; completeness would force both sizes at most six. Choose a nonadjacent pair `y,z` across these remaining sets. Then `b,x,y,z` are independent, a contradiction.

### 8.2. The remaining 58-edge case has private sizes `19,19,18`

The only remaining possibility is `R=0` and total deficit one: two centres `e_1,e_2` have zero deficit and a third centre `f` has deficit one. Each zero-deficit centre has a unique shared neighbour. By Lemma 7.1, these are distinct, say `b_1,b_2`, and their covering pairs are respectively `{e_1,f}` and `{e_2,f}`. There are no other nonprivate candidates, since every covering pair among three centres contains at least one of `e_1,e_2`.

Counting gives

\[
|P_{e_1}|=|P_{e_2}|=19,\quad |P_f|=18,
\quad d(f)+1=18+2=20.
\]

Thus all three candidate centre degrees equal nineteen. Proposition 5.3 also gives a member `x` of `P_f` with full degree at most nineteen; private degree monotonicity gives `d(x)=c(x)=19`. The same tertiary exchange as in Stage 1 shows that `c(f)=19` too. Therefore all three complete conflict neighbourhoods are contained in `F`.

**Still open in this repository:** realize or exclude this `19,19,18` private-clique configuration in a genuine maximum-degree-four original graph, preserving all outside-candidate witness edges. This is a concrete next obstruction; the proof for two matching members does not eliminate it.

## 9. Computation and formalization boundaries

The [companion script](../scripts/check_stage2.py) checks the complementary-double cycle and triple-path obstruction templates by constructing actual degree-at-most-four graphs and computing full conflicts. It also computes exact induced-matching numbers and component corrections for the 38-, 39-, and 40-candidate doubled-cycle boundary examples and the unselected-witness path. The [saved output](../results/stage2-checks.json) records 72 labelled template checks and four exact examples, all passing.

Those computations do not enumerate all 39-edge graphs. The exclusion theorem rests on the paper lemmas above and the existing upstream theorems. No new Lean theorem, proof placeholder, or axiom was introduced. The upstream submodule remains unchanged.
