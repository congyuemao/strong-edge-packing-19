# A Corrected Nineteen Bound for Induced Matchings in Prescribed Edge Sets

*A complete proof manuscript with a correspondence to the verified Lean development*

**Author:** Congyue Mao

**Proof version:** aligned with the optimized `StrongEdge19` development at commit `2c20ac6099a0fb581367e3bee39465aafec5f879`.

**Date:** 11 October 2026.

## Abstract

Let $G$ be a finite simple graph of maximum degree at most four, and let $F\subseteq E(G)$. Write $\nu_s^G(F)$ for the maximum size of an induced matching of the original graph contained in $F$, and let $t_G(F)$ count the original connected components isomorphic to $C_5[2]$ whose entire edge sets belong to $F$. We prove

$$
|F|\leq 19\nu_s^G(F)+t_G(F).
$$

The constant nineteen is sharp. The proof refines the private-neighbourhood argument for the verified corrected 19.5 bound. A tertiary-optimal maximum independent set in the candidate conflict graph has positive integer deficit at every centre once wholly selected twenty-cliques have been excluded. The critical-degree analysis exports only candidate degree nineteen. A separate rigidity theorem extends a nineteen-edge strong clique of full conflict degree at least nineteen to an original twenty-clique; this recovers the neighbourhood closure needed for the final contradiction. An exact incidence identity gives the packing bound, and induction restores the exceptional components.

This manuscript presents the complete nineteen-bound argument in the order used by the optimized formalization. The established structural results from the pinned 19.5 project are stated explicitly in Section 2, with their proofs available in the cited foundation. All subsequent structural improvements and their use in the packing argument are proved here. The historical small-matching-number investigations are not prerequisites. Appendix A identifies the corresponding Lean declarations.

**Keywords.** Induced matching; prescribed edge set; square of a line graph; doubled five-cycle; private neighbourhood; formal verification.

**Contents:** [Statement](#1-statement-and-conventions) · [Foundation](#2-the-verified-foundation-and-elementary-cover-identities) · [Compensation and normalization](#3-exact-compensation-and-critical-normalization) · [Root tools](#4-root-counting-tools) · [Stage 2](#5-stage-2-the-candidate-degree-interface) · [Stage 3](#6-stage-3-nineteen-clique-rigidity-through-a-closed-support) · [Positive deficits](#7-eliminating-zero-deficit-and-proving-compensation) · [Correction and sharpness](#8-restoring-exceptional-components-and-sharpness) · [Lean concordance](#appendix-a-correspondence-with-the-lean-development) · [Verification scope](#appendix-b-verification-status-and-scope).

## 1. Statement and conventions

Throughout, $G$ is a finite simple graph with $\Delta(G)\leq4$. Two distinct original edges **conflict** if they share an endpoint or some original edge joins an endpoint of one to an endpoint of the other. Let

$$
\widehat H=L(G)^2,\qquad H=\widehat H[F].
$$

Thus the vertices of $\widehat H$ are all original edges. Selecting $F$ restricts the vertex set of the conflict graph; it does not remove original edges that witness conflicts. Write

$$
c(e)=d_{\widehat H}(e),\qquad d(e)=d_H(e)\quad(e\in F).
$$

An induced matching in $G$ contained in $F$ is precisely an independent set of $H$. Hence $\nu_s^G(F)=\alpha(H)$.

The graph $C_5[2]$ has five disjoint pairs of vertices, with all four possible edges between each two consecutive pairs around a five-cycle and no other edges. It has ten vertices and twenty edges. Define

$$
t_G(F)=\bigl|\{D:\ D\text{ is a connected component of }G,
\ D\cong C_5[2],\ E(D)\subseteq F\}\bigr|.
$$

The count concerns actual original connected components, not labelled representations of them and not components of the candidate subgraph.

**Theorem 1.1.** Every $F\subseteq E(G)$ contains an induced matching $M$ of $G$ such that

$$
|F|\leq19|M|+t_G(F).
\tag{1.1}
$$

Consequently $|F|\leq19\nu_s^G(F)+t_G(F)$.

We first establish the bound when no twenty-edge strong clique is wholly selected. The final step restores such cliques while keeping $G$ fixed.

## 2. The verified foundation and elementary cover identities

A **strong clique** is a set $Q\subseteq E(G)$ of pairwise conflicting edges. Put $q=|Q|$, and let $d_Q(v)$ count its edges incident with the original vertex $v$. Original degree $d_G(v)$, selected degree $d_Q(v)$, full conflict degree $c(e)$, and candidate conflict degree $d(e)$ will always be distinguished.

We use the following results of the [pinned 19.5 development](../../upstream/packing195/manuscript/packing195.md) [1], at commit `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`.

**Foundation 2.1 (full-degree thresholds).** If every edge of a strong clique $Q$ has full conflict degree at least $h$, then

| $h$ | 20 | 21 | 22 | 23 | 24 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Upper bound on $q$ | 18 | 17 | 16 | 15 | 13 |

These are bounds on original-edge cliques using full original conflict degrees. In particular, the threshold-24 bound used below is thirteen, not the weaker bound fourteen sufficient for the abstract local-39 criterion.

**Foundation 2.2 (selected subcubic bound).** If $d_Q(v)\leq3$ for every original vertex, then $q\leq17$. Thus every strong clique with at least eighteen edges has a vertex incident with four of its selected edges.

**Foundation 2.3 (twenty-clique rigidity).** Every strong clique has at most twenty edges. A twenty-edge strong clique is the complete edge set of a whole original component isomorphic to $C_5[2]$. Such a clique is closed under full conflict adjacency: an original edge conflicting with one of its members belongs to the same clique. Distinct twenty-cliques are disjoint.

These three results are established upstream; this proof neither assumes the nineteen bound nor reproves the 19.5 project. Their exact Lean interfaces are listed in Appendix A. The elementary root tools used later are also available upstream; we give their counting arguments to make the new structural steps readable without reconstructing those tools from code.

For an original edge $uv$, set

$$
C(uv)=(N_G(u)\setminus\{v\})\cup(N_G(v)\setminus\{u\}).
$$

Neither endpoint belongs to $C(uv)$, and $|C(uv)|\leq6$. An original edge other than $uv$ conflicts with $uv$ exactly when it meets this cover. Indeed, a shared endpoint leaves the other endpoint in the cover; otherwise a connecting original edge supplies an endpoint in the cover. The converse follows from the same adjacency condition.

For a vertex set $S$, let $e_G(S)$ and $e_Q(S)$ count original and selected edges with both endpoints in $S$. Counting incidences gives

$$
c(uv)+e_G(C(uv))=\sum_{a\in C(uv)}d_G(a)\leq24,
\tag{2.1}
$$

and, when $uv\in Q$,

$$
q-1+e_Q(C(uv))=\sum_{a\in C(uv)}d_Q(a).
\tag{2.2}
$$

In particular $c(e)\leq24$. If an endpoint of $uv$ has degree at most three, or if $uv$ lies in a triangle, its cover has at most five vertices and $c(uv)\leq20$. Therefore

$$
c(uv)\geq21\ \Longrightarrow\ d_G(u)=d_G(v)=4,
\quad |C(uv)|=6,\quad uv\text{ lies in no triangle}.
\tag{2.3}
$$

The paper uses the exact identities (2.1)–(2.2). The main Lean development often uses their immediate one-sided cover bounds together with its finite incidence identity; no stronger premise is required by this presentation.

## 3. Exact compensation and critical normalization

### 3.1. Optimization and private sets

Choose a maximum independent set $M$ of $H$. Among these, minimize $\sum_{e\in M}d(e)$; call such a set **optimal**. When needed, minimize $\sum_{e\in M}c(e)$ among optimal sets; call the resulting choice **tertiary-optimal**. All three objectives have minimizers by finiteness. The second objective uses candidate degrees; the third uses full degrees.

For $e\in M$ and $x\in F$, define

$$
P_e=\{x\in F:N_H[x]\cap M=\{e\}\},\qquad
m(x)=|N_H[x]\cap M|.
$$

**Lemma 3.1 (private exchange).** The following hold.

1. $m(x)\geq1$ for all $x\in F$.
2. $e\in P_e\subseteq N_H[e]$.
3. $P_e$ is a clique.
4. For an optimal $M$, every $x\in P_e$ satisfies $d(x)\geq d(e)$.

**Proof.** An uncovered vertex could be added to $M$. Independence gives the second assertion. Two nonadjacent members of $P_e$ could replace $e$, increasing cardinality. Finally, replacing $e$ by a private vertex preserves independence and cardinality, so minimality of the candidate-degree sum gives the last assertion. The exchange with $x=e$ is harmless. ∎

### 3.2. The exact identity

Define integer deficits and nonnegative excess coverage by

$$
L(e)=d(e)+1+|P_e|,\qquad \delta(e)=39-L(e),
\qquad R=\sum_{x\in F}\max\{m(x)-2,0\}.
$$

**Lemma 3.2 (exact compensation).** For a maximum independent set,

$$
2|F|=39|M|-\sum_{e\in M}\delta(e)-R.
\tag{3.1}
$$

**Proof.** Counting pairs $(x,e)$ with $e\in M$ and $x\in N_H[e]$ gives
$\sum_e(d(e)+1)=\sum_xm(x)$. A vertex belongs to exactly one private set when $m(x)=1$, and to none otherwise, so $\sum_e|P_e|=\sum_x\mathbf1_{m(x)=1}$. For every integer $m\geq1$,

$$
m+\mathbf1_{m=1}=2+\max\{m-2,0\}.
$$

Summing gives $\sum_eL(e)=2|F|+R$, which is (3.1). ∎

This argument only needs maximality, although the checked interface assumes maximum cardinality. It requires neither the degree bound nor exceptional-component removal. In particular,

$$
|F|\leq19|M|\quad\Longleftrightarrow\quad
\sum_e\delta(e)+R\geq|M|.
\tag{3.2}
$$

Deficits are integers, not truncated natural differences. In a wholly selected $C_5[2]$, the conflict graph is $K_{20}$, giving $d(e)=19$, $|P_e|=20$, and $\delta(e)=-1$. Thus nonnegativity will only be asserted under the appropriate exclusion hypothesis.

### 3.3. The five possible zero-deficit rows

**Lemma 3.3.** If $M$ is optimal and $\delta(e)=0$, then

$$
19\leq d(e)\leq23,\qquad |P_e|=38-d(e).
\tag{3.3}
$$

**Proof.** Since $|P_e|\leq d(e)+1$, the equality $d(e)+1+|P_e|=39$ gives $d(e)\geq19$. Also $d(e)\leq c(e)\leq24$. If $d(e)=24$, private exchange gives $c(x)\geq d(x)\geq24$ for every $x\in P_e$. Foundation 2.1 bounds its size by thirteen, whereas the equality requires fourteen. ∎

No exclusion of twenty-cliques is needed for this lemma.

**Lemma 3.4 (full-degree witness).** Under the hypotheses of Lemma 3.3, some $x\in P_e$ satisfies $c(x)=d(x)=d(e)$.

**Proof.** Every private member has $c(x)\geq d(x)\geq d(e)$. If all full degrees were at least $d(e)+1$, Foundation 2.1 would give the following contradictions:

| $d(e)$ | Required $|P_e|$ | Bound at full threshold $d(e)+1$ |
| --- | ---: | ---: |
| 19 | 19 | 18 |
| 20 | 18 | 17 |
| 21 | 17 | 16 |
| 22 | 16 | 15 |
| 23 | 15 | 13 |

Hence some full degree is at most $d(e)$, forcing both equalities. ∎

**Lemma 3.5 (internal tertiary normalization).** If $M$ is tertiary-optimal and $\delta(e)=0$, then

$$
c(e)=d(e),\qquad N_{\widehat H}[e]\subseteq F.
\tag{3.4}
$$

**Proof.** Exchange $e$ for the witness from Lemma 3.4. Candidate-degree equality preserves the second objective, so the exchanged set remains optimal. Tertiary minimality gives $c(e)\leq c(x)=d(e)$, and the reverse inequality always holds. The candidate neighbourhood is the intersection of the full neighbourhood with $F$; equality of their finite cardinalities gives full-neighbourhood containment. The centre itself is already a candidate. ∎

This stronger normalization is retained internally for degrees twenty-one through twenty-three. It is not an input to the degree-nineteen rigidity argument in Section 7.

## 4. Root counting tools

### 4.1. Original types and load

Let $r$ be incident with four edges of a strong clique $Q$. Then $d_G(r)=4$, and all root edges to $A=N_G(r)$ are selected. For each $x\neq r$, define its **original type** $T(x)=N_G(x)\cap A$. Call type sizes one, two, three, and four singleton, double, triple, and quadruple. Put

$$
\mathcal P=\{x\neq r:|T(x)|\geq2\}.
$$

When $A$ is independent, all vertices with nonempty type are outside $A\cup\{r\}$. Let $K$ consist of selected edges from $A$ to these external vertices, and let $O$ consist of selected edges with both endpoints external. Write $k=|K|$, $o=|O|$. Then

$$
q=4+k+o,\qquad k\leq12,\qquad q\leq16+o.
\tag{4.1}
$$

Even without independence, counting original edges meeting $A$ gives

$$
q\leq\sum_{a\in A}d_G(a)-e_G(A)+o\leq16-e_G(A)+o.
\tag{4.2}
$$

An outer edge $xy$ must conflict with every root edge, so

$$
T(x)\cup T(y)=A,\qquad d_O(x)+|T(x)|\leq4.
\tag{4.3}
$$

Counting neighbours of the four labels other than $r$ gives

$$
\sum_{x\neq r}|T(x)|\leq12,\qquad |\mathcal P|\leq6.
\tag{4.4}
$$

When $A$ is independent, define

$$
\lambda(a)=\sum_{x\neq r:\ a\in T(x)}(|T(x)|-1).
$$

For each summand, the original edges from $x$ to $T(x)\setminus\{a\}$ lie inside $C(ra)$. They are distinct: independence of $A$ separates the label endpoints from the external endpoints. Equation (2.1) therefore gives

$$
\lambda(a)+c(ra)\leq24.
\tag{4.5}
$$

In particular, if every selected edge has full degree at least $h$, then $\lambda(a)\leq24-h$. All type sums and loads count original incidences, including unselected edges.

### 4.2. Independent neighbourhoods at threshold nineteen

**Lemma 4.1.** If $q\geq18$ and every member of $Q$ has full degree at least nineteen, then the original neighbourhood of every four-edge selected root is independent.

**Proof.** Suppose $ab\in E(G[A])$. Each of $ra,rb$ is a selected triangle edge, so (2.1) bounds the original internal edges of either cover by one. If an external type contains $a$, each of its other labels supplies a different edge inside $C(ra)$. Such a type has size at most two. The same holds at $b$; a type missing both is contained in the other two labels. Thus every external type has size at most two.

Moreover, at most one external double can contain $a$: each such double supplies a distinct internal edge of $C(ra)$. By (4.3), outer edges join complementary double types, and every outer edge must meet that one possible double containing $a$. It has at most two outer neighbours, so $o\leq2$. Equation (4.2) gives $q\leq16-1+2=17$, a contradiction. ∎

For full threshold at least twenty-one, independence at a four-edge root also follows directly from (2.3), without a lower bound on $q$.

### 4.3. Restricted supports and complementary doubles

**Lemma 4.2.** Suppose every endpoint of a strong clique $Q'$ belongs to a set $P$, and $G[P]$ has maximum degree at most two.

1. $|Q'|\leq5$.
2. If a set $D\subseteq P$ meets every edge of $Q'$ in exactly one endpoint, then $|Q'|\leq4$.
3. If a selected edge has an endpoint of degree at most one in $G[P]$, then $|Q'|\leq3$.

**Proof.** Conflicts between edges supported on $P$ depend only on adjacency between their endpoints, so they are preserved in $G[P]$. The cover of a selected edge has at most two vertices, each with selected degree at most two, giving the first bound by (2.2). If equality five holds, each such cover has two vertices, both of selected degree two. Given a supported vertex $x$, choose $xy\in Q'$. Equality supplies another original neighbour $a\neq y$ of $x$, with selected degree two; choose $ab\in Q'$ with $b\neq x$. Then $x$ lies in the cover of $ab$, so it also has selected degree two. Consequently all nonzero selected degrees equal two. If every selected edge crosses $D$, its count is the sum of these degrees over $D$, which is even and cannot be five. Finally, the cover within $P$ of a selected edge at a degree-one endpoint has at most one vertex; (2.2) gives the third bound. ∎

If both endpoints of each edge in an outer subfamily have type size at most two, (4.3) makes their types complementary pairs. They lie among external multiple tips, whose original restricted degree is at most two. Fixing a label partitions these tips according to whether their type contains it; every edge of the subfamily crosses this partition. Lemma 4.2 gives at most four such edges. If they are supported on at most three tips, the same partition gives at most $|L||R|\leq2$ edges. These counts use all original adjacency within the support.

### 4.4. Selected tips and fully selected doubles

Let $B$ be the external tips of edges in $K$, and let $D_2$ be the double tips whose two type edges are both selected. Assume $A$ is independent.

The basic witness rule is the following: if $ax,by\in K$, $a\notin T(y)$, and $b\notin T(x)$, then $xy\in E(G)$. The edges are disjoint, and independence of $A$ and the missing type incidences exclude all other cross-edge witnesses.

**Lemma 4.3 (tip bounds and saturation).**

1. If a selected singleton exists, then $|B|\leq6$.
2. $|D_2|\leq4$. If equality holds, the four tips split into two equal-type classes of size two, and each tip's complete original neighbourhood outside $A$ is the other class.
3. If all types have size at most two and $|D_2|=4$, then $B=D_2$.

**Proof.** For a selected singleton edge $ax$, a selected tip whose type misses $a$ must be adjacent to $x$, by the witness rule. Thus
$B\subseteq(N_G(a)\setminus\{r\})\cup(N_G(x)\setminus\{a\})$, proving the first claim.

Fully selected doubles with distinct types are adjacent, by choosing labels in the two type differences. A type class has size at most three, since any of its labels is also adjacent to $r$. If two distinct classes occur, choose one tip from each; every fully selected double lies in the union of their residual neighbourhoods outside $A$, each of size at most two. This gives $|D_2|\leq4$. In the equality case, a tip's class and its complement are both nonempty and each has size at most two: adjacency across different types and the residual capacity two give these bounds. Thus both have size two and saturate all residual neighbours. Applying this observation to a tip in the complement shows that the complement is also an equal-type class.

For the third assertion, take $ay\in K$. Some fully selected double $x$ misses $a$, since a label cannot have four neighbours other than $r$. Because $|T(y)|\leq2$, a label of $T(x)$ is absent from $T(y)$. The witness rule forces $xy$, and the established residual saturation places $y$ in $D_2$. ∎

**Lemma 4.4 (small types and one triple).** At an independent four-edge root:

1. If every type has size at most two, then $q\leq17$.
2. If exactly one tip has type three and all others have type at most two, then $k\leq10$, $o\leq4$, and $q\leq18$.

**Proof.** In the first case, either there is a selected singleton, or $B\subseteq\mathcal P$. Lemma 4.3 and (4.4) give $|B|\leq6$. Each tip supplies one selected type edge, and precisely the fully selected doubles supply a second, so $k=|B|+|D_2|$. If $|D_2|\leq3$, then $k\leq9$; if $|D_2|=4$, then $k=8$. Complementary doubles give $o\leq4$, proving the claim.

For the second case, let $x$ be the triple and $a_0$ its missing label. If at most one type edge at $x$ is selected, at least two of the twelve possible original type incidences are missing from $K$, giving $k\leq10$. Otherwise choose two selected type edges at $x$. A selected tip at $a_0$ misses at least one of their labels, so it must be adjacent to $x$. Since the triple has only one residual neighbour, at most one selected type edge uses $a_0$. The other three labels contribute at most nine, again giving $k\leq10$.

Outer edges avoiding $x$ join complementary doubles, so there are at most four. At most one outer edge meets $x$. If there were five altogether, the four avoiding edges would be supported on at most four doubles, by $3+2|\mathcal P\setminus\{x\}|\leq12$. Eight outer incidences saturate all four doubles, leaving them no neighbours outside their type labels and those four tips. An outer edge at $x$ could not meet those tips and could not conflict with any of the four avoiding edges. This contradiction proves $o\leq4$. ∎

We also use the elementary charge

$$
o+|Z|\leq|\mathcal P|,
\tag{4.6}
$$

where $Z$ is the set of quadruple tips. A quadruple has no outer neighbour. Charge each edge meeting a triple to such a triple, each of which has capacity one. Every remaining outer edge has two double endpoints, whose total incidence capacity is twice the number of doubles. This proves (4.6); zero-type endpoints cannot occur, since their partner would have to be a quadruple incident with an outer edge.

### 4.5. Saturated labels and the triple obstruction

**Lemma 4.5.** Suppose $q\geq16+o$. Then every label in $A$ has selected degree four, and every original type edge is selected. If additionally the neighbourhoods of $r$ and of every label are independent, and there is no quadruple type, then no triple type exists.

**Proof.** The inequality $q\leq\sum_{a\in A}d_Q(a)+o\leq16+o$ forces equality and saturation at every label. Thus all its original incident edges are selected.

Under the independence hypotheses, two original types must be nested or disjoint. Otherwise selected type edges at labels in the two differences force adjacency between the tips. A common label would then have an edge inside its original neighbourhood, a contradiction.

Suppose $x$ has triple type $S$. Every multiple type intersects $S$, and nesting, together with the absence of quadruples, makes it a subset of $S$. Let $b$ be the fourth label. Its three original neighbours other than $r$ are distinct singleton tips of type $\{b\}$, all with selected type edges. Comparing each to a selected type edge of $x$, the witness rule forces three residual neighbours of $x$. A triple can have only one. ∎

Whenever $q\geq18$ and all full degrees are at least nineteen, Lemma 4.1 applies again with each saturated label as the root. This supplies exactly the additional independence hypotheses in Lemma 4.5.

## 5. Stage 2: the candidate-degree interface

### 5.1. Four outer edges on four multiple tips

**Lemma 5.1.** Let $r$ be a four-edge selected root. Suppose $o=4$ and every endpoint of every outer edge belongs to a set $P\subseteq\mathcal P$ of at most four vertices.

1. They cannot occur if every edge of $Q$ has full degree at least twenty-one.
2. They cannot occur even at full threshold twenty.

**Proof.** Every vertex of $P$ has outer degree at most two by (4.3). The eight incidences of the four outer edges force exactly four support vertices, each of outer degree two and type size two. Every outer edge therefore joins complementary types.

Choose an outer edge $uv$, another outer neighbour $x\neq v$ of $u$, and another outer neighbour $y\neq u$ of $v$. All four labels belong to $C(uv)$, by (4.3); so do $x,y$.

At threshold twenty-one, $x\neq y$, because otherwise $uv$ is a triangle edge. The two original type stars at $x,y$ provide four distinct edges inside $C(uv)$. But (2.1) permits at most three at that threshold, proving the first assertion.

At threshold twenty, complementarity still gives $x\neq y$: a common vertex would have to have a type complementary to both complementary endpoint types. The support is therefore exactly $\{u,v,x,y\}$. Of the four outer edges, at most three meet $u$ or $v$, since both have outer degree two and share $uv$. An outer edge avoiding them must be $xy$. It lies inside $C(uv)$ and is distinct from the four type-star edges. Thus $e_G(C(uv))\geq5$, so (2.1) gives $c(uv)\leq19$, a contradiction. ∎

The two versions correspond to separate Lean lemmas. The threshold-twenty-one proof is used in the threshold-twenty-two root bound; the stronger threshold-twenty proof is used in the unique-triple argument below.

### 5.2. A unique triple at threshold twenty

**Lemma 5.2.** At an independent four-edge root, if all selected edges have full degree at least twenty and there is exactly one triple $x$, with all other types of size at most two, then $o\leq3$.

**Proof.** Lemma 4.4 gives $o\leq4$. Suppose $o=4$. Let $P=\mathcal P\setminus\{x\}$. The type budget gives $|P|\leq4$; every outer edge avoiding $x$ has both endpoints in $P$. If no outer edge meets $x$, Lemma 5.1 is a contradiction.

Otherwise exactly one outer edge $xy$ meets the triple, and the other three form a set $R$ supported on $P$. Their six incidences, with degree at most two on at most four vertices, force at least two vertices of $R$-degree two. Their incidence sets, each of size two in a three-edge set, intersect. Hence some $uv\in R$ has both endpoints of $R$-degree two. Each endpoint has at least two original type neighbours, so its original neighbourhood is exhausted by type neighbours and neighbours in $P$.

The edge $xy$ must conflict with $uv$. Since $x\notin P$, and both $x,y$ are external, the saturation just established forces $y\in P$: otherwise the edges have neither a common endpoint nor a cross-edge. Thus all four outer edges are supported on $\mathcal P$. In $G[\mathcal P]$, every vertex has degree at most two, and the triple $x$ has degree at most one. The outer edges remain a strong clique there. Lemma 4.2(3), applied to $xy$, bounds their number by three, a contradiction. ∎

### 5.3. The unconditional threshold-twenty improvement

**Theorem 5.3.** If every member of a strong clique $Q$ has full conflict degree at least twenty, then $q\leq17$.

**Proof.** Assume $q\geq18$. Foundation 2.2 supplies a four-edge root, and Lemma 4.1 makes its neighbourhood independent. The label loads are at most four. We distinguish the original types.

If a quadruple $z$ exists, its contribution three at every label leaves at most one unit there. Every other multiple tip is a double, and no two of those doubles can share a label. The quadruple has no outer neighbour. If an outer edge exists, its endpoints are complementary doubles and use every label. Uniqueness at each label makes them the only other multiple tips; that edge is the only possible outer edge. Thus $o\leq1$, and $q\leq17$, a contradiction.

Suppose there is no quadruple but there are two triples $x,y$. Their types share two labels $a,b$. At either label their total contribution four exhausts the load. Any other type containing that label is a singleton. An outer edge avoiding both triples would need singleton endpoints to cover $a$ and $b$, and could not cover all four labels. Every outer edge therefore meets $x$ or $y$, giving $o\leq2$. Since $q\geq18$, Lemma 4.5 saturates every label; Lemma 4.1 applied at those labels makes their neighbourhoods independent. Lemma 4.5 then excludes the triple, a contradiction.

If there is exactly one triple and no quadruple, Lemmas 4.4 and 5.2 give $q=4+k+o\leq4+10+3=17$. If there is no type larger than two, Lemma 4.4 gives $q\leq17$ directly. These cases exhaust the possibilities. ∎

No four-edge-root assumption appears in this theorem: it is supplied by the contradiction assumption $q\geq18$.

### 5.4. Eight selected type edges at threshold twenty-one

**Lemma 5.4.** At a four-edge selected root, if every member of $Q$ has full degree at least twenty-one and every original type has size at most two, then $k\leq8$.

**Proof.** The root neighbourhood is independent by (2.3). Lemma 4.3 and (4.4) give $|B|\leq6$, and $k=|B|+|D_2|$. If $|D_2|\leq2$, the conclusion follows. If $|D_2|=4$, saturation gives $B=D_2$, so $k=8$. It remains to treat $|D_2|=3$.

Distinct types of fully selected doubles are disjoint. Indeed, the tips are adjacent by the witness rule; a common label would form a triangle containing a selected type edge, forbidden by (2.3).

If two fully selected doubles $x,y$ have distinct types, they are complementary. For a selected edge $aw$, at least one of their types misses $a$. If, say, $a\notin T(x)$, then some label of $T(x)$ is missing from $T(w)$, since $a\in T(w)$ and $|T(w)|\leq2$. The witness rule gives $wx\in E(G)$. Therefore

$$
B\subseteq(N_G(x)\setminus A)\cup(N_G(y)\setminus A),
$$

so $|B|\leq4$, which is more than sufficient.

Otherwise the three fully selected doubles have the same type. Each of its labels has these three neighbours and $r$, exhausting its original degree. Any other selected tip must use a label outside that type, and the same witness argument places it in the residual neighbourhood of one fixed fully selected double. Thus $|B|\leq3+2=5$, and $k\leq5+3=8$. ∎

### 5.5. Three stronger root bounds

**Theorem 5.5.** Suppose $Q$ has a vertex incident with four selected edges. Then the following full-degree bounds hold:

| Full degree of every member | Upper bound on $q$ |
| --- | ---: |
| at least 21 | 16 |
| at least 22 | 15 |
| at least 23 | 13 |

**Proof.** At each threshold the root neighbourhood is independent.

At threshold twenty-one, every load is at most three. If a quadruple exists, it consumes the entire load at every label; no other multiple tip can exist, and there is no outer edge. Hence $q\leq16$. If a triple $x$ exists without a quadruple, it is unique, since two triples share a label and would contribute four. At every label of $T(x)$, at most one other multiple tip can occur. Any outer edge avoiding $x$ joins complementary doubles $u,v$. Every other multiple tip intersects $T(x)$, and uniqueness at that shared label forces it to equal $u$ or $v$. Thus there is at most one outer edge avoiding $x$, and at most one meeting it. Lemma 4.4 gives $k\leq10$, so $q\leq4+10+2=16$. In the remaining small-type case, Lemma 5.4 gives $k\leq8$ and complementary-double counting gives $o\leq4$, again yielding sixteen. The large-type cases are the same root argument already provided by the upstream threshold-twenty-one development.

At threshold twenty-two, loads are at most two, so there is no quadruple. If a triple $x$ exists, every other multiple type would intersect it and exceed the load two at a shared label. Thus $x$ is the only multiple tip. Every outer edge must meet it, giving $o\leq1$; Lemma 4.4 gives $q\leq4+10+1=15$. With only small types, summing loads gives $2|\mathcal P|\leq8$, so $|\mathcal P|\leq4$. We have $k\leq8$ and $o\leq4$. Equality $o=4$ contradicts Lemma 5.1(1), hence $q\leq4+8+3=15$.

At threshold twenty-three, loads are at most one. All types have size at most two, and each label occurs in at most one double type. If an outer edge exists, its complementary endpoint types account for all labels, so these endpoints are the only multiple tips and that edge is the only outer edge. Consequently $o\leq1$, while Lemma 5.4 gives $k\leq8$, proving $q\leq13$. ∎

The root hypothesis is essential to the stated interfaces. We do not assert these three improvements for arbitrary strong cliques without supplying that hypothesis.

### 5.6. A private subcubic bound at a closed centre

**Lemma 5.6.** Let $M$ be a maximum independent set of $H$, let $e=uv\in M$, and suppose $c(e)\geq21$ and $N_{\widehat H}[e]\subseteq F$. If the private clique $P_e$, regarded as a set of original edges, has selected degree at most three at every vertex, then $|P_e|\leq13$.

**Proof.** By (2.3), both endpoints have original degree four and $|C(e)|=6$. Since their private selected degrees are at most three, choose an original edge $uz\notin P_e$ and an original edge $vw\notin P_e$. Neither is $e$.

We first show that no private edge is incident with $z$. The edge $uz$ conflicts with $e$, so neighbourhood closure makes it a candidate. As it is not private to $e$, it is covered by another centre $f\in M\setminus\{e\}$. It cannot equal that centre, since it conflicts with $e$. Thus it conflicts with $f$.

By the cover characterization, $uz$ meets $C(f)$. Its endpoint $u$ cannot lie there: that would make $f$ conflict with $e$. Hence $z\in C(f)$. Any private edge incident with $z$ would also conflict with $f$ (and cannot equal $f$), contrary to privacy. Thus $d_{P_e}(z)=0$. The argument at $w$ is identical.

Both vertices belong to $C(e)$, and they are distinct, since a common vertex would form a triangle on $e$. The other four cover vertices have private selected degree at most three. Equation (2.2) therefore gives

$$
|P_e|-1\leq\sum_{a\in C(e)}d_{P_e}(a)\leq4\cdot3=12.
$$

All connecting edges in this argument are original edges, whether or not private or selected. ∎

### 5.7. The optimized Stage 2 conclusion

**Theorem 5.7 (candidate-degree interface).** If $M$ is tertiary-optimal and $e\in M$ has $\delta(e)=0$, then

$$
d(e)=19.
\tag{5.1}
$$

**Proof.** Lemma 3.3 restricts $d(e)$ to nineteen through twenty-three. Suppose first that $d(e)\in\{21,22,23\}$. Lemma 3.5 supplies $c(e)=d(e)$ and full-neighbourhood closure. The private clique has respective sizes seventeen, sixteen, and fifteen. If it had selected maximum degree at most three, Lemma 5.6 would bound it by thirteen. Hence it has a four-edge selected root. Every private member $x$ has full degree at least $d(x)\geq d(e)$, by private exchange. Theorem 5.5 now gives the respective bounds sixteen, fifteen, and thirteen, contradicting those required sizes. Thus $d(e)\leq20$.

If $d(e)=20$, the private clique has eighteen members, each of full degree at least twenty. Theorem 5.3 bounds it by seventeen, another contradiction. Only degree nineteen remains. ∎

This conclusion assumes neither the absence of twenty-cliques nor a component-correction hypothesis. Its exported statement is only (5.1). The private size nineteen follows directly from the deficit definition when needed. The normalization in Lemma 3.5 is used inside the twenty-one through twenty-three cases; it is not passed to Stage 3.

## 6. Stage 3: nineteen-clique rigidity through a closed support

We prove a structural theorem for an arbitrary original-edge clique, independently of private sets or optimization.

**Theorem 6.1.** Let $Q$ be a strong clique with $|Q|=19$ and $c(e)\geq19$ for every $e\in Q$. Then there is an original twenty-edge strong clique $T\supseteq Q$. Consequently $Q$ is contained in the complete edge set of an original $C_5[2]$ component.

The full-degree hypothesis is explicit: a nineteen-clique by itself only forces full degree at least eighteen.

### 6.1. A quadruple must exist

For the next two lemmas, assume $q\geq19$ and all full degrees in $Q$ are at least nineteen. Foundation 2.2 supplies a four-edge root, Lemma 4.1 makes $A$ independent, and (4.5) gives $\lambda(a)\leq5$.

Three distinct tips of type at least three are impossible. Three three-element subsets of a four-element set have a common label; their contributions at that label would total at least six.

**Lemma 6.2.** If two triple tips exist, then $o\leq3$.

**Proof.** Let the tips be $x,y$, and suppose $o\geq4$. The type budget gives

$$
2|\mathcal P|+2\leq12,\qquad |\mathcal P|\leq5.
$$

No third type of size at least three exists, so an outer edge avoiding $x,y$ is supported on $D=\mathcal P\setminus\{x,y\}$. At most one outer edge meets each triple. If $|\mathcal P|\leq4$, then $|D|\leq2$, which supports at most one simple edge. This would give $o\leq3$. Therefore $|\mathcal P|=5$.

The two triples and three other multiple tips use all twelve type incidences. There are no singleton types anywhere. There is also no quadruple, since it and the two triples would contradict the preceding common-label argument. An outer endpoint cannot have type zero, because its partner would have to be a quadruple. Hence every outer endpoint lies in $\mathcal P$.

The original restricted graph $G[\mathcal P]$ has maximum degree at most two, while either triple has restricted degree at most one. If an outer edge met a triple, Lemma 4.2(3) would give $o\leq3$. Thus all outer edges avoid both triples and are supported on the three vertices of $D$. Their degrees are at most two, so the handshake identity gives $2o\leq6$, again a contradiction. ∎

**Lemma 6.3.** Every such $Q$ has a quadruple at its four-edge root.

**Proof.** Suppose no quadruple exists. If there is no triple, the upstream small-type bound $q\leq18$ already contradicts $q\geq19$; Lemma 4.4 explains the stronger seventeen bound, but that improvement is unnecessary in this branch. If there is exactly one triple, Lemma 4.4 gives $q\leq18$. Otherwise there are two triples, and Lemma 6.2 gives $o\leq3$. Since $q\geq19$, all labels are saturated by Lemma 4.5. Their neighbourhoods are independent by Lemma 4.1 applied at those labels. Lemma 4.5 excludes the triple, a contradiction. ∎

### 6.2. Four doubles and twelve original type incidences

Fix a quadruple $z$. Equation (4.1) gives $o\geq3$, and (4.6) gives $|\mathcal P|\geq o+1\geq4$.

**Lemma 6.4.** Every original type other than that of $z$ has size at most two. Moreover, $\mathcal P$ consists of $z$ and exactly four double tips, these five tips use all twelve type incidences, and $3\leq o\leq4$.

**Proof.** If another tip $y$ had type size at least three, choose a third multiple tip $w\neq z,y$, possible since $|\mathcal P|\geq4$. The types of $y,w$ intersect. At a common label the quadruple, $y$, and $w$ contribute at least $3+2+1=6$, violating the load bound five. This proves the first assertion and also uniqueness of the quadruple.

Let $D=\mathcal P\setminus\{z\}$. The type budget gives $|D|\leq4$. The quadruple cannot meet an outer edge, so all outer endpoints are complementary doubles in $D$. If $|D|\leq3$, the bipartite count following Lemma 4.2 gives $o\leq2$. Thus $|D|=4$. These four doubles and $z$ contribute exactly $4+4\cdot2=12$ type incidences. No other nonempty type can exist. Finally (4.6) gives $o+1\leq|\mathcal P|=5$, as required. ∎

### 6.3. A closed original support on at most ten vertices

**Lemma 6.5.** Under the preceding hypotheses, every member of $D$ has all its original neighbours outside $A$ in $D$. The set

$$
S=\{r\}\cup A\cup\mathcal P
$$

has at most ten vertices, contains all endpoints of $Q$, and is closed under original adjacency.

**Proof.** If $o=4$, its eight incidences on the four doubles force outer degree two at each. Their two original type neighbours and two outer neighbours exhaust original degree four, proving residual closure.

If $o=3$, then $q\geq19=16+o$, so Lemma 4.5 makes every original type edge selected. The four doubles are exactly the four fully selected doubles. Lemma 4.3 gives closure of their entire residual original neighbourhoods, including any unselected edges, inside $D$.

Now $|S|\leq1+4+5=10$. The neighbours of $r$ are $A$; those of $z$ are also exactly $A$, since $z$ has type four. Every neighbour other than $r$ of a label has nonempty type, hence belongs to $\mathcal P$ by Lemma 6.4. A double has its type neighbours in $A$ and its remaining neighbours in $D$. This proves closure.

Every selected edge is a root edge, a type edge, or an outer edge. Nonempty types all lie in $\mathcal P$, and outer endpoints lie in $D$. Hence every selected endpoint belongs to $S$. ∎

This is the closed-support argument used by Lean. It does not require a separate classification of labelled four-cycles in the quadruple case.

### 6.4. Completing a nineteen-edge clique

**Proof of Theorem 6.1.** Apply Lemma 6.5, and let $T=E(G[S])$ be all original edges inside the closed set $S$, including unselected ones. The degree bound and handshake identity give

$$
|T|\leq\tfrac12\sum_{v\in S}d_G(v)\leq20.
$$

For $e\in Q$, every full conflict neighbour is also supported on $S$. This follows either from the endpoint characterization or by first finding an endpoint of that neighbour in $C(e)\subseteq S$, and then using closure once more for its other endpoint. Therefore

$$
N_{\widehat H}(e)\subseteq T\setminus\{e\}.
$$

The left-hand side has at least nineteen members, and the right-hand side at most nineteen. Equality follows, and $|T|=20$. This holds for every $e\in Q$. Since $|Q|=19$, only one edge of $T$ is outside $Q$. Every pair of distinct members of $T$ therefore has at least one member in $Q$, whose neighbourhood is exactly all other members of $T$. Thus $T$ is a strong clique. Foundation 2.3 identifies it with the full edge set of an original $C_5[2]$ component. ∎

The completion is in the original graph. Membership of its twentieth edge in a candidate set has not been assumed or proved at this stage.

## 7. Eliminating zero deficit and proving compensation

### 7.1. Degree nineteen requires only secondary optimization

**Lemma 7.1.** Let $M$ be optimal, let $e\in M$, and suppose $\delta(e)=0$ and $d(e)=19$. Then $F$ contains a twenty-edge strong clique.

**Proof.** The deficit definition gives

$$
39=19+1+|P_e|,\qquad |P_e|=19.
$$

The private set is a clique, and for every $x\in P_e$,
$c(x)\geq d(x)\geq d(e)=19$. Theorem 6.1 extends it to an original twenty-clique $T$. Since $e\in P_e$, the centre lies in $T$.

Foundation 2.3 makes $T$ conflict-closed. Consequently

$$
N_{\widehat H}(e)\subseteq T\setminus\{e\},\qquad
19=d(e)\leq c(e)\leq19.
$$

Thus the full and candidate neighbourhoods of $e$ have equal finite cardinalities. As the latter is their intersection with $F$, every full neighbour is a candidate. Every other edge of $T$ conflicts with $e$, and $e\in F$ already. Hence $T\subseteq F$. ∎

This proof uses only optimality, not tertiary optimality. It recovers full degree and neighbourhood closure after applying rigidity, rather than importing the stronger normalization conclusion of Lemma 3.5. This order is the optimized interface.

### 7.2. Positive deficits

**Theorem 7.2.** Suppose every strong clique contained in $F$ has at most nineteen edges. For every tertiary-optimal $M$,

$$
\delta(e)\geq1\quad(e\in M),\qquad
\sum_{e\in M}\delta(e)+R\geq|M|.
\tag{7.1}
$$

**Proof.** First the upstream local-39 argument gives $\delta(e)\geq0$. Its relevant count is short enough to display. Privacy and the clique exclusion give $|P_e|\leq\min\{d(e)+1,19\}$; exchange supplies full degree at least $d(e)$ for every private member. Apply Foundation 2.1 where appropriate:

| Candidate centre degree | Bound on private size | Bound on $L(e)$ |
| --- | ---: | ---: |
| $d(e)\leq18$ | $d(e)+1$ | $2d(e)+2\leq38$ |
| 19 | 19 | 39 |
| 20 | 18 | 39 |
| 21 | 17 | 39 |
| 22 | 16 | 39 |
| 23 | 15 | 39 |
| 24 | 13 | 38 |

These cover all degrees because $d(e)\leq24$. If a deficit were zero, Theorem 5.7 would give candidate degree nineteen, and Lemma 7.1 would give a twenty-clique contained in $F$, contrary to the hypothesis. An integer which is nonnegative and nonzero is at least one. Summation and $R\geq0$ prove the second assertion. ∎

**Corollary 7.3 (uncorrected packing without a twenty-clique).** Under the same exclusion hypothesis, $F$ contains an induced matching $M$ with $|F|\leq19|M|$.

**Proof.** Choose a tertiary-optimal maximum independent set of $H$. By Lemma 3.2 and Theorem 7.2,

$$
2|F|=39|M|-\sum_e\delta(e)-R\leq38|M|.
$$

Its independence in $H$ is exactly the required induced-matching property in $G$. The empty candidate set is included. ∎

The result holds for arbitrary matching number. No finite enumeration, abstract conflict-graph realization assumption, or separate analysis of matching numbers two and three is used.

## 8. Restoring exceptional components and sharpness

### 8.1. Induction with the twenty-clique count

Let

$$
\kappa_G(F)=|\{T\subseteq F:|T|=20,\ T\text{ is a strong clique in }G\}|.
$$

**Lemma 8.1.** Every $F$ contains an induced matching $M$ such that

$$
|F|\leq19|M|+\kappa_G(F).
\tag{8.1}
$$

**Proof.** Use strong induction on $|F|$, always in the same original graph $G$. If no twenty-clique is contained in $F$, Foundation 2.3 says every contained clique has size at most nineteen, and Corollary 7.3 applies.

Otherwise choose a twenty-clique $T\subseteq F$ and put $F'=F\setminus T$. Distinct twenty-cliques are disjoint, so the twenty-cliques contained in $F'$ are exactly those contained in $F$ other than $T$. Therefore

$$
|F|=|F'|+20,\qquad \kappa_G(F)=\kappa_G(F')+1.
$$

The induction hypothesis supplies $M'\subseteq F'$. Choose any $e\in T$. Conflict closure of $T$ ensures that $e$ conflicts with no member of $M'$. Thus $M=M'\cup\{e\}$ is an induced matching and

$$
\begin{aligned}
|F|&\leq19|M'|+\kappa_G(F')+20\\
&=19(|M'|+1)+(\kappa_G(F')+1)
=19|M|+\kappa_G(F).
\end{aligned}
$$

This completes the induction. ∎

### 8.2. The literal component correction

**Proof of Theorem 1.1.** Foundation 2.3 sends each twenty-clique in $F$ to a whole original $C_5[2]$ component whose twenty edges are selected. This map is injective: a component determines its complete edge set. Hence $\kappa_G(F)\leq t_G(F)$, and Lemma 8.1 gives (1.1). Finally $|M|\leq\alpha(H)=\nu_s^G(F)$, yielding the independence-number statement. ∎

The Lean implementation expresses this last comparison in two steps. It bounds `twentyCliquesIn` by `tightComponentCount`, which counts the certified original vertex supports, and then uses the upstream equality between that support count and the cardinality of `tightComponentsIn`, the set of actual original connected components. The certificate is a property of a support, not a choice of a five-pair labelling, so no multiplicity of representations is counted.

Equivalently, one may remove all $t=t_G(F)$ fully selected exceptional components at once. Their edge sets are mutually conflict-disconnected and each contributes exactly one induced-matching member, giving

$$
|F_0|=|F|-20t,\qquad
\nu_s^G(F_0)=\nu_s^G(F)-t.
$$

The induction above is the route used in `Main.lean`; the simultaneous removal interpretation explains the correction combinatorially.

### 8.3. Sharpness and the original critical examples

Take $G=C_5[2]$ and select any nineteen of its twenty edges. Its full conflict graph is $K_{20}$: two distinct edges either meet or have adjacent endpoints, as follows from the complete joins between consecutive pairs of the five-cycle. Thus $\nu_s^G(F)=1$, while $t_G(F)=0$. Equality $|F|=19$ proves that the constant nineteen cannot be decreased.

For this proper selection, an optimal centre has candidate degree eighteen, private size nineteen, and deficit one. For the full twenty-edge selection, the corresponding deficit is minus one and the correction is one. These examples distinguish the scope of Theorem 7.2 from that of the corrected theorem. The explicit sharpness construction is a paper argument here and has finite regression checks; it is not a separately declared theorem in the current Lean extension.

In particular, if $t_G(F)=0$ and $\nu_s^G(F)\leq2$, then $|F|\leq38$. This rules out the proposed thirty-nine-edge obstruction. The same proof handles every larger matching number.

Before exceptional-component removal, the exact identity gives the corrected equivalence

$$
|F|\leq19|M|+t_G(F)
\quad\Longleftrightarrow\quad
\sum_e\delta(e)+R\geq|M|-2t_G(F)
$$

for any maximum independent set. The stronger pointwise positive-deficit claim is made only under the twenty-clique exclusion.

## Appendix A. Correspondence with the Lean development

The primary endpoint is `StrongEdge19.prescribed_edge_bound19`. Its graph hypothesis is only the original maximum-degree bound, in a finite simple graph. The matching-witness version is `StrongEdge19.induced_matching_packing19_with_connected_component_count`. The source contains the usual finiteness and decidability instances; these add no structural restriction on the finite graph.

### A.1. Established upstream results

Names in this table have namespace `StrongEdge`.

| Paper result | Source | Principal declaration or interface |
| --- | --- | --- |
| Full-degree thresholds, Foundation 2.1 | [Packing195Thresholds.lean](../../upstream/packing195/lean/StrongEdge/Packing195Thresholds.lean) and its imported bounds | `cliqueBounds195_of_degree_le_four`; the stronger threshold-24 value is `high24_clique_card_le_thirteen` |
| Selected subcubic bound, Foundation 2.2 | [SubcubicSeventeen.lean](../../upstream/packing195/lean/StrongEdge/Bounds/SubcubicSeventeen.lean) | `clique_card_le_seventeen_of_support_degree_le_three` |
| Original component certificate, Foundation 2.3 | [TwentyCliqueRigidity.lean](../../upstream/packing195/lean/StrongEdge/Bounds/TwentyCliqueRigidity.lean) | `twenty_clique_support_is_five_cycle_blowup` |
| Universal twenty-edge upper bound, Foundation 2.3 | [TwentyCliqueSaturation.lean](../../upstream/packing195/lean/StrongEdge/Bounds/TwentyCliqueSaturation.lean) | `clique_card_le_twenty` |
| Conflict closure used in Sections 7–8 | [TwentyCliqueComponent.lean](../../upstream/packing195/lean/StrongEdge/Bounds/TwentyCliqueComponent.lean) | `twenty_clique_conflict_closed` |
| Private exchange, Lemma 3.1 | [Basic.lean](../../upstream/packing195/lean/StrongEdge/Basic.lean), [PrivateExchange.lean](../../upstream/packing195/lean/StrongEdge/PrivateExchange.lean) | `private_isClique`, `private_degree_mono`, `IsOptimal` |
| Root tools in Lemmas 4.3–4.4 | [RootCounting.lean](../../upstream/packing195/lean/StrongEdge/Bounds/RootCounting.lean), [High21Double.lean](../../upstream/packing195/lean/StrongEdge/Bounds/High21Double.lean), [High21ImprovedRoot.lean](../../upstream/packing195/lean/StrongEdge/Bounds/High21ImprovedRoot.lean), [High20UniqueTriple.lean](../../upstream/packing195/lean/StrongEdge/Bounds/High20UniqueTriple.lean) | `rootTips_card_le_six_of_single`, `fullDoubleTips_card_le_four`, `fullDoubleTips_saturated_of_four`, `root_card_le_ten_of_unique_triple` |
| Literal component count, Section 8.2 | [TightComponents.lean](../../upstream/packing195/lean/StrongEdge/TightComponents.lean) | `tightComponentCount_eq_connected_component_count` |
| Removal and comparison of twenty-clique counts, Section 8 | [Packing195Unconditional.lean](../../upstream/packing195/lean/StrongEdge/Packing195Unconditional.lean) | `twentyCliquesIn_sdiff`, `twenty_clique_count_le_tight_component_count` |

### A.2. Extension modules

Every declaration listed below has namespace `StrongEdge19`. The table includes all 83 mathematical declarations in the optimized extension, grouping implementation helpers with the paper argument they support. A group may correspond to several intermediate finite-set steps rather than to a separate paper theorem.

| Paper location | Lean module | Declarations |
| --- | --- | --- |
| Section 3.2 | [Compensation.lean](../lean/StrongEdge19/Compensation.lean) | `excessCoverage`, `deficit`, `privateOwners_card_eq_indicator`, `coverage_pointwise_exact`, `private_double_count_exact`, `compensation_identity`, `nineteen_bound_iff_compensation`, `nineteen_bound_of_positive_deficits` |
| Sections 3.1 and 3.3 | [Tertiary.lean](../lean/StrongEdge19/Tertiary.lean) | `IsTertiaryOptimal`, `tertiary_optimal_exists`, `private_swap_optimal`, `private_cost_mono_of_equal_degree`, `centre_cost_eq_degree_of_private_witness` |
| Sections 3.3 and 7.1 | [CriticalNormalization.lean](../lean/StrongEdge19/CriticalNormalization.lean) | `induced_neighborhood_closed_of_degree_eq`, `induced_clique_image`, `zero_deficit_degree_range`, `zero_deficit_full_degree_witness`, `zero_deficit_full_degree_and_closed_neighborhood` |
| Lemma 4.1 and root existence | [Root19.lean](../lean/StrongEdge19/Root19.lean) | `large_clique_exists_root_four`, `high19_triangle_external_multiple_card_le_one`, `high19_root_triangle_outer_card_le_two`, `high19_large_clique_root_neighborhood_independent` |
| Sections 4.1 and 6.1 | [RootLoad.lean](../lean/StrongEdge19/RootLoad.lean) | `root_label_load_add_degree_le_twenty_four`, `high19_root_label_budget_five`, `three_triple_types_share_label`, `high19_no_three_triple_types` |
| Lemma 4.5 and Section 6.1 | [RootSaturation.lean](../lean/StrongEdge19/RootSaturation.lean) | `labels_saturated_of_card_ge_sixteen_add_outer`, `no_triple_of_saturated_independent_labels`, `high19_large_triple_requires_four_outer_edges` |
| Lemma 4.2 and Lemma 6.2 | [OuterSupport.lean](../lean/StrongEdge19/OuterSupport.lean) | `edges_supported_on_two_card_le_one`, `restricted_degree_two_clique_at_leaf_card_le_three`, `multiple_restricted_degree_add_type_le_four`, `high19_two_triples_outer_card_le_three` |
| Section 4.3 and Lemma 6.4 | [BipartiteSupport.lean](../lean/StrongEdge19/BipartiteSupport.lean) | `edges_crossing_parts_card_le_product`, `small_complementary_types_outer_card_le_two` |
| Lemma 5.1 | [TypeCover.lean](../lean/StrongEdge19/TypeCover.lean) | `two_type_stars_inside`, `two_type_stars_inside_add_external_edge`, `outer_root_neighborhood_subset_cover`, `exists_other_outer_neighbor` |
| Lemmas 5.1 and 5.2 | [OuterSaturation.lean](../lean/StrongEdge19/OuterSaturation.lean) | `three_outer_edges_have_saturated_pair`, `four_outer_edges_impossible_at_high20` |
| Lemma 5.2 | [High20Triple.lean](../lean/StrongEdge19/High20Triple.lean) | `high20_unique_triple_outer_card_le_three` |
| Lemma 4.4 and Theorem 5.3 | [High20Root.lean](../lean/StrongEdge19/High20Root.lean) | `high20_outer_card_le_one_of_root_type_four`, `small_types_clique_card_le_seventeen`, `high20_clique_card_le_seventeen` |
| Lemma 5.4 and Theorem 5.5 | [SmallTypes.lean](../lean/StrongEdge19/SmallTypes.lean) | `selected_tip_adj_full_double_of_missing_label`, `rootTips_card_le_four_of_disjoint_full_double_types`, `rootTips_card_le_five_of_three_equal_full_double_types`, `high21_small_types_rootEdges_card_le_eight`, `high21_clique_card_le_sixteen_of_root_four` |
| Lemma 5.1 and Theorem 5.5 | [High22Root.lean](../lean/StrongEdge19/High22Root.lean) | `four_outer_edges_impossible_at_high21`, `high22_clique_card_le_fifteen_of_root_four` |
| Theorem 5.5 | [High23Root.lean](../lean/StrongEdge19/High23Root.lean) | `high23_clique_card_le_thirteen_of_root_four` |
| Section 2 and Lemma 5.6 | [EndpointConflict.lean](../lean/StrongEdge19/EndpointConflict.lean) | `strongConflict_of_shared_endpoint`, `strongConflict_of_adjacent_endpoints`, `strongConflict_of_meets_cover` |
| Lemma 5.6 | [PrivateSubcubic.lean](../lean/StrongEdge19/PrivateSubcubic.lean) | `private_missing_edge_zero_incidence`, `private_subcubic_card_le_thirteen` |
| Theorem 5.7 | [CriticalHighDegree.lean](../lean/StrongEdge19/CriticalHighDegree.lean) | `zero_deficit_degree_le_twenty`, `zero_deficit_candidate_degree_eq_nineteen` |
| Lemma 6.3 | [QuadType.lean](../lean/StrongEdge19/QuadType.lean) | `high19_large_clique_exists_type_four` |
| Lemma 6.4 | [QuadLoad.lean](../lean/StrongEdge19/QuadLoad.lean) | `high19_no_quad_triple_multiple`, `high19_large_quad_other_types_le_two` |
| Lemma 6.4 | [QuadCore.lean](../lean/StrongEdge19/QuadCore.lean) | `high19_large_quad_outer_supported`, `high19_large_quad_counts`, `high19_large_quad_positive_type_support` |
| Lemma 6.5 | [ClosedCore.lean](../lean/StrongEdge19/ClosedCore.lean) | `high19_large_quad_residual_closed`, `high19_large_clique_closed_ten_support` |
| Theorem 6.1 and Section 6.4 | [NineteenRigidity.lean](../lean/StrongEdge19/NineteenRigidity.lean) | `closed_ten_edges_card_le_twenty`, `conflict_stays_in_closed_support`, `high19_nineteen_clique_extends_to_twenty`, `high19_nineteen_clique_in_five_cycle_blowup` |
| Lemma 7.1 | [CriticalNineteen.lean](../lean/StrongEdge19/CriticalNineteen.lean) | `critical_degree_nineteen_forces_selected_twenty` |
| Theorem 7.2 | [PositiveDeficits.lean](../lean/StrongEdge19/PositiveDeficits.lean) | `zero_deficit_impossible`, `deficit_pos_of_no_twenty_clique`, `global_compensation_of_no_twenty_clique` |
| Corollary 7.3 | [Packing.lean](../lean/StrongEdge19/Packing.lean) | `induced_matching_packing19_of_no_twenty_clique` |
| Section 8 and Theorem 1.1 | [Main.lean](../lean/StrongEdge19/Main.lean) | `induced_matching_packing19_with_twenty_clique_count`, `induced_matching_packing19_unconditional`, `induced_matching_packing19_with_connected_component_count`, `induced_matching_packing19_of_no_full_tight_component`, `prescribed_edge_bound19`, `candidate_card_le_thirty_eight_of_indepNum_le_two` |

### A.3. The optimized dependency boundary

Theorem 5.7 corresponds to `zero_deficit_candidate_degree_eq_nineteen`. It concludes only candidate degree nineteen; it has no no-twenty-clique hypothesis. Its proof still uses tertiary normalization inside `zero_deficit_degree_le_twenty`, where the twenty-one through twenty-three cases need full-neighbourhood closure.

Lemma 7.1 corresponds to `critical_degree_nineteen_forces_selected_twenty`. Its assumption is `IsOptimal`, not `IsTertiaryOptimal`. It derives private size directly from the deficit, applies `high19_nineteen_clique_extends_to_twenty`, and obtains full degree and candidate membership using upstream twenty-clique closure and `induced_neighborhood_closed_of_degree_eq`.

`zero_deficit_impossible` combines these two interfaces. The proof then passes through positive deficits, exact compensation, the no-twenty-clique packing theorem, restoration by induction, and the literal component-count endpoint. There is no reverse dependency from the Stage 2 high-degree exclusions to Stage 3 nineteen-clique rigidity.

In the small-type branch of Lemma 6.3, Lean invokes the upstream `clique_card_le_eighteen_of_independent_root_types_le_two`. It does not import `High20Root.lean` to use its stronger seventeen bound. Section 4.4 includes that stronger elementary count because it is used by the threshold-twenty proof, while the Stage 3 dependency remains on the older sufficient interface.

## Appendix B. Verification status and scope

The optimized mathematical source [2] was compiled with Lean `4.35.0-rc4`. Its [recorded verification](../verification/interface-refactor/candidate/results.json) covers 29 Lean files and audits all 83 new declarations. The [raw compiler output](../verification/interface-refactor/candidate/build-and-audit.log) records only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`. No additional mathematical axiom, proof placeholder, or hidden graph hypothesis is introduced.

This manuscript changes no Lean source, original conflict definition, induced-matching definition, or correction definition. Its correspondence check compares the mathematical source hashes with that existing verified record and checks the cited declarations. This is documentation validation, not a new compilation and not machine verification of the English prose. The individual foundational results remain the unchanged theorems of the pinned 19.5 project.

The [Stage 2](../results/stage2-checks.json) and [Stage 3](../results/stage3-checks.json) finite checks concern their explicitly stated families and examples. They are not proof certificates used by Lean and do not replace any universal argument above. The sharpness example in Section 8.3 and the explanatory maximality weakening after Lemma 3.2 are paper observations; the current Lean identity assumes a maximum independent set, and the explicit sharpness construction has no separate extension declaration.

For build reproduction, see the [Lean extension guide](../lean/README.md). For the measured difference between the preserved original implementation and the optimized interface, see the [interface review](../notes/candidate-degree-interface-review.md). Earlier Stage 1–3 notes record the research history; this manuscript is the consolidated proof matching the optimized source.

The [documentation validation record](validation.json) is reproduced from the repository root with `python route-b/scripts/check-manuscript.py`. It checks the complete 83-declaration concordance, statement references, local links, math delimiters, English-text consistency, and unchanged audited source hashes.

## AI assistance and verification

This research was conducted predominantly using generative AI systems, including mathematical exploration, proof development, Lean formalization, and manuscript preparation. OpenAI generative AI systems, including Codex, were used for this work under the direction of **Congyue Mao**. The formal proof terms were checked by the Lean kernel, with the verification record described in Appendix B. This kernel verification applies to the formal development; the English exposition and PDF typesetting were reviewed separately.

## References

[1] C. Mao, *A Corrected 19.5 Bound for Induced Matchings in Prescribed Edge Sets*. Proof manuscript and verified Lean development, 10 October 2026. [Source and manuscript](https://github.com/congyuemao/strong-edge-packing-195/tree/2e91b05b25a4ee931a0490fefcdbb4f253be95c8). Pinned foundation: `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`.

[2] C. Mao, *StrongEdge19: Corrected Nineteen Packing in Prescribed Edge Sets*. Lean source and verification archive, 11 October 2026. [Optimized mathematical source](https://github.com/congyuemao/strong-edge-packing-19/tree/2c20ac6099a0fb581367e3bee39465aafec5f879). This manuscript follows that audited mathematical source; subsequent commits add exposition and publishing files.
