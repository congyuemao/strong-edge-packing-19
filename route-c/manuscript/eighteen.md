# Strong Cliques and the Eighteen Bound for Induced Matchings in Graphs of Maximum Degree Four

*Sharpness of the whole-edge-set bound, nineteen-edge strong cliques, and the clique case for prescribed edge sets*

**Author:** Congyue Mao

**Date:** 30 October 2026.

## Abstract

Let $G$ be a finite simple graph of maximum degree at most four. Two edges conflict if they share an endpoint or an edge of $G$ joins an endpoint of one to an endpoint of the other. An induced matching is a set of pairwise non-conflicting edges, and a strong clique is a set of pairwise conflicting edges. We prove three results.

First, all eighteen edges of the circulant $C_9(1,3)$ pairwise conflict. Hence its induced matching number equals $m/18$. Joos's theorem implies $\nu_s(G)\geq m(G)/18$ for graphs of maximum degree at most four without components isomorphic to $C_5[2]$; this example shows that the bound is attained, and disjoint copies refute Joos's conjecture that $\nu_s(G)\geq m(G)/17$ for such graphs.

Second, every strong clique with at least nineteen edges lies inside a connected component isomorphic to $C_5[2]$. Consequently a graph without such components has strong clique number at most eighteen, with equality for $C_9(1,3)$. This removes the conflict-degree hypothesis from the nineteen-clique rigidity theorem of the companion nineteen manuscript. The proof combines an incidence inequality, which confines a nineteen-edge strong clique to at most eighteen endpoints, with an exhaustive SAT search over the remaining finite configurations; every instance was answered by two independent solvers.

Third, for a prescribed edge set $F\subseteq E(G)$ we propose the eighteen-fold bound $|F|\leq18\nu_s^G(F)+\tau_G(F)$. Here $\tau_G(F)$ adds $\max\{0,|F\cap E(C)|-18\}$ over the components $C$ isomorphic to $C_5[2]$. This conjecture implies the proved nineteen bound. We prove it for $F=E(G)$ and whenever $\nu_s^G(F)\leq1$, and show that it is sharp.

**Keywords.** Induced matching; strong clique; square of a line graph; prescribed edge set; doubled five-cycle; SAT; computer-assisted proof.

**Contents:** [Introduction](#1-introduction-and-results) · [The circulant](#2-the-circulant-c_913) · [Incidence inequality](#3-an-incidence-inequality-for-strong-cliques) · [Reduction](#4-reduction-to-finitely-many-configurations) · [Search](#5-the-exhaustive-search) · [Clique theorem](#6-proof-of-the-clique-theorem) · [Prescribed sets](#7-the-eighteen-bound-for-prescribed-edge-sets) · [Scope](#appendix-a-verification-status-and-scope).

## 1. Introduction and results

### 1.1. Conventions

Throughout, $G$ is a finite simple graph with $\Delta(G)\leq4$, $n(G)=|V(G)|$ and $m(G)=|E(G)|$. Two distinct edges **conflict** if they share an endpoint, or some edge of $G$ joins an endpoint of one to an endpoint of the other. This is adjacency in the square of the line graph, $L(G)^2$. All conflicts are evaluated in the whole graph $G$: selecting a subset of edges never removes the edges that witness conflicts.

An **induced matching** is a set of pairwise non-conflicting edges. For $F\subseteq E(G)$, let $\nu_s^G(F)$ be the largest size of an induced matching of $G$ contained in $F$, and write $\nu_s(G)=\nu_s^G(E(G))$. A **strong clique** is a set of pairwise conflicting edges; $\omega_s(G)$ is the largest size of one. Thus $\nu_s^G(F)\leq1$ exactly when $F$ is empty or a strong clique.

$C_5[2]$ is obtained from the five-cycle by replacing every vertex by an independent pair and every edge by the four edges between the corresponding pairs. It is 4-regular with ten vertices and twenty edges, and all twenty edges pairwise conflict. For $k\geq1$ and $S\subseteq\{1,\dots,\lfloor k/2\rfloor\}$, the circulant $C_k(S)$ has vertex set $\mathbb{Z}_k$ and edges $\{i,i\pm s\}$ for $s\in S$. For a strong clique $F$, write $V(F)$ for the set of endpoints and $d_F(x)$ for the number of edges of $F$ at $x$.

For $F\subseteq E(G)$ define

$$
\tau_G(F)=\sum_{C}\max\{0,\ |F\cap E(C)|-18\}, \tag{1.1}
$$

where $C$ ranges over the connected components of $G$ isomorphic to $C_5[2]$. The companion manuscripts use instead $t_G(F)$, the number of such components whose whole edge set lies in $F$ [1, 2].

### 1.2. Background

The Erdős–Nešetřil conjecture [3] predicts that graphs of maximum degree four have strong chromatic index at most twenty; the best general bound is twenty-one [4]. Since a strong edge colouring partitions the edges into induced matchings, it would imply $|F|\leq20\nu_s^G(F)$ for every $F$. Chung, Gyárfás, Tuza and Trotter [5] showed that a graph of maximum degree four whose edges pairwise conflict has at most twenty edges, with equality only for $C_5[2]$. The companion 19.5 project proves the version that allows conflict witnesses outside the clique: every strong clique has at most twenty edges, and a twenty-edge strong clique is exactly the edge set of a $C_5[2]$ component [1, Theorem 6.4].

For whole edge sets, Joos proved [6, Theorem 1] that

$$
\nu_s(G)\geq\frac{n(G)-i(G)-n_5(G)}{9}, \tag{1.2}
$$

where $i(G)$ is the number of isolated vertices and $n_5(G)$ the number of components isomorphic to $C_5[2]$. Nguyen [7] independently proved the same bound for connected graphs; the two works appeared jointly as [8]. Since every non-isolated vertex has degree at most four, $m(G)\leq2(n(G)-i(G))$, so (1.2) gives $\nu_s(G)\geq m(G)/18$ when $n_5(G)=0$. Joos remarked that he could not construct a graph without a $C_5[2]$ component attaining $m(G)/18$. He described a graph with $\nu_s=m/17$ and conjectured [6, Conjecture 2]:

> If $G$ has maximum degree at most four and no component isomorphic to $C_5[2]$, then $\nu_s(G)\geq m(G)/17$.

For prescribed edge sets the companion manuscripts prove $2|F|\leq39\nu_s^G(F)+t_G(F)$ [1] and

$$
|F|\leq19\nu_s^G(F)+t_G(F), \tag{1.3}
$$

the latter with a complete Lean formalization [2]. The constant nineteen in (1.3) is attained by nineteen edges of a $C_5[2]$ component, for which $t_G(F)=0$.

### 1.3. Results

**Proposition 1.1.** All eighteen edges of the 4-regular graph $C_9(1,3)$ pairwise conflict. Consequently $\nu_s(C_9(1,3))=1=m(C_9(1,3))/18$, and for every $k\geq1$ the disjoint union of $k$ copies has $\nu_s=k=m/18$. In particular Joos's conjecture quoted above is false, and the bound $\nu_s(G)\geq m(G)/18$ is best possible for graphs of maximum degree at most four without $C_5[2]$ components.

The circulant also attains (1.2) with equality, since $n=9$ and $\nu_s=1$.

**Theorem 1.2.** Let $F$ be a strong clique with $|F|\geq19$. Then $G$ has a component $C\cong C_5[2]$ with $F\subseteq E(C)$.

**Corollary 1.3.** If no component of $G$ is isomorphic to $C_5[2]$, then $\omega_s(G)\leq18$. Equality holds for $G=C_9(1,3)$.

Theorem 1.2 strengthens [2, Theorem 6.1], which reaches the same conclusion for nineteen-edge strong cliques whose edges all have conflict degree at least nineteen. That manuscript observes that a nineteen-edge strong clique by itself only forces conflict degree at least eighteen. Theorem 1.2 shows that no such clique exists outside $C_5[2]$. Its proof is computer-assisted: Section 3 proves by hand that the endpoint set is small, and Section 5 searches the remaining configurations exhaustively.

**Conjecture 1.4 (eighteen bound for prescribed edge sets).** For every $F\subseteq E(G)$,

$$
|F|\leq18\nu_s^G(F)+\tau_G(F). \tag{1.4}
$$

**Theorem 1.5.** Inequality (1.4) holds in each of the following cases:

1. $F=E(G)$;
2. $\nu_s^G(F)\leq1$.

It is attained by $F=E(C_9(1,3))$ and by any nineteen or twenty edges of a $C_5[2]$ component, and by disjoint unions of these examples.

**Proposition 1.6.** Conjecture 1.4 implies (1.3).

Thus Conjecture 1.4 is the natural common strengthening of the prescribed-set nineteen bound and of the whole-edge-set eighteen bound. Proposition 1.1 shows that eighteen cannot be lowered: every constant smaller than eighteen already fails for $F=E(G)$.

## 2. The circulant $C_9(1,3)$

**Proof of Proposition 1.1.** Write $G=C_9(1,3)$. Its edges are the nine **short** edges $\{i,i+1\}$ and the nine **long** edges $\{i,i+3\}$, indices modulo nine, so $G$ is 4-regular with eighteen edges. Rotation $i\mapsto i+1$ is an automorphism, so it suffices to show that the edges $\{0,1\}$ and $\{0,3\}$ conflict with every other edge.

An edge conflicts with an edge $e$ exactly when it has an endpoint in $N[e]$, the union of the closed neighbourhoods of the endpoints of $e$. Since $N[0]=\{0,1,3,6,8\}$, $N[1]=\{0,1,2,4,7\}$ and $N[3]=\{0,2,3,4,6\}$,

$$
N[\{0,1\}]=\mathbb{Z}_9\setminus\{5\},\qquad N[\{0,3\}]=\mathbb{Z}_9\setminus\{5,7\}.
$$

Every edge has an endpoint other than $5$, so it conflicts with $\{0,1\}$. An edge avoiding $\{0,1,2,3,4,6,8\}$ would be $\{5,7\}$, but $7-5=2$ is neither $\pm1$ nor $\pm3$, so $\{5,7\}$ is not an edge. Hence every edge conflicts with $\{0,3\}$. All eighteen edges therefore pairwise conflict, and an induced matching contains at most one of them: $\nu_s(G)=1$.

Edges in different components never conflict, so $\nu_s$ is additive over components. A disjoint union of $k$ copies thus has $m=18k$ and $\nu_s=k<m/17$. It has maximum degree four and no $C_5[2]$ component, so it contradicts the conjecture. ∎

A direct computation confirms the 153 conflicting pairs and $\nu_s=1$, and the proposition is formalized in Lean (Appendix A). Among all connected 4-regular graphs with at most thirteen vertices, $C_9(1,3)$ is the only one other than $C_5[2]$ whose strong clique number reaches eighteen.

## 3. An incidence inequality for strong cliques

**Lemma 3.1.** Let $F$ be a strong clique with $s=|F|$ edges and write $d(x)=d_F(x)$. Then

$$
\binom{s}{2}\leq\frac{3}{2}\sum_{x\in V(F)}d(x)^2. \tag{3.1}
$$

**Proof.** Two distinct edges share at most one endpoint, so exactly $\sum_x\binom{d(x)}{2}$ pairs of edges of $F$ share an endpoint. Every other pair $\{e,f\}$ is disjoint, and some edge $g=xy$ of $G$ has $x\in e$ and $y\in f$. Both endpoints of $g$ lie in $V(F)$, and $g\neq e,f$.

Let $W$ be the set of edges of $G[V(F)]$ outside $F$, and let $w(x)$ be the number of edges of $W$ at $x$. Since $\Delta(G)\leq4$, $w(x)+d(x)\leq4$. A fixed edge $g=xy$ witnesses at most $(d(x)-[g\in F])(d(y)-[g\in F])$ disjoint pairs: one edge of $F$ at $x$ and one at $y$, both different from $g$. Using $ab\leq(a^2+b^2)/2$, the number of disjoint pairs is at most

$$
\sum_{xy\in W}\frac{d(x)^2+d(y)^2}{2}+\sum_{xy\in F}\frac{(d(x)-1)^2+(d(y)-1)^2}{2}
=\sum_{x}\frac{w(x)d(x)^2+d(x)(d(x)-1)^2}{2}.
$$

Replace $w(x)$ by its upper bound $4-d(x)$ and add the pairs that share an endpoint. Since

$$
\binom{d}{2}+\frac{(4-d)d^2+d(d-1)^2}{2}=\frac{d^2-d+2d^2+d}{2}=\frac{3}{2}d^2,
$$

inequality (3.1) follows. ∎

**Corollary 3.2.** A strong clique with $s$ edges satisfies

$$
\frac{s}{2}\leq|V(F)|\leq\frac{s(31-s)}{12}. \tag{3.2}
$$

If $s=19$, then $10\leq|V(F)|\leq18$.

**Proof.** The lower bound holds because $\sum_xd(x)=2s$ and $d(x)\leq4$. Since $1\leq d(x)\leq4$, we have $(d(x)-1)(d(x)-4)\leq0$, that is, $d(x)^2\leq5d(x)-4$. Summing gives $\sum_xd(x)^2\leq10s-4|V(F)|$, and (3.1) yields $s(s-1)/2\leq\frac{3}{2}(10s-4|V(F)|)$. This rearranges to the upper bound in (3.2).

For $s=19$, (3.2) gives $9.5\leq|V(F)|\leq19$. Suppose $|V(F)|=19$. Then (3.1) and the summed estimate give $114\leq\sum_xd(x)^2\leq190-76=114$. So $d(x)^2=5d(x)-4$, that is $d(x)\in\{1,4\}$, for every $x$. If $a$ vertices have degree four, then $4a+(19-a)=38$, so $3a=19$, which is impossible. ∎

## 4. Reduction to finitely many configurations

Let $F$ be a strong clique with $|F|=19$, and let $H=G[V(F)]$. By the proof of Lemma 3.1, every conflict between two edges of $F$ is witnessed by an edge of $H$. Since $\Delta(H)\leq4$, the pair $(H,F)$ has the following properties:

1. $H$ is a graph on $n=|V(F)|$ vertices with $\Delta(H)\leq4$, and $10\leq n\leq18$;
2. $F\subseteq E(H)$, $|F|=19$, and every vertex of $H$ is an endpoint of $F$;
3. any two disjoint edges of $F$ are joined by an edge of $H$.

The pair is also closed under relabelling the vertices, and it satisfies (3.1).

**Lemma 4.1.** If $n=10$ and every vertex of $H$ has degree four in $H$, then $H$ is a connected component of $G$ isomorphic to $C_5[2]$, and $F\subseteq E(H)$.

**Proof.** No vertex of $H$ has a neighbour outside $V(F)$, because its four neighbours are already in $H$. Thus $H$ is a union of components of $G$, and it is 4-regular with twenty edges. The search of Section 5 (instance $R$) shows that all twenty edges of every such $H$ pairwise conflict. By the twenty-clique rigidity theorem [1, Theorem 6.4], formalized in Lean in [1], a twenty-edge strong clique is exactly the edge set of a component isomorphic to $C_5[2]$. ∎

Lemma 4.1 is also confirmed by an independent enumeration. There are 59 connected 4-regular graphs on ten vertices, a count that agrees with OEIS A006820 [9], and one disconnected one, $K_5\cup K_5$. In $K_5\cup K_5$ a strong clique lies inside one $K_5$ and has at most ten edges. Among the connected ones, only $C_5[2]$ has strong clique number at least nineteen.

## 5. The exhaustive search

### 5.1. Encoding

For $10\leq n\leq18$, the instance $I_n$ has a Boolean variable $a_{xy}$ ("$xy\in E(H)$") and a variable $f_{xy}$ ("$xy\in F$") for every pair $0\leq x<y<n$, together with the following clauses:

1. $f_{xy}\to a_{xy}$;
2. at most four of the $a_{xy}$ at each vertex $x$;
3. at least one of the $f_{xy}$ at each vertex $x$;
4. exactly nineteen of the $f_{xy}$;
5. $f_{xy}\wedge f_{zw}\to a_{xz}\vee a_{xw}\vee a_{yz}\vee a_{yw}$ for all disjoint pairs $\{x,y\},\{z,w\}$.

Three sound strengthenings are added:

- **Degree order.** Unary counters represent $d_F(x)$, and the instance requires $d_F(0)\geq d_F(1)\geq\cdots\geq d_F(n-1)$.
- **Lexicographic order.** For all $i<j$ with $d_F(i)=d_F(j)$, the vector $(f_{ic})_c$, taken over $c\notin\{i,j\}$ in increasing order, is lexicographically at most $(f_{jc})_c$. Here $f_{xy}$ denotes $f_{\min(x,y)\max(x,y)}$. This is the row-wise constraint of Codish, Miller, Prosser and Stuckey [11], restricted to vertices of equal $F$-degree.
- **Counting.** Inequality (3.1), in the form $\sum_x\sum_{k=1}^{4}(2k-1)[d_F(x)\geq k]\geq114$.

**Lemma 5.1.** Every pair $(H,F)$ satisfying properties 1–3 of Section 4 has a labelling of its vertices that satisfies both the degree order and the lexicographic order.

**Proof.** Among the labellings with non-increasing $F$-degrees, choose one whose $F$-adjacency matrix $A$ is least in the lexicographic order of its entries, read row by row and each row left to right. Suppose $i<j$, $d_F(i)=d_F(j)$, and the first column $c\notin\{i,j\}$ with $A_{ic}\neq A_{jc}$ has $A_{ic}=1$ and $A_{jc}=0$. Exchanging the labels $i$ and $j$ keeps the degrees non-increasing, so let $A'$ be the matrix after the exchange.

If $c<i$, then $A$ and $A'$ agree before row $c$. In row $c$ they agree before column $i$, and $A'_{ci}=A_{jc}=0<1=A_{ic}=A_{ci}$. If $c>i$, then $A$ and $A'$ agree in all rows before $i$. In row $i$ they agree before column $c$, because $A'_{ij}=A_{ji}=A_{ij}$, and $A'_{ic}=A_{jc}=0<A_{ic}$. In both cases $A'$ is smaller than $A$, contradicting the choice. ∎

For $n=10$ the instance $I_{10}$ adds the clause "some vertex has at most three of the $a_{xy}$". This excludes exactly the case of Lemma 4.1. The instance $R$ has ten vertices and requires instead:

- every vertex to have exactly four of the $a_{xy}$;
- nineteen edges of $F$ pairwise conflicting;
- the twentieth edge to fail to conflict with some edge of $F$.

Cardinality constraints use sequential counters from PySAT [10].

**Lemma 5.2.** If Theorem 1.2 fails, then some instance $I_n$ with $10\leq n\leq18$ is satisfiable.

**Proof.** Let $F$ be a strong clique with $|F|\geq19$ that does not lie in a $C_5[2]$ component.

First, choose a nineteen-edge subset $F_0\subseteq F$ that does not lie in a $C_5[2]$ component either. Suppose instead that every nineteen-edge subset of $F$ lies in such a component. Any two edges of $F$ lie together in some nineteen-edge subset, hence in a common component. So all edges of $F$ lie in one component $C\cong C_5[2]$, and $F\subseteq E(C)$, contrary to the choice of $F$.

Next, let $n=|V(F_0)|$, so $10\leq n\leq18$ by Corollary 3.2. Label $V(F_0)$ as $\{0,\dots,n-1\}$ as in Lemma 5.1, and set $a,f$ from $H=G[V(F_0)]$ and $F_0$. Clauses 1–5 hold by properties 1–3 of Section 4, the two order constraints by Lemma 5.1, and the counting constraint by Lemma 3.1. If $n=10$, Lemma 4.1 provides a vertex of $H$-degree at most three, because $F_0$ is not contained in a $C_5[2]$ component. ∎

### 5.2. Controls

Before the main instances, the same encoder was run on cases with known answers:

| Instance | Expected | Result |
| --- | --- | --- |
| $n=10$, $s=20$ (no exclusion) | SAT, $C_5[2]$ | SAT |
| $n=10$, $s=19$ (no exclusion) | SAT, subsets of $C_5[2]$ | SAT |
| $n=9$, $s=18$ | SAT, $C_9(1,3)$ | SAT |
| $n=10$, $s=21$ | UNSAT by [1, Theorem 6.4] | UNSAT |
| $n=10$, $s=20$, with exclusion | UNSAT by [1, Theorem 6.4] | UNSAT |
| $R$ with $s=17$ in place of $19$ | SAT, a 4-regular graph with a seventeen-edge clique | SAT |

The first five controls return the expected answer both with and without the three strengthenings, and every control returns it under both solvers.

### 5.3. Results

| Instance | Vertices | Clauses | CaDiCaL | Glucose | Result |
| --- | --- | --- | --- | --- | --- |
| $I_{10}$ (with exclusion) | 10 | 18004 | 0.5 s | 0.3 s | UNSAT |
| $I_{11}$ | 11 | 23762 | 1.1 s | 1.0 s | UNSAT |
| $I_{12}$ | 12 | 30367 | 2.8 s | 3.0 s | UNSAT |
| $I_{13}$ | 13 | 37476 | 5.4 s | 6.6 s | UNSAT |
| $I_{14}$ | 14 | 45140 | 10.8 s | 15.4 s | UNSAT |
| $I_{15}$ | 15 | 53413 | 20.9 s | 25.1 s | UNSAT |
| $I_{16}$ | 16 | 62352 | 32.4 s | 42.7 s | UNSAT |
| $I_{17}$ | 17 | 72017 | 41.0 s | 57.4 s | UNSAT |
| $I_{18}$ | 18 | 82471 | 59.5 s | 83.9 s | UNSAT |
| $I_{19}$ (cross-check) | 19 | 93780 | 78.7 s | 95.5 s | UNSAT |
| $I_{20}$ (cross-check) | 20 | 106013 | 95.6 s | 118.6 s | UNSAT |
| $R$ | 10 | 12283 | 85.4 s | 101.8 s | UNSAT |

Times are solve times on one 24-thread Windows workstation, with sixteen instances running in parallel.

All instances are unsatisfiable under both CaDiCaL 1.5.3 and Glucose 4 through PySAT 1.9.dev17 [10]. The solvers share no search code. The instances $I_{19}$ and $I_{20}$ are covered by Corollary 3.2, and their UNSAT results are recorded only as a cross-check.

## 6. Proof of the clique theorem

**Proof of Theorem 1.2.** By Lemma 5.2 and the unsatisfiability of every $I_n$ (Section 5.3), every strong clique with at least nineteen edges lies inside a component isomorphic to $C_5[2]$. ∎

**Proof of Corollary 1.3.** Without $C_5[2]$ components, Theorem 1.2 leaves no strong clique with nineteen or more edges. Proposition 1.1 gives eighteen for $C_9(1,3)$. ∎

## 7. The eighteen bound for prescribed edge sets

**Proof of Theorem 1.5(1).** Let $F=E(G)$. A $C_5[2]$ component has all twenty edges in $F$, so $\tau_G(E(G))=2n_5(G)$. The handshake bound gives $m(G)\leq2(n(G)-i(G))$, and (1.2) then gives

$$
18\nu_s(G)\geq2(n(G)-i(G))-2n_5(G)\geq m(G)-\tau_G(E(G)).
$$

∎

**Proof of Theorem 1.5(2).** If $\nu_s^G(F)=0$, then $F$ is empty. Otherwise $\nu_s^G(F)=1$, so $F$ is a strong clique. If $|F|\leq18$, the bound holds. If $|F|\geq19$, Theorem 1.2 places $F$ inside one $C_5[2]$ component $C$. Then $\tau_G(F)=|F|-18$, and $|F|=18+\tau_G(F)$.

For sharpness, $C_9(1,3)$ with $F=E(G)$ has $|F|=18=18\nu_s$ and $\tau=0$. Nineteen or twenty edges of a $C_5[2]$ component give $|F|=18+\tau$ with $\nu_s=1$. Both sides of (1.4) are additive over disjoint unions. ∎

**Proof of Proposition 1.6.** Let $C$ be a $C_5[2]$ component. If $|F\cap E(C)|=19$, then $C$ contributes one to $\tau_G(F)$ and nothing to $t_G(F)$. If $|F\cap E(C)|=20$, it contributes two and one, respectively. Otherwise it contributes nothing to either. Hence $\tau_G(F)-t_G(F)$ is the number of components $C$ with $|F\cap E(C)|\geq19$. Choosing one edge of $F$ in each such component gives an induced matching, so $\tau_G(F)-t_G(F)\leq\nu_s^G(F)$. Therefore $18\nu_s^G(F)+\tau_G(F)\leq19\nu_s^G(F)+t_G(F)$. ∎

**Remarks.** The cases proved here are those in which $F$ is either the whole edge set or a single strong clique. The first open case is $\nu_s^G(F)=2$, where (1.4) asks for $|F|\leq36$ outside $C_5[2]$ components. The method of Sections 3–5 does not extend directly: an edge set without three pairwise non-conflicting edges need not have a small endpoint set. The examples of Theorem 1.5 are all disjoint unions of strong cliques. We do not know a connected example with $\nu_s^G(F)\geq2$ attaining (1.4). The circulant $C_9(1,3)$ is itself a connected graph with $\nu_s(G)<m(G)/17$. We do not know a connected one with $\nu_s(G)\geq2$, that is, whether the conjecture already fails for connected graphs with larger induced matching number.

## Appendix A. Verification status and scope

**Paper proofs.** Proposition 1.1, Lemma 3.1, Corollary 3.2, the reduction in Section 4, Lemmas 5.1 and 5.2, Theorem 1.5 and Proposition 1.6 are proved in this manuscript. Lemma 4.1 also uses the Lean-formalized twenty-clique rigidity theorem [1, Theorem 6.4].

**Finite computations.** The finite computations are listed below. Instructions, logs and machine-readable results are in [the Route C guide](../README.md).

- The instances $I_{10},\dots,I_{18}$ and $R$ of Section 5. Each is unsatisfiable under two independent SAT solvers; $I_{19}$ and $I_{20}$ were added as cross-checks.
- The controls of Section 5.2.
- The conflict check and induced matching number of $C_9(1,3)$.
- The strong clique numbers of all connected 4-regular graphs with at most thirteen vertices. They are computed from the graph lists in the Route C data directory, which the enumeration script regenerates; their counts agree with OEIS A006820.

**Lean formalization.** Proposition 1.1 is formalized in the [Route C Lean package](../lean/README.md), on top of the pinned 19.5 definitions of conflict, induced matching and $C_5[2]$ component. The formalization covers the following facts:

- $C_9(1,3)$ is 4-regular with eighteen edges;
- its edges pairwise conflict;
- every induced matching has at most one edge;
- it has no $C_5[2]$ component;
- $17|M|<m$ for every induced matching $M$;
- $m=18\nu_s$.

Finite facts use kernel-checked `decide`. The axiom audit of all twelve declarations reports only `propext`, `Classical.choice` and `Quot.sound` ([record](../lean/verification/results.json)).

**Not established.**

- The SAT results are not accompanied by DRAT or LRAT certificates, and Theorem 1.2 and its consequences are not formalized in Lean.
- The search depends on the correctness of the encoder; that is why the controls are reported.
- Conjecture 1.4 remains open for $\nu_s^G(F)\geq2$ and $F\neq E(G)$.
- We found no earlier statement of Proposition 1.1 or Theorem 1.2. Our literature search used arXiv:1407.8336v1, which is the only arXiv version, and general web searches. We could not access the journal version [8], so we do not know whether Joos's conjecture appears there.

## AI assistance and verification

This research was conducted predominantly with generative AI, under the direction of **Congyue Mao**. Claude Opus 5.5 (Anthropic), working through Claude Code, carried out the mathematical exploration, the search programs and the manuscript preparation. The SAT computations were run with two independent solvers, and the hand proofs were checked against the computations where they overlap. These checks are not external human peer review.

## References

[1] C. Mao, *A Corrected 19.5 Bound for Induced Matchings in Prescribed Edge Sets*. Proof manuscript and verified Lean development, 10 October 2026. [Source and manuscript](https://github.com/congyuemao/strong-edge-packing-195/tree/2e91b05b25a4ee931a0490fefcdbb4f253be95c8).

[2] C. Mao, *A Corrected Nineteen Bound for Induced Matchings in Prescribed Edge Sets*. Proof manuscript and verified Lean development, 11 October 2026. [Manuscript](../../route-b/manuscript/packing19.md).

[3] P. Erdős, Problems and results in combinatorial analysis and graph theory, *Discrete Mathematics* 72 (1988), 81–92.

[4] M. Huang, M. Santana and G. Yu, Strong chromatic index of graphs with maximum degree four, *Electronic Journal of Combinatorics* 25(3) (2018), P3.31. [arXiv:1806.07012](https://arxiv.org/abs/1806.07012).

[5] F. R. K. Chung, A. Gyárfás, Z. Tuza and W. T. Trotter, The maximum number of edges in $2K_2$-free graphs of bounded degree, *Discrete Mathematics* 81 (1990), 129–135.

[6] F. Joos, *Induced matchings in graphs of maximum degree 4*, [arXiv:1407.8336v1](https://arxiv.org/abs/1407.8336) (2014).

[7] V. H. Nguyen, *Induced matchings in graphs of degree at most 4*, [arXiv:1407.7604](https://arxiv.org/abs/1407.7604) (2014).

[8] F. Joos and V. H. Nguyen, Induced matchings in graphs of degree at most 4, *SIAM Journal on Discrete Mathematics* 30 (2016), no. 1, 154–165. [DOI 10.1137/140986980](https://doi.org/10.1137/140986980).

[9] The On-Line Encyclopedia of Integer Sequences, [A006820](https://oeis.org/A006820): number of connected 4-regular simple graphs on $n$ vertices.

[10] A. Ignatiev, A. Morgado and J. Marques-Silva, PySAT: a Python toolkit for prototyping with SAT oracles, in *Theory and Applications of Satisfiability Testing – SAT 2018*, Lecture Notes in Computer Science 10929 (2018), 428–437.

[11] M. Codish, A. Miller, P. Prosser and P. J. Stuckey, Constraints for symmetry breaking in graph representation, *Constraints* 24 (2019), 1–24.
