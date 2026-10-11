# Start here

[Repository overview](../README.md) · [Proof guide](PROOF_GUIDE.md) · [Verification](VERIFICATION.md)

## The question

Given a collection of candidate edges in a graph, how large an induced matching must it contain? The repository addresses finite simple graphs $G$ with maximum degree at most four and arbitrary prescribed sets $F\subseteq E(G)$. Choosing candidates changes which edges may enter the matching. It does not change the graph in which the induced-matching condition is evaluated.

This distinction matters even for a three-edge path $a-b-c-d$. If only $ab$ and $cd$ are candidates, they still conflict through the original middle edge $bc$. They cannot both be chosen. Deleting $bc$ before checking conflicts would answer a different question.

## Definitions and result

Two distinct original edges have a **strong conflict** if they share an endpoint or an original edge joins one endpoint of each. An **induced matching relative to $G$** is a collection of edges with no such conflict between any pair. Its endpoints therefore induce exactly those disjoint edges in $G$.

The **candidate set** $F$ specifies the eligible edges. Write $\nu_s^G(F)$ for the maximum size of an induced matching of the original graph contained in $F$. Equivalently, first form the full conflict graph $L(G)^2$, then take its induced subgraph on the vertex set $F$ and its independence number.

The exceptional graph $C_5[2]$ consists of five independent vertex pairs arranged around a cycle, with all four possible edges between consecutive pairs and no other edges. It has ten vertices and twenty edges. The **original-component correction** $t_G(F)$ counts the connected components of $G$ of this form for which all twenty edges belong to $F$. It does not count partially selected components, candidate-subgraph components, or different labellings of the same component.

The [main theorem, Theorem 1.1](../route-b/manuscript/packing19.md#1-statement-and-conventions), states

$$
|F|\le 19\nu_s^G(F)+t_G(F).
$$

More explicitly, the proof produces an induced matching $M\subseteq F$ with $|F|\le19|M|+t_G(F)$. This holds for every candidate set and every matching number; connectivity, planarity, and triangle-freeness are not hypotheses.

## Why nineteen is sharp

Take $G=C_5[2]$ and choose any nineteen of its twenty edges. The full conflict graph is $K_{20}$, so $\nu_s^G(F)=1$. Since the component is not fully selected, $t_G(F)=0$. Thus equality holds with $|F|=19$, and the coefficient cannot be decreased.

Selecting all twenty edges instead gives matching number one and correction one. This explains why the correction is necessary and why positive-deficit arguments first exclude wholly selected exceptional components. The [sharpness discussion](../route-b/manuscript/packing19.md#83-sharpness-and-the-original-critical-examples) is a paper argument with finite regression examples; there is no separate Lean sharpness theorem in this extension.

## A reading path

1. Read the [complete PDF](../route-b/manuscript/packing19.pdf), beginning with the statement and conventions. The [Markdown manuscript](../route-b/manuscript/packing19.md) provides section links and editable source.
2. Use the [proof guide](PROOF_GUIDE.md) to follow the main dependencies, especially the boundary between the critical-degree analysis and original-graph clique extension.
3. Inspect the upstream [conflict definitions](../upstream/packing195/lean/StrongEdge/Basic.lean), [induced-matching definition](../upstream/packing195/lean/StrongEdge/Conflict.lean), and [component count](../upstream/packing195/lean/StrongEdge/TightComponents.lean), with the [formalisation guide](FORMALIZATION.md) alongside them.
4. Open [Main.lean](../route-b/lean/StrongEdge19/Main.lean), ending at `StrongEdge19.prescribed_edge_bound19`. Appendix A of the manuscript supplies the full paper-to-Lean concordance.
5. Read the [independent audit](../route-b/audit-2026-10-11/REPORT.md) and the [verification guide](VERIFICATION.md) for its precise snapshot, evidence, and trust boundary.

## Current proof and preserved research

The consolidated manuscript and current Lean extension are the final argument. The Stage 1–3 notes preserve the development sequence, including earlier small-matching-number investigations that the final general proof does not require. The [chronological index](RESEARCH_HISTORY.md) identifies final dependencies, historical experiments, documentation, and verification evidence without replacing those records.

This is an AI-assisted project. The existing [disclosure](../route-b/manuscript/packing19.md#ai-assistance-and-verification) describes predominantly generative-AI research under Congyue Mao's direction. Formal checking, finite experiments, and automated audit are distinct from external human peer review. Mathematical originality and suitability for publication remain subject to specialist review; the [literature orientation](RELATED_WORK.md) is a starting point for that work.
