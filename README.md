# A corrected nineteen bound for induced matchings

This repository contains a public mathematical manuscript, a Lean-formalised theorem, and recorded verification and audit evidence for induced-matching packing in graphs of maximum degree four. The complete argument is available as an English paper and as a formal development extending the pinned 19.5 foundation. Journal publication, external human peer review, and independently certified originality are not claimed.

## Main theorem

Let $G$ be a finite simple graph of maximum degree at most four, and let $F\subseteq E(G)$ be **any prescribed edge subset**. Then

$$
|F|\le 19\nu_s^G(F)+t_G(F).
$$

Here $\nu_s^G(F)$ is the largest size of an induced matching of $G$ contained in $F$. All strong conflicts are evaluated in the **full original graph**: an edge outside $F$ can still join endpoints of two selected edges and prevent them from belonging to the same induced matching.

The correction $t_G(F)$ counts actual original connected components isomorphic to $C_5[2]$ whose full twenty-edge sets lie in $F$. The graph $C_5[2]$ replaces each vertex of a five-cycle by an independent pair, with all four edges between consecutive pairs. The correction counts components once, regardless of their labellings. No connectivity assumption or restriction on the matching number is imposed.

## Read the result

| Reader goal | Destination |
| --- | --- |
| Read the complete paper | [PDF manuscript](route-b/manuscript/packing19.pdf) |
| Read editable mathematical source | [English manuscript](route-b/manuscript/packing19.md) |
| Inspect the final Lean theorem | [Main.lean: StrongEdge19.prescribed_edge_bound19](route-b/lean/StrongEdge19/Main.lean) |
| Read the independent audit report | [Snapshot-specific report](route-b/audit-2026-10-11/REPORT.md) |
| See verification details | [Evidence, limitations, and reproduction](docs/VERIFICATION.md) |
| Start with an accessible overview | [Start here](docs/START_HERE.md) |

## Proof at a glance

The pinned 19.5 foundation supplies clique and degree estimates, while an exact compensation identity reduces the improvement to positive integer deficits. Tertiary optimisation and critical-degree analysis establish candidate degree nineteen for a zero-deficit centre; a separate original-graph rigidity theorem extends the resulting nineteen-clique to a twenty-clique, after which candidate membership of the twentieth edge is proved. Excluding wholly selected twenty-cliques therefore gives positive deficits and global compensation; restoring each exceptional component adds twenty candidates, one matching edge, and one correction unit, with the original graph fixed throughout.

The [proof guide](docs/PROOF_GUIDE.md) traces these steps to the paper and Lean sources. The [formalisation guide](docs/FORMALIZATION.md) explains the definitions and theorem interfaces without duplicating the manuscript's declaration concordance.

## Verification status and limitations

The independent audit reports successful recompilation of **104/104 project modules** and inspection of **1,521 project-origin declarations**, including private and generated declarations. Its transitive axiom union is `propext`, `Classical.choice`, and `Quot.sound`. Previously compiled mathlib and other library artifacts were reused; this was not a clean rebuild of the entire dependency graph.

The audit examined commit `028f4d3541ad41a558b3d1f5c8fd962046ea24dd`. Its supported conclusion is that no error was found within the documented scope. Later PDF publication and this navigation layer are outside that snapshot. Automated checks and the recorded audit do not constitute external human refereeing. Finite regression families and manuscript checks have separate, narrower scopes, detailed in the [verification guide](docs/VERIFICATION.md).

## Reproduction and research history

Follow the [reproduction instructions](docs/VERIFICATION.md#reproducing-checks-without-replacing-evidence), including their snapshot and local-path requirements. The `strong-edge-packing-195` submodule remains pinned to `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`. The [research history](docs/RESEARCH_HISTORY.md) indexes the preserved stage notes, experiments, proof versions, and audit records. The [related-work guide](docs/RELATED_WORK.md) distinguishes the prescribed-edge question from whole-edge-set and colouring results; specialist assessment of originality remains necessary.

## AI assistance

The manuscript's [AI-assistance disclosure](route-b/manuscript/packing19.md#ai-assistance-and-verification) states that the research was conducted predominantly using generative AI, including mathematical exploration, proof development, Lean formalisation, and manuscript preparation, under Congyue Mao's direction. Lean checks the formal proof terms; the English exposition and PDF were reviewed separately. This disclosure does not imply endorsement by an independent human mathematician.
