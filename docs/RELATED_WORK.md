# Related work and questions for specialist review

[Repository overview](../README.md) · [Start here](START_HERE.md) · [Research history](RESEARCH_HISTORY.md)

This page is a limited literature orientation, **not a comprehensive novelty search**. The source records and papers linked below support the stated bibliographic details and comparisons. The project's originality, relationship to other results, and significance for publication require specialist confirmation. No claim is made that this selection exhausts the literature or identifies the latest best bound in each setting.

## Three different questions

| Setting | Quantity being bounded | Point to check when comparing results |
| --- | --- | --- |
| Whole-edge-set induced matching | The largest induced matching in all of $E(G)$ | There is no prescribed candidate set. Applying such a theorem after deleting edges can change the original conflicts. |
| Prescribed-edge induced matching | $\nu_s^G(F)$ for every $F\subseteq E(G)$ | Conflicts are measured in the full original graph, including edges outside $F$. The corrected nineteen bound is stated below. |
| Strong edge colouring | A partition of all original edges into induced matchings | A colouring controls all colour classes simultaneously. A bound on one large induced matching is not itself an integer colouring theorem. |

Here $G$ is finite and simple with maximum degree at most four. The repository proves $|F|\le19\nu_s^G(F)+t_G(F)$. Its correction $t_G(F)$ counts original $C_5[2]$ connected components whose entire twenty-edge sets are selected, once per component. See the [statement and definitions](START_HERE.md#definitions-and-result).

The following comparison is a direct mathematical deduction, rather than a claim of equivalence between the cited theorems: if a strong edge colouring of the **original** graph uses at most $k$ colours, intersect its colour classes with $F$. These intersections partition $F$ into at most $k$ induced matchings of $G$, so one has size at least $|F|/k$. Thus $|F|\le k\nu_s^G(F)$ on that colouring theorem's graph class. A coefficient 21 does not by itself give the corrected coefficient 19; a coefficient 19 valid only for a restricted class does not cover every graph of maximum degree four.

## Whole-edge-set bounds

Felix Joos and Viet Hang Nguyen, *Induced Matchings in Graphs of Degree at Most 4*, prove a sharp $n(G)/9$ lower bound for induced matchings when the graph has maximum degree at most four, has no isolated vertices, and excludes the specified blown-up five-cycle as a component. The publisher also states edge-count consequences. This concerns the whole graph, and does not directly settle the arbitrary prescribed-edge problem with original conflicts retained. [SIAM paper, DOI 10.1137/140986980](https://epubs.siam.org/doi/10.1137/140986980).

In particular, applying a whole-edge-set theorem to the spanning graph with edge set $F$ can discard an outside-candidate edge that witnesses a conflict. The [three-edge path](START_HERE.md#the-question) already shows why that substitution is insufficient.

## General and restricted colouring results

Mingfang Huang, Michael Santana, and Gexin Yu, *Strong chromatic index of graphs with maximum degree four*, give an upper bound of 21 colours in their 2018 paper. The original-graph colour-class argument above consequently gives a prescribed-edge coefficient 21. This citation is a comparison point, not a statement about the current best known colouring bound. [Authors' arXiv record, 1806.07012](https://arxiv.org/abs/1806.07012).

Ying Wang, Wai Chee Shiu, Weifan Wang, and Min Chen, *Planar graphs with maximum degree 4 are strongly 19-edge-colorable*, **Discrete Mathematics 341(6)** (2018), 1629–1635, establish a 19-colour bound under **planarity**. The same colour-class deduction applies to prescribed sets in those original planar graphs; it does not remove the planarity assumption. [Publisher record, DOI 10.1016/j.disc.2018.02.025](https://www.sciencedirect.com/science/article/pii/S0012365X18300645).

Jian-Bo Lv, Xiangwen Li, and Gexin Yu, *On strong edge-coloring of graphs with maximum degree 4*, **Discrete Applied Mathematics 235** (2018), 142–153, study additional maximum-average-degree restrictions. For example, their bound of 19 colours assumes $\operatorname{mad}(G)<15/4$, where maximum average degree is the largest average degree of a nonempty subgraph. This is a sparsity condition beyond maximum degree four. [Publisher record](https://www.sciencedirect.com/science/article/pii/S0166218X17304183) and [author-hosted paper](https://gyu.people.wm.edu/DA-6319-R2.pdf).

## The project's foundation and remaining review

The direct formal dependency is the repository's [corrected 19.5 foundation](../upstream/packing195/manuscript/packing195.md), pinned at `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`. The [proof guide](PROOF_GUIDE.md) identifies which earlier structural results are used and where the nineteen-bound extension begins. This provenance is not evidence of priority over all external literature.

A specialist comparison should check the exact candidate-set quantifiers, original-graph conflict convention, exceptional-component correction, graph-class hypotheses, and any weighted or fractional variants. The [recorded audit](../route-b/audit-2026-10-11/REPORT.md) addresses the stated proof snapshot and trust boundary, not a complete bibliographic review or independent certification of originality.
