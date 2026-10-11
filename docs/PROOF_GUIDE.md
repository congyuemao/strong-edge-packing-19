# Guide to the proof

[Repository overview](../README.md) · [Start here](START_HERE.md) · [Formalisation](FORMALIZATION.md)

This roadmap follows the [consolidated manuscript](../route-b/manuscript/packing19.md). Let $\widehat H=L(G)^2$ be the full original conflict graph and $H=\widehat H[F]$ its candidate restriction. Write $c(e)$ for full conflict degree and $d(e)$ for candidate degree. All graphs below are finite and simple, with $\Delta(G)\le4$.

## 1. Use the pinned foundation

[Paper Section 2](../route-b/manuscript/packing19.md#2-the-verified-foundation-and-elementary-cover-identities) states the structural results supplied by the corrected 19.5 project, pinned at `2e91b05b25a4ee931a0490fefcdbb4f253be95c8`. Its [threshold interface](../upstream/packing195/lean/StrongEdge/Packing195Thresholds.lean), [local-39 argument](../upstream/packing195/lean/StrongEdge/MinimalPacking195.lean), and [twenty-clique rigidity](../upstream/packing195/lean/StrongEdge/Bounds/TwentyCliqueRigidity.lean) provide the starting estimates and identify twenty-cliques with whole original $C_5[2]$ components.

The full-degree thresholds 20, 21, 22, 23, and 24 give clique-size bounds 18, 17, 16, 15, and **13**, respectively. The last value is essential: the weaker value fourteen sufficient for the abstract local-39 interface would not give the later zero-deficit exclusion. The selected-subcubic bound in [SubcubicSeventeen.lean](../upstream/packing195/lean/StrongEdge/Bounds/SubcubicSeventeen.lean) supplies a four-selected-edge root when a clique is large enough.

## 2. Count compensation exactly

For a maximum independent set $M$ in $H$, let $P_e$ be the candidates whose closed neighbourhood meets $M$ exactly at $e$, and let $m(x)=|N_H[x]\cap M|$. Put $\delta(e)=39-(d(e)+1+|P_e|)$ and $R=\sum_{x\in F}\max\{m(x)-2,0\}$. [Paper Section 3.2](../route-b/manuscript/packing19.md#32-the-exact-identity) gives

$$
2|F|=39|M|-\sum_{e\in M}\delta(e)-R.
$$

[`StrongEdge19.compensation_identity`](../route-b/lean/StrongEdge19/Compensation.lean) is the formal identity. Deficits are integers: a fully selected exceptional component can have deficit minus one. This identity alone does not assert nonnegative deficits or exclude exceptional components. Lean assumes a maximum independent set; the paper's observation that maximality suffices for this count is not a separate formalised strengthening.

## 3. Normalise a critical centre

[Paper Sections 3.1 and 3.3](../route-b/manuscript/packing19.md#3-exact-compensation-and-critical-normalization) choose a maximum independent set, then minimise its candidate-degree sum, then its full-degree sum. Existence is proved by finite minimisation in [`tertiary_optimal_exists`](../route-b/lean/StrongEdge19/Tertiary.lean).

Private-set exchanges and the foundation's thresholds yield a full-degree witness. [`zero_deficit_full_degree_and_closed_neighborhood`](../route-b/lean/StrongEdge19/CriticalNormalization.lean) derives $c(e)=d(e)$ and full closed-neighbourhood containment in $F$ for a tertiary-optimal zero-deficit centre. These facts are used internally by the high-degree exclusions.

## 4. Exclude critical degrees 20 through 24

[Paper Section 5](../route-b/manuscript/packing19.md#5-stage-2-the-candidate-degree-interface), together with Lemma 3.3, leads to [`zero_deficit_candidate_degree_eq_nineteen`](../route-b/lean/StrongEdge19/CriticalHighDegree.lean). Degree 24 is already excluded by the upstream thirteen bound. The extension improves the threshold-20 clique bound to seventeen. For degrees 21–23, normalisation and the [private subcubic lemma](../route-b/lean/StrongEdge19/PrivateSubcubic.lean) supply a four-selected-edge root before the stronger root bounds are applied.

The exported Stage 2 conclusion is only $d(e)=19$. It requires tertiary optimality but neither a no-selected-twenty-clique hypothesis nor Stage 3's nineteen-clique extension. See the [manuscript's dependency boundary](../route-b/manuscript/packing19.md#a3-the-optimized-dependency-boundary).

## 5. Extend a clique in the original graph

[Paper Section 6, Theorem 6.1](../route-b/manuscript/packing19.md#6-stage-3-nineteen-clique-rigidity-through-a-closed-support) treats an arbitrary nineteen-edge strong clique $Q$ whose members all have **full conflict degree at least nineteen**. A nineteen-clique alone would only force degree at least eighteen.

[`high19_large_clique_closed_ten_support`](../route-b/lean/StrongEdge19/ClosedCore.lean) finds a closed original support on at most ten vertices. [`high19_nineteen_clique_extends_to_twenty`](../route-b/lean/StrongEdge19/NineteenRigidity.lean) then extends $Q$ to an original twenty-clique $T$. **The twentieth edge is not assumed selected, and this theorem does not conclude $T\subseteq F$.** Upstream twenty-clique rigidity identifies the component; it does not depend on the new nineteen-packing theorem.

## 6. Recover selection and eliminate zero deficit

[Paper Section 7.1](../route-b/manuscript/packing19.md#71-degree-nineteen-requires-only-secondary-optimization) applies that extension to the private nineteen-clique of a zero-deficit centre with $d(e)=19$. Upstream conflict closure bounds $c(e)$ by nineteen. Equality with candidate degree makes every full neighbour a candidate, so $T\subseteq F$.

[`critical_degree_nineteen_forces_selected_twenty`](../route-b/lean/StrongEdge19/CriticalNineteen.lean) needs only secondary optimality. It recovers full-degree equality after rigidity rather than taking the stronger normalisation conclusion as an input. [`zero_deficit_impossible`](../route-b/lean/StrongEdge19/PositiveDeficits.lean) combines this with Stage 2 under the no-selected-twenty-clique hypothesis.

## 7. Obtain the bound and restore components

[Paper Section 7.2](../route-b/manuscript/packing19.md#72-positive-deficits) uses the upstream local estimate to establish nonnegative deficits when no twenty-clique is wholly selected. Excluding zero makes every integer deficit at least one. [`global_compensation_of_no_twenty_clique`](../route-b/lean/StrongEdge19/PositiveDeficits.lean) and [Packing.lean](../route-b/lean/StrongEdge19/Packing.lean) give $|F|\le19|M|$ for arbitrary matching number.

[Paper Sections 8.1–8.2](../route-b/manuscript/packing19.md#8-restoring-exceptional-components-and-sharpness) and [Main.lean](../route-b/lean/StrongEdge19/Main.lean) remove a selected twenty-clique from **$F$, keeping $G$ fixed**, apply induction, and restore it. Full-conflict closure permits adding one matching edge. The twenty restored candidates cost nineteen units from that edge and one component-correction unit. The literal original-component count yields `StrongEdge19.prescribed_edge_bound19`.

## 8. Locate sharpness and scope limits

[Paper Section 8.3](../route-b/manuscript/packing19.md#83-sharpness-and-the-original-critical-examples) takes nineteen of the twenty edges of $C_5[2]$: $\nu_s^G(F)=1$ and $t_G(F)=0$. This establishes sharpness on paper and has finite regression examples, but no separately declared Lean sharpness theorem. The universal upper bound is formalised. The development does not separately formalise every historical small-matching-number exchange or intermediate prose observation; consult the [verification guide](VERIFICATION.md) for the exact evidence scope.
