"""Check Stage 3 root templates and sharp compensation examples.

This finite check is not a proof for arbitrary original graphs. The exact
scope is recorded in the output. All conflicts use complete original graphs,
including the original core edges not selected as candidates.
Only the Python standard library is required.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import platform
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

from check_stage2 import adjacency, conflict, correction_count, edge, exact_matching


LABELS = frozenset(range(1, 5))
DOUBLE_TYPES = tuple(frozenset(s) for s in itertools.combinations(LABELS, 2))
TRIPLE_TYPES = tuple(frozenset(s) for s in itertools.combinations(LABELS, 3))
ROOT_EDGES = frozenset(edge(0, label) for label in LABELS)


def complete_with_branches(core):
    """Saturate core degrees with separate neighbours of degree four.

    Fresh branch leaves have degree one. No selected edge has a fresh
    endpoint, so these extensions never create new conflicts between the
    selected core edges. They remain available for full conflict degrees.
    """
    result = set(core)
    adj = adjacency(core)
    fresh = max(adj, default=-1) + 1
    for vertex in sorted(adj):
        for _ in range(4 - len(adj[vertex])):
            branch = fresh
            result.add(edge(vertex, branch))
            result.update(edge(branch, branch + offset) for offset in (1, 2, 3))
            fresh += 4
    completed = adjacency(result)
    assert all(len(completed[v]) == 4 for v in adj)
    return result


def full_degrees(original, candidates):
    adj = adjacency(original)
    return {e: sum(conflict(e, f, adj) for f in original) for e in candidates}


def type_incidence(types):
    return Counter(label for part in types for label in part)


def type_core(types):
    return set(ROOT_EDGES) | {
        edge(5 + index, label)
        for index, part in enumerate(types)
        for label in part
    }


def check_triangle_roots():
    """Exactly one internal label edge; all double multisets fit its slots.

    We add no original tip-to-tip edges here. The check verifies the
    triangle-label load restriction in these explicitly completed original
    graphs, rather than enumerating every possible triangle-root graph.
    """
    checked = 0
    high_roots = 0
    maximum_outer_capacity = 0
    for inside in itertools.combinations(sorted(LABELS), 2):
        capacity = {label: 3 - (label in inside) for label in LABELS}
        for count in range(6):
            for types in itertools.combinations_with_replacement(DOUBLE_TYPES, count):
                incidences = type_incidence(types)
                if any(incidences[label] > capacity[label] for label in LABELS):
                    continue
                original = complete_with_branches(type_core(types) | {edge(*inside)})
                checked += 1
                degrees = full_degrees(original, ROOT_EDGES)
                if min(degrees.values()) < 19:
                    continue
                high_roots += 1
                for label in inside:
                    assert incidences[label] <= 1
                # Every permissible outer edge must cover all four labels.
                pairs = [(i, j) for i, j in itertools.combinations(range(count), 2)
                         if types[i] | types[j] == LABELS]
                a = inside[0]
                holders = [i for i, part in enumerate(types) if a in part]
                assert len(holders) <= 1
                assert all(any(i in pair for i in holders) for pair in pairs)
                # That unique double has only two original slots outside A.
                outer_capacity = min(2, len(pairs)) if holders else 0
                maximum_outer_capacity = max(maximum_outer_capacity, outer_capacity)
                assert outer_capacity <= 2
    return {
        "scope": "One internal label edge, every capacity-feasible multiset of "
                 "zero through five double tips, and separate branch completion; "
                 "no additional original tip-to-tip edges in this check.",
        "original_graphs_checked": checked,
        "graphs_with_all_four_root_full_degrees_at_least_19": high_roots,
        "maximum_permitted_outer_capacity_in_high_root_cases": maximum_outer_capacity,
    }


def saturated_type_families():
    for doubles in itertools.combinations_with_replacement(DOUBLE_TYPES, 4):
        types = (LABELS,) + doubles
        if all(type_incidence(types)[a] == 3 for a in LABELS):
            yield "one_quadruple_four_doubles", types
    for triples in itertools.combinations_with_replacement(TRIPLE_TYPES, 2):
        for doubles in itertools.combinations_with_replacement(DOUBLE_TYPES, 3):
            types = triples + doubles
            if all(type_incidence(types)[a] == 3 for a in LABELS):
                yield "two_triples_three_doubles", types


def possible_tip_graphs(types):
    possible = list(itertools.combinations(range(len(types)), 2))
    capacity = [4 - len(part) for part in types]
    for mask in range(1 << len(possible)):
        if mask.bit_count() < 3:
            continue
        selected = [pair for i, pair in enumerate(possible) if mask >> i & 1]
        degrees = Counter(i for pair in selected for i in pair)
        if all(degrees[i] <= capacity[i] for i in range(len(types))):
            yield {edge(5 + i, 5 + j) for i, j in selected}


def check_saturated_families():
    count_keys = ("type_multisets", "original_core_graphs", "candidate_sets",
                  "nineteen_cliques", "high_nineteen_cliques")
    counts = Counter(dict.fromkeys(count_keys, 0))
    by_family = {}
    passing = []
    for family, types in saturated_type_families():
        family_counts = by_family.setdefault(family, Counter(dict.fromkeys(count_keys, 0)))
        counts["type_multisets"] += 1
        family_counts["type_multisets"] += 1
        for tip_edges in possible_tip_graphs(types):
            core = type_core(types) | tip_edges
            assert 19 <= len(core) <= 20
            original = complete_with_branches(core)
            adj = adjacency(original)
            counts["original_core_graphs"] += 1
            family_counts["original_core_graphs"] += 1
            optional = sorted(core - ROOT_EDGES)
            degrees = full_degrees(original, core)
            for extra in itertools.combinations(optional, 15):
                candidates = set(ROOT_EDGES) | set(extra)
                assert len(candidates) == 19
                counts["candidate_sets"] += 1
                family_counts["candidate_sets"] += 1
                if not all(conflict(e, f, adj)
                           for e, f in itertools.combinations(candidates, 2)):
                    continue
                counts["nineteen_cliques"] += 1
                family_counts["nineteen_cliques"] += 1
                if min(degrees[e] for e in candidates) < 19:
                    continue
                counts["high_nineteen_cliques"] += 1
                family_counts["high_nineteen_cliques"] += 1
                assert family == "one_quadruple_four_doubles"
                # Count a full original exceptional component, then verify
                # that deleting the one candidate changes only its correction.
                assert len(original) == 20
                assert correction_count(original, original) == 1
                assert correction_count(original, candidates) == 0
                assert all(degrees[e] == 19 for e in candidates)
                passing.append({
                    "family": family,
                    "tip_types": [sorted(part) for part in types],
                    "original_edges": sorted(original),
                    "candidate_edges": sorted(candidates),
                    "retained_original_noncandidate_edge": sorted(original - candidates),
                    "full_conflict_degree_of_every_candidate": 19,
                    "original_doubled_cycle_components": 1,
                    "candidate_correction": 0,
                })
    assert passing
    assert by_family["two_triples_three_doubles"]["high_nineteen_cliques"] == 0
    return {
        "scope": "All capacity-feasible type multisets in the two stated "
                 "saturated families, with all simple original graphs on their "
                 "tips having at least three edges and respecting original "
                 "degree four; all nineteen-edge core candidate sets containing "
                 "the four root edges. Spare core degree is completed by "
                 "separate branches. Tip permutations are represented by "
                 "nondecreasing type multisets; root labels remain labelled.",
        "counts": dict(counts),
        "counts_by_family": {name: dict(values) for name, values in by_family.items()},
        "passing_examples": passing,
    }


def doubled_cycle(offset):
    return {edge(offset + 2 * i + a, offset + 2 * ((i + 1) % 5) + b)
            for i in range(5) for a in (0, 1) for b in (0, 1)}


def check_compensation_examples():
    records = []
    for proper_count, full_count in [(1, 0), (2, 0), (3, 0), (4, 0), (2, 1), (0, 1)]:
        original = set()
        candidates = set()
        for index in range(proper_count + full_count):
            component = doubled_cycle(index * 10)
            original |= component
            candidates |= component - ({min(component)} if index < proper_count else set())
        chosen = exact_matching(original, candidates)
        adj = adjacency(original)
        owners = {x: {e for e in chosen if x == e or conflict(x, e, adj)}
                  for x in candidates}
        assert all(owners.values())
        deficits = []
        for e in chosen:
            degree = sum(conflict(e, x, adj) for x in candidates)
            private = sum(owner == {e} for owner in owners.values())
            deficits.append(39 - degree - 1 - private)
        excess = sum(len(owner) - 2 for owner in owners.values() if len(owner) >= 3)
        correction = correction_count(original, candidates)
        assert correction == full_count
        assert len(chosen) == proper_count + full_count
        assert sorted(deficits) == [-1] * full_count + [1] * proper_count
        assert 2 * len(candidates) == 39 * len(chosen) - sum(deficits) - excess
        assert len(candidates) == 19 * len(chosen) + correction
        assert sum(deficits) + excess == len(chosen) - 2 * correction
        records.append({
            "proper_nineteen_edge_components": proper_count,
            "fully_selected_components": full_count,
            "candidate_count": len(candidates),
            "exact_induced_matching_number": len(chosen),
            "candidate_correction": correction,
            "deficits": sorted(deficits),
            "R": excess,
            "original_edges": sorted(original),
            "candidate_edges": sorted(candidates),
            "maximum_induced_matching": chosen,
        })
    return records


def main():
    script = Path(__file__).resolve()
    dependency = script.with_name("check_stage2.py")
    triangle = check_triangle_roots()
    families = check_saturated_families()
    examples = check_compensation_examples()
    result = {
        "status": "All assertions passed",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "python_version": platform.python_version(),
        "script_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
        "dependency_sha256": hashlib.sha256(dependency.read_bytes()).hexdigest(),
        "evidence_limit": "Finite checks of the explicitly listed families and "
                          "boundary examples only; not an exhaustive original-graph "
                          "search, not Lean verification, and not a substitute for "
                          "the Stage 2 and Stage 3 paper proofs.",
        "triangle_roots": triangle,
        "saturated_families": families,
        "compensation_examples": examples,
    }
    output = script.parent.parent / "results" / "stage3-checks.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "triangle_root_graphs": triangle["original_graphs_checked"],
        "saturated_family_counts": families["counts"],
        "counts_by_family": families["counts_by_family"],
        "compensation_examples": len(examples),
        "output": str(output),
    }, indent=2))


if __name__ == "__main__":
    main()
