"""Check Stage 2 obstruction templates and exact boundary examples.

This is not an exhaustive search over original graphs. All conflicts below
are computed in the complete supplied graph, including noncandidate edges.
Only the Python standard library is required.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import platform
from collections import defaultdict
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path


def edge(u, v):
    assert u != v
    return tuple(sorted((u, v)))


def adjacency(edges):
    adj = defaultdict(set)
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    assert max(map(len, adj.values()), default=0) <= 4
    return dict(adj)


def conflict(e, f, adj):
    if e == f:
        return False
    return bool(set(e) & set(f)) or any(v in adj[u] for u in e for v in f)


def conflict_degree(e, edges):
    adj = adjacency(edges)
    return sum(conflict(e, f, adj) for f in edges)


def cover(e, edges):
    adj = adjacency(edges)
    u, v = e
    return (adj[u] - {v}) | (adj[v] - {u})


def complete_degrees_with_leaves(edges):
    """Saturate the existing vertices; the fresh leaves are original edges."""
    result = set(edges)
    adj = adjacency(result)
    fresh = max(adj, default=-1) + 1
    for u in sorted(adj):
        for _ in range(4 - len(adj[u])):
            result.add(edge(u, fresh))
            fresh += 1
    adjacency(result)
    return result


def root_graph(types, outer):
    result = {edge(0, label) for label in range(1, 5)}
    result |= {edge(tip, label) for tip, labels in types.items() for label in labels}
    result |= {edge(u, v) for u, v in outer}
    adjacency(result)
    return result


def record_cover_obstruction(name, edges, selected_edge):
    adj = adjacency(edges)
    assert all(len(adj[u]) == 4 for u in selected_edge)
    vertices = cover(selected_edge, edges)
    inside = sorted(e for e in edges if set(e) <= vertices)
    degree = conflict_degree(selected_edge, edges)
    assert len(vertices) == 6
    assert len(inside) >= 5
    assert degree == sum(len(adj[u]) for u in vertices) - len(inside)
    assert degree <= 19
    return {
        "template": name,
        "original_edges": sorted(edges),
        "selected_edge": selected_edge,
        "cover_vertices": sorted(vertices),
        "internal_cover_edges": inside,
        "full_conflict_degree": degree,
    }


def check_templates():
    records = []
    labels = set(range(1, 5))
    for first_tuple in itertools.combinations(sorted(labels), 2):
        first = set(first_tuple)
        second = labels - first
        doubles = {5: first, 6: second, 7: first, 8: second}
        cycle = root_graph(doubles, [(5, 6), (6, 7), (7, 8), (8, 5)])
        cycle = complete_degrees_with_leaves(cycle)
        for selected in [edge(5, 6), edge(6, 7), edge(7, 8), edge(8, 5)]:
            records.append(record_cover_obstruction("double_four_cycle", cycle, selected))

        for missing in sorted(labels):
            triple = labels - {missing}
            for endpoint, next_vertex in [(5, 6), (8, 7)]:
                if doubles[endpoint] | triple != labels:
                    continue
                types = {**doubles, 9: triple}
                path = root_graph(types, [(5, 6), (6, 7), (7, 8), (9, endpoint)])
                path = complete_degrees_with_leaves(path)
                records.append(record_cover_obstruction(
                    "triple_attached_to_double_path", path, edge(endpoint, next_vertex)
                ))

            types = {**doubles, 9: triple, 10: {missing}}
            separated = root_graph(types, [(5, 6), (6, 7), (7, 8), (9, 10)])
            separated = complete_degrees_with_leaves(separated)
            adj = adjacency(separated)
            assert not conflict(edge(9, 10), edge(6, 7), adj)
            records.append({
                "template": "triple_edge_disjoint_from_double_path",
                "original_edges": sorted(separated),
                "nonconflicting_selected_pair": [edge(9, 10), edge(6, 7)],
            })
    return records


def exact_matching(edges, candidates):
    adj = adjacency(edges)
    vertices = sorted(candidates)
    neighbours = [sum(1 << j for j, f in enumerate(vertices) if conflict(e, f, adj))
                  for e in vertices]

    @lru_cache(None)
    def solve(mask):
        if not mask:
            return ()
        available = [i for i in range(len(vertices)) if mask >> i & 1]
        i = max(available, key=lambda j: (neighbours[j] & mask).bit_count())
        without = mask & ~(1 << i)
        chosen = (i,) + solve(without & ~neighbours[i])
        skipped = solve(without)
        return chosen if len(chosen) >= len(skipped) else skipped

    result = [vertices[i] for i in solve((1 << len(vertices)) - 1)]
    assert all(not conflict(e, f, adj) for e, f in itertools.combinations(result, 2))
    return result


def correction_count(edges, candidates):
    adj = adjacency(edges)
    remaining = set(adj)
    result = 0
    while remaining:
        start = min(remaining)
        component = {start}
        pending = [start]
        while pending:
            for v in adj[pending.pop()]:
                if v not in component:
                    component.add(v)
                    pending.append(v)
        remaining -= component
        component_edges = {e for e in edges if set(e) <= component}
        if len(component) != 10 or len(component_edges) != 20:
            continue
        twin_classes = defaultdict(set)
        for v in component:
            twin_classes[frozenset(adj[v])].add(v)
        classes = list(twin_classes.values())
        if len(classes) != 5 or any(len(part) != 2 for part in classes):
            continue
        if any(len(adj[v]) != 4 for v in component):
            continue
        quotient_degrees = [sum(bool(adj[min(part)] & other) for other in classes)
                            for part in classes]
        if quotient_degrees == [2] * 5 and component_edges <= candidates:
            result += 1
    return result


def doubled_cycle(offset):
    return {edge(offset + 2 * i + a, offset + 2 * ((i + 1) % 5) + b)
            for i in range(5) for a in range(2) for b in range(2)}


def check_examples():
    original = doubled_cycle(0) | doubled_cycle(10)
    examples = []
    for name, removed, expected_size, expected_t in [
        ("two_proper_doubled_cycles", {edge(0, 2), edge(10, 12)}, 38, 0),
        ("one_full_one_proper_doubled_cycle", {edge(10, 12)}, 39, 1),
        ("two_full_doubled_cycles", set(), 40, 2),
    ]:
        candidates = original - removed
        matching = exact_matching(original, candidates)
        correction = correction_count(original, candidates)
        assert len(candidates) == expected_size and len(matching) == 2
        assert correction == expected_t
        assert len(candidates) == 19 * len(matching) + correction
        examples.append({
            "name": name, "original_edges": sorted(original),
            "candidate_edges": sorted(candidates), "maximum_matching": matching,
            "candidate_count": len(candidates), "induced_matching_number": len(matching),
            "component_correction": correction,
        })

    path = {edge(0, 1), edge(1, 2), edge(2, 3)}
    candidates = {edge(0, 1), edge(2, 3)}
    matching = exact_matching(path, candidates)
    assert len(matching) == 1
    assert len(exact_matching(candidates, candidates)) == 2
    examples.append({
        "name": "unselected_middle_edge_remains_a_witness",
        "original_edges": sorted(path), "candidate_edges": sorted(candidates),
        "maximum_matching": matching, "induced_matching_number": 1,
    })
    return examples


def main():
    templates = check_templates()
    examples = check_examples()
    counts = defaultdict(int)
    for item in templates:
        counts[item["template"]] += 1
    assert dict(counts) == {
        "double_four_cycle": 24,
        "triple_attached_to_double_path": 24,
        "triple_edge_disjoint_from_double_path": 24,
    }
    output = Path(__file__).resolve().parents[1] / "results" / "stage2-checks.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    result = {
        "status": "passed",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "python_version": platform.python_version(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Seventy-two labelled template checks and four exact boundary examples; not an exhaustive 39-edge graph search and not a formal proof.",
        "template_counts": dict(counts), "templates": templates, "examples": examples,
    }
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "passed", "template_counts": dict(counts),
                      "exact_examples": len(examples), "result": str(output)}))


if __name__ == "__main__":
    main()
