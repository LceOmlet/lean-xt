import json
import subprocess
import sys
import time
import traceback
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from lean_xt.leandojo import find_theorem


AND = "\u2227"
NE = "\u2260"
MEM = "\u2208"
SET_A = "a.divisors.filter IsPrimePow"
SET_B = "b.divisors.filter IsPrimePow"

CONDITIONS = [
    "a.Coprime b",
    "IsRelPrime a b",
    "Nat.gcd a b = 1",
    "b.Coprime a",
    f"a.Coprime b {AND} a {NE} 0",
    f"IsRelPrime a b {AND} a {NE} 0",
    f"Nat.gcd a b = 1 {AND} a {NE} 0",
    f"b.Coprime a {AND} b {NE} 0",
    f"(IsRelPrime a b {AND} a {NE} 0) {AND} b {NE} 0",
    f"(Nat.gcd a b = 1 {AND} a {NE} 0) {AND} b {NE} 0",
    f"(b.Coprime a {AND} b {NE} 0) {AND} a {NE} 0",
    f"(a.Coprime b {AND} a {NE} 0) {AND} b {NE} 0",
    f"((a.Coprime b {AND} a {NE} 0) {AND} b {NE} 0) {AND} a + b {NE} 0",
]

GOALS = [
    f"Disjoint ({SET_A}) ({SET_B})",
    f"forall {{n : Nat}}, n {MEM} {SET_A} -> n {MEM} {SET_B} -> False",
    f"Disjoint ({SET_B}) ({SET_A})",
    f"forall {{n : Nat}}, n {MEM} {SET_B} -> n {MEM} {SET_A} -> False",
]


@dataclass(frozen=True)
class Bridge:
    label: str
    source: int
    target: int
    tactics: tuple[str, ...]


COND_BRIDGES = [
    Bridge("rel_to_coprime", 1, 0, ("apply (Nat.coprime_iff_isRelPrime).2", "apply hcond")),
    Bridge("gcd_to_coprime", 2, 0, ("apply (Nat.coprime_iff_gcd_eq_one).2", "apply hcond")),
    Bridge("comm_to_coprime", 3, 0, ("apply Nat.Coprime.symm", "apply hcond")),
    Bridge("coprime_and_nonzero_to_coprime", 4, 0, ("apply hcond.1",)),
    Bridge("gcd_to_rel", 2, 1, ("apply (Nat.coprime_iff_isRelPrime).1", "apply (Nat.coprime_iff_gcd_eq_one).2", "apply hcond")),
    Bridge("comm_to_rel", 3, 1, ("apply (Nat.coprime_iff_isRelPrime).1", "apply Nat.Coprime.symm", "apply hcond")),
    Bridge("rel_and_nonzero_to_rel", 5, 1, ("apply hcond.1",)),
    Bridge("gcd_and_nonzero_to_gcd", 6, 2, ("apply hcond.1",)),
    Bridge("comm_and_nonzero_to_comm", 7, 3, ("apply hcond.1",)),
    Bridge("rel_deep_to_rel_and", 8, 5, ("apply hcond.1",)),
    Bridge("gcd_deep_to_gcd_and", 9, 6, ("apply hcond.1",)),
    Bridge("comm_deep_to_comm_and", 10, 7, ("apply hcond.1",)),
    Bridge("coprime_deep_to_coprime_and", 11, 4, ("apply hcond.1",)),
    Bridge("coprime_deeper_to_coprime_deep", 12, 11, ("apply hcond.1",)),
]

GOAL_BRIDGES = [
    Bridge("disjoint_to_forall", 0, 1, ("apply Finset.disjoint_left.mp", "apply hgoal")),
    Bridge("disjoint_symm", 0, 2, ("apply Disjoint.symm", "apply hgoal")),
    Bridge("symm_disjoint_to_forall", 2, 3, ("apply Finset.disjoint_left.mp", "apply hgoal")),
]


@dataclass(frozen=True)
class Node:
    tree: int
    depth: int
    name: str
    parent: str
    cond: int
    goal: int
    cond_bridge: Optional[Bridge]
    goal_bridge: Optional[Bridge]


def assert_apply_only() -> None:
    for bridge in [*COND_BRIDGES, *GOAL_BRIDGES]:
        for tactic in bridge.tactics:
            if not tactic.startswith("apply "):
                raise ValueError(f"Non-apply tactic in {bridge.label}: {tactic}")


def width(tree: int, depth: int, leaf: int) -> int:
    return 1 + ((tree + depth + leaf) % 3)


def candidate_bridges(parent: Node):
    conds = [b for b in COND_BRIDGES if b.target == parent.cond]
    goals = [b for b in GOAL_BRIDGES if b.source == parent.goal]
    candidates = [(c, None) for c in conds] + [(None, g) for g in goals]
    candidates += [(c, g) for c in conds for g in goals]
    return candidates


def choose_candidates(candidates, tree: int, depth: int, leaf: int):
    if not candidates:
        raise ValueError("No apply bridge candidates remain")
    count = min(width(tree, depth, leaf), len(candidates))
    start = (tree * 7 + depth * 3 + leaf) % len(candidates)
    return [candidates[(start + i) % len(candidates)] for i in range(count)]


def condition_delta(bridge: Optional[Bridge]):
    if bridge is None:
        return None
    return {
        "old": CONDITIONS[bridge.target],
        "new": CONDITIONS[bridge.source],
        "bridge": bridge.label,
        "apply_tactics": list(bridge.tactics),
    }


def goal_delta(bridge: Optional[Bridge]):
    if bridge is None:
        return None
    return {
        "old": GOALS[bridge.source],
        "new": GOALS[bridge.target],
        "bridge": bridge.label,
        "apply_tactics": list(bridge.tactics),
    }


def mutation_type(cond_bridge: Optional[Bridge], goal_bridge: Optional[Bridge]) -> str:
    if cond_bridge and goal_bridge:
        return "condition_strengthen_goal_weaken"
    if cond_bridge:
        return "condition_strengthen"
    return "goal_weaken"


def child_from(parent: Node, tree: int, depth: int, leaf: int, branch: int, cond_bridge, goal_bridge):
    cond = cond_bridge.source if cond_bridge else parent.cond
    goal = goal_bridge.target if goal_bridge else parent.goal
    return Node(
        tree=tree,
        depth=depth,
        name=f"xt_apply_tree_{tree:03d}_d{depth}_{leaf}_{branch}",
        parent=parent.name,
        cond=cond,
        goal=goal,
        cond_bridge=cond_bridge,
        goal_bridge=goal_bridge,
    )


def apply_parent_tactics(node: Node) -> list[str]:
    lines = []
    if node.goal_bridge:
        lines.extend("apply " + node.parent if t == "apply hgoal" else t for t in node.goal_bridge.tactics)
    else:
        lines.append("apply " + node.parent)
    lines.extend(node.cond_bridge.tactics if node.cond_bridge else ("apply hcond",))
    return lines


def theorem_text(node: Node) -> str:
    lines = [
        f"theorem {node.name} {{a b : Nat}} (hcond : {CONDITIONS[node.cond]}) :",
        f"    {GOALS[node.goal]} := by",
    ]
    lines.extend("  " + tactic for tactic in apply_parent_tactics(node))
    return "\n".join(lines)


def bridge_probe_text() -> str:
    blocks = []
    for bridge in COND_BRIDGES:
        lines = [
            f"theorem xt_apply_probe_cond_{bridge.label} {{a b : Nat}} (hcond : {CONDITIONS[bridge.source]}) :",
            f"    {CONDITIONS[bridge.target]} := by",
        ]
        lines.extend("  " + tactic for tactic in bridge.tactics)
        blocks.append("\n".join(lines))
    for bridge in GOAL_BRIDGES:
        lines = [
            f"theorem xt_apply_probe_goal_{bridge.label} {{a b : Nat}} (hgoal : {GOALS[bridge.source]}) :",
            f"    {GOALS[bridge.target]} := by",
        ]
        lines.extend("  " + tactic for tactic in bridge.tactics)
        blocks.append("\n".join(lines))
    return "\n\n".join(blocks)


def generate_forest(root_name: str, num_trees: int, depth: int):
    roots, nodes, edges = [], [], []
    for tree in range(num_trees):
        leaves = [Node(tree, 0, root_name, "", 0, 0, None, None)]
        for d in range(1, depth + 1):
            new_leaves = []
            for leaf_idx, parent in enumerate(leaves):
                candidates = candidate_bridges(parent)
                for branch, (cond_bridge, goal_bridge) in enumerate(choose_candidates(candidates, tree, d, leaf_idx)):
                    child = child_from(parent, tree, d, leaf_idx, branch, cond_bridge, goal_bridge)
                    nodes.append(child)
                    edges.append({
                        "tree": tree,
                        "depth": d,
                        "parent": parent.name,
                        "child": child.name,
                        "mutation_type": mutation_type(cond_bridge, goal_bridge),
                        "condition_delta": condition_delta(cond_bridge),
                        "goal_delta": goal_delta(goal_bridge),
                        "condition": CONDITIONS[child.cond],
                        "goal": GOALS[child.goal],
                    })
                    new_leaves.append(child)
            leaves = new_leaves
        roots.append({"tree": tree, "root": root_name, "leaf_count": len(leaves)})
    return roots, nodes, edges


def lake_build(repo_path: Path, timeout: int):
    return subprocess.run(["lake", "build"], cwd=repo_path, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)


def append_and_build(repo_path: Path, file_path: Path, block: str, timeout: int):
    target_file = repo_path / file_path
    original = target_file.read_text(encoding="utf-8")
    target_file.write_text(original.rstrip() + "\n\n" + block + "\n", encoding="utf-8")
    try:
        return lake_build(repo_path, timeout)
    finally:
        target_file.write_text(original, encoding="utf-8")


def main() -> int:
    repo_path = Path(sys.argv[1]).resolve()
    commit = sys.argv[2]
    theorem_name = sys.argv[3]
    file_path = Path(sys.argv[4])
    output_path = Path(sys.argv[5])
    num_trees = int(sys.argv[6]) if len(sys.argv) > 6 else 100
    depth = int(sys.argv[7]) if len(sys.argv) > 7 else 3
    started = time.time()
    result = {"mode": "apply_only", "repo_path": str(repo_path), "commit": commit, "parent": theorem_name, "ok": False}

    try:
        assert_apply_only()
        find_theorem(repo_path, commit, theorem_name, file_path)
        probe_proc = append_and_build(repo_path, file_path, bridge_probe_text(), 600)
        result.update({
            "probe_build_returncode": probe_proc.returncode,
            "probe_build_output_tail": probe_proc.stdout[-4000:],
            "bridge_probe_count": len(COND_BRIDGES) + len(GOAL_BRIDGES),
        })
        if probe_proc.returncode != 0:
            raise RuntimeError("apply bridge probes failed")

        roots, nodes, edges = generate_forest(theorem_name, num_trees, depth)
        forest_proc = append_and_build(repo_path, file_path, "\n\n".join(theorem_text(node) for node in nodes), 900)
        result.update({
            "ok": forest_proc.returncode == 0,
            "forest_build_returncode": forest_proc.returncode,
            "forest_build_output_tail": forest_proc.stdout[-4000:],
            "tree_count": num_trees,
            "depth": depth,
            "node_count": len(nodes),
            "edge_count": len(edges),
            "min_leaf_count": min(r["leaf_count"] for r in roots),
            "max_leaf_count": max(r["leaf_count"] for r in roots),
            "roots": roots,
            "edges": edges,
        })
    except Exception as exc:
        result.update({"error_type": type(exc).__name__, "error": repr(exc), "traceback": traceback.format_exc()})

    result["seconds"] = round(time.time() - started, 3)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k not in {"edges", "roots"}}, indent=2, ensure_ascii=False))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
