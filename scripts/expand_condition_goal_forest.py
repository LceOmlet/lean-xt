import json
import subprocess
import sys
import time
import traceback
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from lean_xt.leandojo import find_theorem


SET_A = "a.divisors.filter IsPrimePow"
SET_B = "b.divisors.filter IsPrimePow"


@dataclass(frozen=True)
class Cond:
    text: str
    to_parent: str


CONDITIONS = [
    Cond("a.Coprime b", "assumption"),
    Cond("IsRelPrime a b", "exact (Nat.coprime_iff_isRelPrime).2 hcond"),
    Cond("IsRelPrime a b \u2227 a \u2260 0", "exact hcond.1"),
    Cond("(IsRelPrime a b \u2227 a \u2260 0) \u2227 b \u2260 0", "exact hcond.1"),
]

GOALS = [
    f"Disjoint ({SET_A}) ({SET_B})",
    f"forall {{n : Nat}}, n \u2208 {SET_A} -> n \u2208 {SET_B} -> False",
]

GOAL_BRIDGES = [
    "",
    "apply Finset.disjoint_left.mp",
]

KINDS = ["condition_strengthen", "goal_weaken", "condition_strengthen_goal_weaken"]


@dataclass(frozen=True)
class Node:
    tree: int
    depth: int
    index: int
    name: str
    parent: str
    cond: int
    goal: int
    parent_cond: int
    parent_goal: int
    mutation: str


def width(tree: int, depth: int, leaf: int) -> int:
    return 1 + ((tree + depth + leaf) % 3)


def next_node(tree: int, depth: int, leaf: int, branch: int, parent: Node) -> Node:
    kind = KINDS[(tree + depth + leaf + branch) % len(KINDS)]
    cond = parent.cond
    goal = parent.goal
    if "condition" in kind:
        cond = min(cond + 1, len(CONDITIONS) - 1)
    if "goal" in kind and goal + 1 < len(GOALS):
        goal += 1
    if cond == parent.cond and goal == parent.goal and cond + 1 < len(CONDITIONS):
        cond += 1
    if cond == parent.cond and goal == parent.goal:
        raise ValueError("No verified mutation remains for this depth")
    kind = (
        "condition_strengthen_goal_weaken" if cond != parent.cond and goal != parent.goal
        else "condition_strengthen" if cond != parent.cond
        else "goal_weaken"
    )

    return Node(
        tree=tree,
        depth=depth,
        index=branch,
        name=f"xt_tree_{tree:03d}_d{depth}_{leaf}_{branch}",
        parent=parent.name,
        cond=cond,
        goal=goal,
        parent_cond=parent.cond,
        parent_goal=parent.goal,
        mutation=kind,
    )


def theorem_text(node: Node) -> str:
    lines = [
        f"theorem {node.name} {{a b : Nat}} (hcond : {CONDITIONS[node.cond].text}) :",
        f"    {GOALS[node.goal]} := by",
    ]
    if node.goal > node.parent_goal:
        lines.append(f"  {GOAL_BRIDGES[node.goal]}")
    lines.extend([
        f"  apply {node.parent}",
        f"  {CONDITIONS[node.cond].to_parent if node.cond != node.parent_cond else 'assumption'}",
    ])
    return "\n".join(lines)


def generate_forest(num_trees: int, depth: int):
    roots = []
    nodes = []
    edges = []
    for tree in range(num_trees):
        root = Node(tree, 0, 0, "alchemy_tree_t0", "", 0, 0, 0, 0, "root")
        leaves = [root]
        for d in range(1, depth + 1):
            new_leaves = []
            for leaf_idx, parent in enumerate(leaves):
                for branch in range(width(tree, d, leaf_idx)):
                    child = next_node(tree, d, leaf_idx, branch, parent)
                    nodes.append(child)
                    condition_delta = None
                    if child.cond != parent.cond:
                        condition_delta = {
                            "old": CONDITIONS[parent.cond].text,
                            "new": CONDITIONS[child.cond].text,
                            "bridge_tactic": CONDITIONS[child.cond].to_parent,
                        }
                    goal_delta = None
                    if child.goal != parent.goal:
                        goal_delta = {
                            "old": GOALS[parent.goal],
                            "new": GOALS[child.goal],
                            "bridge_tactic": GOAL_BRIDGES[child.goal],
                        }
                    edges.append({
                        "tree": tree,
                        "depth": d,
                        "parent": parent.name,
                        "child": child.name,
                        "mutation_type": child.mutation,
                        "condition_delta": condition_delta,
                        "goal_delta": goal_delta,
                        "condition": CONDITIONS[child.cond].text,
                        "goal": GOALS[child.goal],
                    })
                    new_leaves.append(child)
            leaves = new_leaves
        roots.append({"tree": tree, "root": root.name, "leaf_count": len(leaves)})
    return roots, nodes, edges


def main() -> int:
    repo_path = Path(sys.argv[1]).resolve()
    commit = sys.argv[2]
    theorem_name = sys.argv[3]
    file_path = Path(sys.argv[4])
    output_path = Path(sys.argv[5])
    num_trees = int(sys.argv[6]) if len(sys.argv) > 6 else 100
    depth = int(sys.argv[7]) if len(sys.argv) > 7 else 3
    started = time.time()
    result = {"repo_path": str(repo_path), "commit": commit, "parent": theorem_name, "ok": False}

    try:
        find_theorem(repo_path, commit, theorem_name, file_path)
        roots, nodes, edges = generate_forest(num_trees, depth)
        block = "\n\n".join(theorem_text(node) for node in nodes)

        target_file = repo_path / file_path
        original = target_file.read_text(encoding="utf-8")
        target_file.write_text(original.rstrip() + "\n\n" + block + "\n", encoding="utf-8")
        try:
            proc = subprocess.run(["lake", "build"], cwd=repo_path, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
        finally:
            target_file.write_text(original, encoding="utf-8")

        result.update({
            "ok": proc.returncode == 0,
            "build_returncode": proc.returncode,
            "build_output_tail": proc.stdout[-4000:],
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
