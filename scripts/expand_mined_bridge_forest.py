import json
import subprocess
import sys
import time
import traceback
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Node:
    tree: int
    depth: int
    name: str
    params: tuple[str, ...]
    conditions: tuple[str, ...]
    goal: str


def build(repo_path: Path, timeout: int):
    return subprocess.run(["lake", "build"], cwd=repo_path, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)


def load_seeds(paths: list[Path]):
    roots, conds, goals, apply_count = [], {}, {}, 0
    for path in paths:
        data = json.loads(path.read_text(encoding="utf-8"))
        if not data.get("ok"):
            raise ValueError(f"Seed mining file is not ok: {path}")
        ctx = data["context"]
        roots.append(Node(
            tree=len(roots),
            depth=0,
            name=data["parent"],
            params=tuple(ctx["params"]),
            conditions=tuple(hyp["prop"] for hyp in ctx["hypotheses"]),
            goal=ctx["goal"],
        ))
        for delta in data["condition_deltas"]:
            conds.setdefault(delta["old"], [])
            entry = {**delta, "kind": "condition_rw"}
            if entry not in conds[delta["old"]]:
                conds[delta["old"]].append(entry)
        for delta in data["goal_deltas"]:
            goals.setdefault(delta["old"], [])
            entry = {**delta, "kind": "goal_rw"}
            if entry not in goals[delta["old"]]:
                goals[delta["old"]].append(entry)
        apply_count += len(data["apply_invocable"])
    return roots, conds, goals, apply_count


def candidates(node: Node, conds: dict, goals: dict) -> list[dict]:
    out = []
    for idx, condition in enumerate(node.conditions):
        for delta in conds.get(condition, []):
            out.append({**delta, "hyp_index": idx})
    out.extend(goals.get(node.goal, []))
    return out


def choose(items: list[dict], tree: int, depth: int, leaf_idx: int, width: int) -> list[dict]:
    if not items:
        return []
    count = min(width, len(items))
    start = (tree * 17 + depth * 7 + leaf_idx) % len(items)
    rotated = [items[(start + idx) % len(items)] for idx in range(len(items))]
    picked = []
    for kind in ("condition_rw", "goal_rw"):
        for item in rotated:
            if item["kind"] == kind and item not in picked:
                picked.append(item)
                break
    picked.extend(item for item in rotated if item not in picked)
    return picked[:count]


def child_from(parent: Node, name: str, delta: dict) -> Node:
    conditions = list(parent.conditions)
    goal = parent.goal
    if delta["kind"] == "condition_rw":
        conditions[delta["hyp_index"]] = delta["new"]
    elif delta["kind"] == "goal_rw":
        goal = delta["new"]
    else:
        raise ValueError(f"Unsupported delta kind: {delta['kind']}")
    return Node(parent.tree, parent.depth + 1, name, parent.params, tuple(conditions), goal)


def theorem_text(parent: Node, child: Node, delta: dict) -> str:
    hyp_binders = " ".join(f"(h{idx} : {condition})" for idx, condition in enumerate(child.conditions))
    lines = [
        f"theorem {child.name} {' '.join(child.params)} {hyp_binders} :",
        f"    {child.goal} := by",
    ]
    for idx, condition in enumerate(parent.conditions):
        lines.append(f"  have hparent_{idx} : {condition} := by")
        if delta["kind"] == "condition_rw" and delta["hyp_index"] == idx:
            lines.extend([f"    rw [{delta['candidate']}]", f"    exact h{idx}"])
        else:
            lines.append(f"    exact h{idx}")
    lines.extend([f"  have hgoal : {parent.goal} := by", f"    apply {parent.name}"])
    lines.extend(f"    exact hparent_{idx}" for idx in range(len(parent.conditions)))
    if delta["kind"] == "goal_rw":
        lines.extend([f"  rw [{delta['candidate']}] at hgoal", "  exact hgoal"])
    else:
        lines.append("  exact hgoal")
    return "\n".join(lines)


def edge_delta(delta: dict) -> dict:
    out = {
        "kind": delta["kind"],
        "source_tactic": delta["dojo_tactic"],
        "source_theorem": delta["candidate"],
        "old": delta["old"],
        "new": delta["new"],
        "bridge_direction": delta["bridge_direction"],
    }
    if "hyp_index" in delta:
        out["hyp_index"] = delta["hyp_index"]
    return out


def main() -> int:
    repo_path = Path(sys.argv[1]).resolve()
    file_path = Path(sys.argv[2])
    output_path = Path(sys.argv[3])
    seed_paths = [Path(p).resolve() for p in sys.argv[4].split(",") if p]
    tree_count = int(sys.argv[5]) if len(sys.argv) > 5 else len(seed_paths)
    depth = int(sys.argv[6]) if len(sys.argv) > 6 else 3
    width = int(sys.argv[7]) if len(sys.argv) > 7 else 2
    started = time.time()
    target = repo_path / file_path
    original = target.read_text(encoding="utf-8")
    result = {
        "mode": "mined_seeded_recursive_forest",
        "repo_path": str(repo_path),
        "seed_files": [str(path) for path in seed_paths],
        "ok": False,
    }

    try:
        seed_roots, conds, goals, apply_count = load_seeds(seed_paths)
        leaves = []
        for idx in range(tree_count):
            root = seed_roots[idx % len(seed_roots)]
            leaves.append(Node(idx, 0, root.name, root.params, root.conditions, root.goal))
        nodes, edges, roots, blocks = [], [], [], []
        build_summaries = []

        for current_depth in range(1, depth + 1):
            next_leaves, depth_blocks = [], []
            for leaf_idx, parent in enumerate(leaves):
                for branch, delta in enumerate(choose(candidates(parent, conds, goals), parent.tree, current_depth, leaf_idx, width)):
                    child_name = f"xt_mined_tree_{parent.tree:03d}_d{current_depth}_{leaf_idx}_{branch}"
                    child = child_from(parent, child_name, delta)
                    depth_blocks.append(theorem_text(parent, child, delta))
                    next_leaves.append(child)
                    nodes.append({"name": child.name, "tree": child.tree, "depth": child.depth, "conditions": list(child.conditions), "goal": child.goal})
                    edges.append({
                        "tree": child.tree,
                        "depth": current_depth,
                        "parent": parent.name,
                        "child": child.name,
                        "delta": edge_delta(delta),
                    })
            if not depth_blocks:
                break
            blocks.extend(depth_blocks)
            target.write_text(original.rstrip() + "\n\n" + "\n\n".join(blocks) + "\n", encoding="utf-8")
            proc = build(repo_path, 900)
            build_summaries.append({"depth": current_depth, "returncode": proc.returncode, "output_tail": proc.stdout[-4000:]})
            if proc.returncode != 0:
                raise RuntimeError(f"Generated theorem build failed at depth {current_depth}")
            leaves = next_leaves

        roots = [{"tree": tree, "root": seed_roots[tree % len(seed_roots)].name} for tree in range(tree_count)]
        result.update({
            "ok": True,
            "tree_count": tree_count,
            "requested_depth": depth,
            "reached_depth": max((node["depth"] for node in nodes), default=0),
            "width": width,
            "node_count": len(nodes),
            "edge_count": len(edges),
            "condition_bridge_count": sum(len(v) for v in conds.values()),
            "goal_bridge_count": sum(len(v) for v in goals.values()),
            "apply_bridge_count": apply_count,
            "builds": build_summaries,
            "roots": roots,
            "nodes": nodes,
            "edges": edges,
        })
    except Exception as exc:
        result.update({"error_type": type(exc).__name__, "error": repr(exc), "traceback": traceback.format_exc()})
    finally:
        target.write_text(original, encoding="utf-8")

    result["seconds"] = round(time.time() - started, 3)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k not in {"nodes", "edges", "roots", "builds"}}, indent=2, ensure_ascii=False))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
