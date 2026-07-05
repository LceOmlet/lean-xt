import json
import re
import subprocess
import sys
import time
import traceback
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from lean_xt.condition_goal import _conclusion, _decl_nodes, _hypotheses
from lean_xt.leandojo import find_theorem


AND = "\u2227"
OR = "\u2228"
IFF = "\u2194"
MEM = "\u2208"
NE = "\u2260"
NOT = "\u00ac"


@dataclass(frozen=True)
class Hypothesis:
    name: str
    prop: str


@dataclass(frozen=True)
class Context:
    params: tuple[str, ...]
    terms: tuple[tuple[str, str], ...]
    hypotheses: tuple[Hypothesis, ...]
    goal: str
    extra_props: tuple[str, ...]


@dataclass(frozen=True)
class Bridge:
    schema: str
    source: str
    target: str
    tactics: tuple[str, ...]
    hyp_index: Optional[int] = None


@dataclass(frozen=True)
class Node:
    tree: int
    depth: int
    name: str
    parent: str
    conditions: tuple[str, ...]
    goal: str
    parent_conditions: tuple[str, ...]
    parent_goal: str
    cond_bridge: Optional[Bridge]
    goal_bridge: Optional[Bridge]


def binder_chunks(text: str) -> list[str]:
    pairs = {"{": "}", "(": ")", "[": "]"}
    chunks, stack, start = [], [], None
    for idx, ch in enumerate(text):
        if ch in pairs:
            if not stack:
                start = idx
            stack.append(pairs[ch])
        elif stack and ch == stack[-1]:
            stack.pop()
            if not stack and start is not None:
                chunks.append(text[start:idx + 1])
    return chunks


def split_binder(chunk: str) -> tuple[list[str], str]:
    inner = chunk[1:-1].strip()
    if ":" not in inner:
        return [], ""
    names, typ = inner.split(":", 1)
    return [n for n in names.split() if n != "_"], typ.strip()


def normalize_type(typ: str) -> str:
    return typ.replace("\u2115", "Nat").strip()


def theorem_context(traced_theorem) -> Context:
    _, decl, _, _, statement, _ = _decl_nodes(traced_theorem, raw_string=True)
    hyp_names, hyp_binders = _hypotheses(decl)
    hypotheses = []
    hyp_binder_set = set(hyp_binders)
    for names, binder in zip(hyp_names, hyp_binders):
        _, prop = split_binder("(" + binder + ")")
        hypotheses.append(Hypothesis(names[0], prop))

    goal = _conclusion(decl)
    prefix = statement[:statement.rfind(goal)]
    chunks = binder_chunks(prefix)
    params = []
    typed_names = []
    for chunk in chunks:
        inner = chunk[1:-1].strip()
        if inner in hyp_binder_set:
            continue
        params.append(chunk)
        names, typ = split_binder(chunk)
        for name in names:
            typed_names.append((name, normalize_type(typ)))

    extra_props = []
    for name, typ in typed_names:
        if typ == "Nat":
            extra_props.append(f"{name} {NE} 0")
    for i, (lhs, lhs_type) in enumerate(typed_names):
        for rhs, rhs_type in typed_names[i + 1:]:
            if lhs_type == rhs_type and lhs_type:
                extra_props.extend([f"{lhs} = {rhs}", f"{lhs} {NE} {rhs}"])
    return Context(tuple(params), tuple(typed_names), tuple(hypotheses), goal, tuple(dict.fromkeys(extra_props)))


def paren(prop: str) -> str:
    return f"({prop})"


def params_for(ctx: Context, texts: list[str]) -> str:
    body = "\n".join(texts)
    binders = []
    for chunk in ctx.params:
        names, typ = split_binder(chunk)
        used = [name for name in names if re.search(rf"\b{re.escape(name)}\b", body)]
        if used:
            binders.append(f"{chunk[0]}{' '.join(used)} : {typ}{chunk[-1]}")
    return " ".join(binders)


def strip_outer_parens(text: str) -> str:
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        for idx, ch in enumerate(text):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and idx != len(text) - 1:
                    return text
        text = text[1:-1].strip()
    return text


def split_top(text: str, sep: str) -> Optional[tuple[str, str]]:
    depth = 0
    for idx, ch in enumerate(text):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == sep and depth == 0:
            return text[:idx].strip(), text[idx + 1:].strip()
    return None


def app_args(text: str) -> Optional[tuple[str, list[str]]]:
    text = strip_outer_parens(text)
    match = re.match(r"^([A-Za-z_][A-Za-z0-9_'.]*)\s+(.+)$", text)
    if not match:
        return None
    head, rest = match.groups()
    args = []
    while rest.strip():
        rest = rest.strip()
        if rest.startswith("("):
            depth = 0
            for idx, ch in enumerate(rest):
                if ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0:
                        args.append(rest[:idx + 1])
                        rest = rest[idx + 1:]
                        break
            else:
                return None
        else:
            piece, _, rest = rest.partition(" ")
            args.append(piece)
    return head, args


def parse_forall(goal: str) -> Optional[tuple[str, Optional[str], str]]:
    goal = strip_outer_parens(goal)
    match = re.match(r"^forall\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*([^,]+),\s*(.+)$", goal)
    if match:
        var, typ, body = match.groups()
        return var, normalize_type(typ), body.strip()
    match = re.match(r"^forall\s+([A-Za-z_][A-Za-z0-9_']*)\s*,\s*(.+)$", goal)
    if match:
        var, body = match.groups()
        return var, None, body.strip()
    return None


def instantiate_var(body: str, var: str, term: str) -> str:
    return re.sub(rf"\b{re.escape(var)}\b", term, body)


def condition_bridges(ctx: Context, conditions: tuple[str, ...]) -> list[Bridge]:
    bridges = []
    for hyp_index, prop in enumerate(conditions):
        for extra in ctx.extra_props:
            source = f"{paren(prop)} {AND} {paren(extra)}"
            bridges.append(Bridge("and_projection", source, prop, ("exact hcond.1",), hyp_index))
            source = f"({paren(extra)} {IFF} {paren(prop)}) {AND} {paren(extra)}"
            bridges.append(Bridge("iff_condition_transport", source, prop, ("exact hcond.1.mp hcond.2",), hyp_index))
    return bridges


def relation_goal_bridges(goal: str) -> list[Bridge]:
    parsed = app_args(goal)
    if parsed is None:
        return []
    head, args = parsed
    if head != "Disjoint" or len(args) != 2:
        return []
    left, right = args
    return [
        Bridge("symmetric_relation_goal", f"Disjoint {right} {left}", goal, ("exact hgoal.symm",)),
        Bridge(
            "pointwise_goal_unfold",
            f"forall x, x {MEM} {left} -> x {MEM} {right} -> False",
            goal,
            ("exact fun x hx hy => (Finset.disjoint_left.mp hgoal) hx hy",),
        ),
    ]


def goal_bridges(ctx: Context, goal: str) -> list[Bridge]:
    bridges = [
        Bridge("not_not_intro", f"{NOT}{NOT}{paren(goal)}", goal, ("exact fun hnot => hnot hgoal",)),
        Bridge("and_true_intro", f"{paren(goal)} {AND} True", goal, ("exact \u27e8hgoal, True.intro\u27e9",)),
    ]
    split_and = split_top(strip_outer_parens(goal), AND)
    if split_and:
        left, right = split_and
        bridges.append(Bridge("and_goal_projection_left", left, goal, ("exact hgoal.1",)))
        if strip_outer_parens(right) != "True":
            bridges.append(Bridge("and_goal_projection_right", right, goal, ("exact hgoal.2",)))
    forall_parts = parse_forall(goal)
    if forall_parts:
        var, typ, body = forall_parts
        for term, term_type in ctx.terms:
            if typ is None or normalize_type(typ) == term_type:
                bridges.append(Bridge("forall_specialization", instantiate_var(body, var, term), goal, (f"exact hgoal {term}",)))
    bridges.extend(relation_goal_bridges(goal))
    for extra in ctx.extra_props:
        schema = "nested_or_intro" if split_top(strip_outer_parens(goal), OR) else "or_intro"
        bridges.append(Bridge(schema, f"{paren(goal)} {OR} {paren(extra)}", goal, ("exact Or.inl hgoal",)))
        bridges.append(Bridge("iff_goal_transport", f"({paren(goal)} {IFF} {paren(extra)}) -> {paren(extra)}", goal, ("exact fun hiff => hiff.mp hgoal",)))
    bridges.append(Bridge("exists_intro_unit", f"Exists fun _ : Unit => {paren(goal)}", goal, ("exact \u27e8(), hgoal\u27e9",)))
    return bridges


def candidate_bridges(ctx: Context, parent: Node):
    conds = condition_bridges(ctx, parent.conditions)
    goals = goal_bridges(ctx, parent.goal)
    candidates = [(None, g) for g in goals] + [(c, None) for c in conds]
    candidates += [(c, g) for c in conds for g in goals]
    return candidates


def width(tree: int, depth: int, leaf: int) -> int:
    return 1 + ((tree + depth + leaf) % 3)


def choose(candidates, tree: int, depth: int, leaf: int):
    count = min(width(tree, depth, leaf), len(candidates))
    start = (tree * 13 + depth * 7 + leaf) % len(candidates)
    rotated = [candidates[(start + i) % len(candidates)] for i in range(len(candidates))]
    picked, seen = [], set()
    priority = {"forall_specialization", "and_goal_projection_left", "and_goal_projection_right"}
    for cond_bridge, goal_bridge in rotated:
        if goal_bridge is None or goal_bridge.schema not in priority:
            continue
        key = (None if cond_bridge is None else cond_bridge.schema, goal_bridge.schema)
        if key not in seen:
            picked.append((cond_bridge, goal_bridge))
            seen.add(key)
            if len(picked) == count:
                return picked
    for cond_bridge, goal_bridge in rotated:
        key = (None if cond_bridge is None else cond_bridge.schema, None if goal_bridge is None else goal_bridge.schema)
        if key in seen:
            continue
        picked.append((cond_bridge, goal_bridge))
        seen.add(key)
        if len(picked) == count:
            return picked
    picked.extend(candidate for candidate in rotated if candidate not in picked)
    return picked[:count]


def mutation_type(cond_bridge: Optional[Bridge], goal_bridge: Optional[Bridge]) -> str:
    if cond_bridge and goal_bridge:
        return "condition_strengthen_goal_weaken"
    if cond_bridge:
        return "condition_strengthen"
    return "goal_weaken"


def safe_label(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9_]+", "_", text).strip("_")[:80]


def bridge_delta(bridge: Optional[Bridge], kind: str):
    if bridge is None:
        return None
    old, new = (bridge.target, bridge.source) if kind == "condition" else (bridge.target, bridge.source)
    return {"schema": bridge.schema, "old": old, "new": new, "tactics": list(bridge.tactics)}


def theorem_text(ctx: Context, node: Node) -> str:
    hyp_binders = [f"(h{i} : {condition})" for i, condition in enumerate(node.conditions)]
    lines = [
        f"theorem {node.name} {' '.join(ctx.params)} {' '.join(hyp_binders)} :",
        f"    {node.goal} := by",
    ]
    for idx, parent_condition in enumerate(node.parent_conditions):
        lines.append(f"  have hparent_{idx} : {parent_condition} := by")
        if node.cond_bridge and node.cond_bridge.hyp_index == idx:
            lines.extend("    " + tactic.replace("hcond", f"h{idx}") for tactic in node.cond_bridge.tactics)
        else:
            lines.append(f"    exact h{idx}")
    lines.extend([f"  have hgoal : {node.parent_goal} := by", f"    apply {node.parent}"])
    lines.extend(f"    exact hparent_{idx}" for idx in range(len(node.parent_conditions)))
    if node.goal_bridge:
        lines.extend("  " + tactic for tactic in node.goal_bridge.tactics)
    else:
        lines.append("  exact hgoal")
    return "\n".join(lines)


def bridge_probe_text(ctx: Context, conds: list[Bridge], goals: list[Bridge]) -> str:
    blocks = []
    for idx, bridge in enumerate(conds):
        params = params_for(ctx, [bridge.source, bridge.target])
        lines = [
            f"theorem xt_schema_probe_cond_{idx}_{safe_label(bridge.schema)} {params} (hcond : {bridge.source}) :",
            f"    {bridge.target} := by",
        ]
        lines.extend("  " + tactic for tactic in bridge.tactics)
        blocks.append("\n".join(lines))
    for idx, bridge in enumerate(goals):
        params = params_for(ctx, [bridge.source, bridge.target])
        lines = [
            f"theorem xt_schema_probe_goal_{idx}_{safe_label(bridge.schema)} {params} (hgoal : {bridge.target}) :",
            f"    {bridge.source} := by",
        ]
        lines.extend("  " + tactic for tactic in bridge.tactics)
        blocks.append("\n".join(lines))
    return "\n\n".join(blocks)


def child_from(parent: Node, tree: int, depth: int, leaf: int, branch: int, cond_bridge, goal_bridge):
    conditions = list(parent.conditions)
    if cond_bridge:
        conditions[cond_bridge.hyp_index] = cond_bridge.source
    return Node(
        tree=tree,
        depth=depth,
        name=f"xt_schema_tree_{tree:03d}_d{depth}_{leaf}_{branch}",
        parent=parent.name,
        conditions=tuple(conditions),
        goal=goal_bridge.source if goal_bridge else parent.goal,
        parent_conditions=parent.conditions,
        parent_goal=parent.goal,
        cond_bridge=cond_bridge,
        goal_bridge=goal_bridge,
    )


def generate_forest(ctx: Context, root_name: str, num_trees: int, depth: int):
    roots, nodes, edges = [], [], []
    for tree in range(num_trees):
        leaves = [Node(tree, 0, root_name, "", tuple(h.prop for h in ctx.hypotheses), ctx.goal, (), "", None, None)]
        for d in range(1, depth + 1):
            new_leaves = []
            for leaf_idx, parent in enumerate(leaves):
                for branch, (cond_bridge, goal_bridge) in enumerate(choose(candidate_bridges(ctx, parent), tree, d, leaf_idx)):
                    child = child_from(parent, tree, d, leaf_idx, branch, cond_bridge, goal_bridge)
                    nodes.append(child)
                    edges.append({
                        "tree": tree,
                        "depth": d,
                        "parent": parent.name,
                        "child": child.name,
                        "mutation_type": mutation_type(cond_bridge, goal_bridge),
                        "condition_delta": bridge_delta(cond_bridge, "condition"),
                        "goal_delta": bridge_delta(goal_bridge, "goal"),
                        "conditions": list(child.conditions),
                        "goal": child.goal,
                    })
                    new_leaves.append(child)
            leaves = new_leaves
        roots.append({"tree": tree, "root": root_name, "leaf_count": len(leaves)})
    return roots, nodes, edges


def unique_bridges(edges):
    conds, goals = {}, {}
    for edge in edges:
        delta = edge["condition_delta"]
        if delta:
            conds[(delta["schema"], delta["old"], delta["new"])] = Bridge(delta["schema"], delta["new"], delta["old"], tuple(delta["tactics"]))
        delta = edge["goal_delta"]
        if delta:
            goals[(delta["schema"], delta["old"], delta["new"])] = Bridge(delta["schema"], delta["new"], delta["old"], tuple(delta["tactics"]))
    return list(conds.values()), list(goals.values())


def append_and_build(repo_path: Path, file_path: Path, block: str, timeout: int):
    target_file = repo_path / file_path
    original = target_file.read_text(encoding="utf-8")
    target_file.write_text(original.rstrip() + "\n\n" + block + "\n", encoding="utf-8")
    try:
        return subprocess.run(["lake", "build"], cwd=repo_path, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
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
    result = {"mode": "schema_v2", "repo_path": str(repo_path), "commit": commit, "parent": theorem_name, "ok": False}

    try:
        theorem = find_theorem(repo_path, commit, theorem_name, file_path)
        ctx = theorem_context(theorem)
        roots, nodes, edges = generate_forest(ctx, theorem_name, num_trees, depth)
        conds, goals = unique_bridges(edges)

        probe_proc = append_and_build(repo_path, file_path, bridge_probe_text(ctx, conds, goals), 600)
        result.update({
            "probe_build_returncode": probe_proc.returncode,
            "probe_build_output_tail": probe_proc.stdout[-4000:],
            "condition_probe_count": len(conds),
            "goal_probe_count": len(goals),
            "schema_names": sorted({b.schema for b in [*conds, *goals]}),
            "context": {
                "params": list(ctx.params),
                "terms": [{"name": name, "type": typ} for name, typ in ctx.terms],
                "hypotheses": [{"name": h.name, "prop": h.prop} for h in ctx.hypotheses],
                "goal": ctx.goal,
                "extra_props": list(ctx.extra_props),
            },
        })
        if probe_proc.returncode != 0:
            raise RuntimeError("schema bridge probes failed")

        forest_proc = append_and_build(repo_path, file_path, "\n\n".join(theorem_text(ctx, node) for node in nodes), 900)
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
