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

from lean_dojo import Dojo, TacticState

from lean_xt.condition_goal import _conclusion, _decl_nodes, _hypotheses
from lean_xt.leandojo import find_theorem, traced_theorems_in_file


@dataclass(frozen=True)
class Hypothesis:
    name: str
    prop: str


@dataclass(frozen=True)
class Context:
    params: tuple[str, ...]
    hypotheses: tuple[Hypothesis, ...]
    goal: str


@dataclass(frozen=True)
class StateView:
    hypotheses: dict[str, str]
    goal: str
    raw: str


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
    return [name for name in names.split() if name != "_"], typ.strip()


def theorem_context(traced_theorem) -> Context:
    _, decl, _, _, statement, _ = _decl_nodes(traced_theorem, raw_string=True)
    hyp_names, hyp_binders = _hypotheses(decl)
    hypotheses = []
    for names, binder in zip(hyp_names, hyp_binders):
        _, prop = split_binder("(" + binder + ")")
        if names:
            hypotheses.append(Hypothesis(names[0], prop))

    goal = _conclusion(decl)
    prefix = statement[:statement.rfind(goal)]
    hyp_binder_set = set(hyp_binders)
    params = []
    for chunk in binder_chunks(prefix):
        if chunk[1:-1].strip() not in hyp_binder_set:
            params.append(chunk)
    return Context(tuple(params), tuple(hypotheses), goal)


def params_for(ctx: Context, texts: list[str]) -> str:
    body = "\n".join(texts)
    binders = []
    for chunk in ctx.params:
        names, typ = split_binder(chunk)
        used = [name for name in names if re.search(rf"\b{re.escape(name)}\b", body)]
        if used:
            binders.append(f"{chunk[0]}{' '.join(used)} : {typ}{chunk[-1]}")
    return " ".join(binders)


def parse_state(state, hyp_names: tuple[str, ...]) -> Optional[StateView]:
    raw = getattr(state, "pp", str(state))
    if raw.count("⊢") != 1:
        return None
    before, sep, after = raw.partition("⊢")
    if not sep:
        return None
    hypotheses = {}
    for line in before.splitlines():
        line = line.strip()
        for name in hyp_names:
            prefix = f"{name} : "
            if line.startswith(prefix):
                hypotheses[name] = " ".join(line[len(prefix):].split())
    return StateView(hypotheses, " ".join(after.split()), raw)


def clean_delta(text: str) -> bool:
    return "?m." not in text and "case " not in text


def valid_name(name: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*(\.[A-Za-z_][A-Za-z0-9_']*)*", name))


def candidate_names(traced_theorems, target_name: str, limit: int) -> list[str]:
    names = []
    for theorem in traced_theorems:
        full_name = theorem.theorem.full_name
        if full_name != target_name:
            names.append(full_name)
        try:
            names.extend(theorem.get_premise_full_names())
        except Exception:
            pass
    uniq = []
    for name in names:
        if name != target_name and valid_name(name) and name not in uniq:
            uniq.append(name)
    return uniq[:limit]


def apply_candidates(names: list[str]) -> list[str]:
    variants = []
    for name in names:
        variants.extend([name, f"{name}.mp", f"{name}.mpr"])
    return list(dict.fromkeys(variants))


def mine_with_dojo(traced_theorem, ctx: Context, candidates: list[str]):
    hyp_names = tuple(h.name for h in ctx.hypotheses)
    condition_rw, goal_rw, apply_invocable = [], [], []
    attempts = {"condition_rw": 0, "goal_rw": 0, "goal_apply": 0}
    seen = set()

    with Dojo(traced_theorem.theorem) as (dojo, init_state):
        base = parse_state(init_state, hyp_names)
        if base is None:
            raise RuntimeError("Cannot parse initial Dojo state")

        for candidate in candidates:
            for hyp_index, hyp in enumerate(ctx.hypotheses):
                attempts["condition_rw"] += 1
                tactic = f"rw [{candidate}] at {hyp.name}"
                result = dojo.run_tac(init_state, tactic)
                view = parse_state(result, hyp_names) if isinstance(result, TacticState) else None
                new_prop = None if view is None else view.hypotheses.get(hyp.name)
                key = ("condition_rw", hyp.name, hyp.prop, new_prop, candidate)
                if view and new_prop and clean_delta(new_prop) and view.goal == base.goal and new_prop != hyp.prop and key not in seen:
                    seen.add(key)
                    condition_rw.append({
                        "kind": "condition_rw",
                        "candidate": candidate,
                        "dojo_tactic": tactic,
                        "hypothesis": hyp.name,
                        "hyp_index": hyp_index,
                        "old": hyp.prop,
                        "new": new_prop,
                        "bridge_direction": "new_condition -> old_condition",
                    })

            attempts["goal_rw"] += 1
            tactic = f"rw [{candidate}]"
            result = dojo.run_tac(init_state, tactic)
            view = parse_state(result, hyp_names) if isinstance(result, TacticState) else None
            key = ("goal_rw", ctx.goal, None if view is None else view.goal, candidate)
            if view and clean_delta(view.goal) and view.hypotheses == base.hypotheses and view.goal != ctx.goal and key not in seen:
                seen.add(key)
                goal_rw.append({
                    "kind": "goal_rw",
                    "candidate": candidate,
                    "dojo_tactic": tactic,
                    "old": ctx.goal,
                    "new": view.goal,
                    "bridge_direction": "old_goal -> new_goal",
                })

        for candidate in apply_candidates(candidates):
            attempts["goal_apply"] += 1
            tactic = f"apply {candidate}"
            result = dojo.run_tac(init_state, tactic)
            view = parse_state(result, hyp_names) if isinstance(result, TacticState) else None
            if view is None or not clean_delta(view.goal) or view.goal == ctx.goal or view.goal in base.hypotheses.values():
                continue
            key = ("goal_apply", ctx.goal, view.goal, candidate)
            if key in seen:
                continue
            seen.add(key)
            apply_invocable.append({
                "kind": "goal_apply_precondition",
                "candidate": candidate,
                "dojo_tactic": tactic,
                "old": ctx.goal,
                "new_subgoal": view.goal,
                "bridge_direction": "new_subgoal -> old_goal",
                "state_after": view.raw,
            })

    return attempts, condition_rw, goal_rw, apply_invocable


def safe_label(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9_]+", "_", text).strip("_")[:80]


def probe_text(ctx: Context, condition_rw: list[dict], goal_rw: list[dict], apply_invocable: list[dict]) -> str:
    blocks = []
    for idx, delta in enumerate(condition_rw):
        params = params_for(ctx, [delta["old"], delta["new"]])
        lines = [
            f"theorem xt_mined_probe_cond_{idx}_{safe_label(delta['candidate'])} {params} (hcond : {delta['new']}) :",
            f"    {delta['old']} := by",
            f"  rw [{delta['candidate']}]",
            "  exact hcond",
        ]
        blocks.append("\n".join(lines))
    for idx, delta in enumerate(goal_rw):
        params = params_for(ctx, [delta["old"], delta["new"]])
        lines = [
            f"theorem xt_mined_probe_goal_{idx}_{safe_label(delta['candidate'])} {params} (hgoal : {delta['old']}) :",
            f"    {delta['new']} := by",
            f"  rw [{delta['candidate']}] at hgoal",
            "  exact hgoal",
        ]
        blocks.append("\n".join(lines))
    for idx, delta in enumerate(apply_invocable):
        params = params_for(ctx, [delta["old"], delta["new_subgoal"]])
        lines = [
            f"theorem xt_mined_probe_apply_{idx}_{safe_label(delta['candidate'])} {params} (hbridge : {delta['new_subgoal']}) :",
            f"    {delta['old']} := by",
            f"  apply {delta['candidate']}",
            "  all_goals assumption",
        ]
        blocks.append("\n".join(lines))
    return "\n\n".join(blocks)


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
    limit = int(sys.argv[6]) if len(sys.argv) > 6 else 80
    started = time.time()
    result = {"mode": "alchemy_style_bridge_mining", "repo_path": str(repo_path), "commit": commit, "parent": theorem_name, "ok": False}

    try:
        theorem = find_theorem(repo_path, commit, theorem_name, file_path)
        ctx = theorem_context(theorem)
        traced_theorems = traced_theorems_in_file(repo_path, commit, file_path)
        candidates = candidate_names(traced_theorems, theorem_name, limit)
        attempts, condition_rw, goal_rw, apply_invocable = mine_with_dojo(theorem, ctx, candidates)
        block = probe_text(ctx, condition_rw, goal_rw, apply_invocable)
        probe_proc = append_and_build(repo_path, file_path, block, 600) if block else None
        probe_returncode = None if probe_proc is None else probe_proc.returncode

        result.update({
            "candidate_count": len(candidates),
            "candidates": candidates,
            "attempts": attempts,
            "condition_rw_count": len(condition_rw),
            "goal_rw_count": len(goal_rw),
            "goal_apply_invocable_count": len(apply_invocable),
            "probe_build_returncode": probe_returncode,
            "probe_build_output_tail": None if probe_proc is None else probe_proc.stdout[-4000:],
            "context": {
                "params": list(ctx.params),
                "hypotheses": [{"name": hyp.name, "prop": hyp.prop} for hyp in ctx.hypotheses],
                "goal": ctx.goal,
            },
            "condition_deltas": condition_rw,
            "goal_deltas": goal_rw,
            "apply_invocable": apply_invocable,
        })
        result["ok"] = bool(condition_rw or goal_rw) and probe_returncode == 0
    except Exception as exc:
        result.update({"error_type": type(exc).__name__, "error": repr(exc), "traceback": traceback.format_exc()})

    result["seconds"] = round(time.time() - started, 3)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k not in {"condition_deltas", "goal_deltas", "apply_invocable", "candidates"}}, indent=2, ensure_ascii=False))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
