import json
import subprocess
import sys
import time
import traceback
from pathlib import Path
from types import SimpleNamespace

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from lean_dojo import LeanGitRepo, trace
from lean_dojo.data_extraction.traced_data import TracedFile

from lean_xt import ConditionBridge, GoalBridge, modify_theorem_condition_goal


def find_theorem(repo_path: Path, commit: str, theorem_name: str, file_path: Path):
    cache_root = Path.home() / ".cache" / "lean_dojo" / f"gitpython-{repo_path.name}-{commit}" / repo_path.name
    cached_ast = cache_root / ".lake" / "build" / "ir" / file_path.with_suffix(".ast.json")
    repo = LeanGitRepo(str(repo_path), commit)
    if cached_ast.exists():
        traced_file = TracedFile.from_traced_file(cache_root, cached_ast, repo)
        traced_file.traced_repo = SimpleNamespace(repo=repo, dependencies={})
        for theorem in traced_file.get_traced_theorems():
            if theorem.theorem.full_name == theorem_name:
                return theorem

    traced_repo = trace(repo, build_deps=False)
    for theorem in traced_repo.get_traced_theorems():
        if theorem.theorem.full_name == theorem_name:
            return theorem
    raise ValueError(f"Theorem not found: {theorem_name}")


def main() -> int:
    repo_path = Path(sys.argv[1]).resolve()
    commit = sys.argv[2]
    theorem_name = sys.argv[3]
    file_path = Path(sys.argv[4])
    output_path = Path(sys.argv[5])
    started = time.time()
    result = {"repo_path": str(repo_path), "commit": commit, "parent": theorem_name, "file_path": str(file_path), "ok": False}

    try:
        theorem = find_theorem(repo_path, commit, theorem_name, file_path)
        condition = ConditionBridge(
            old_hypothesis="hab",
            new_hypotheses=["hrel : IsRelPrime a b"],
            tactic="exact (Nat.coprime_iff_isRelPrime).2 hrel",
        )
        goal = GoalBridge(
            new_goal="forall {n : Nat}, n ∈ a.divisors.filter IsPrimePow -> n ∈ b.divisors.filter IsPrimePow -> False",
            tactic="apply Finset.disjoint_left.mp",
        )
        variants = [
            modify_theorem_condition_goal(theorem, "alchemy_tree_t0_condition_strengthened", condition=condition),
            modify_theorem_condition_goal(theorem, "alchemy_tree_t0_goal_weakened", goal=goal),
            modify_theorem_condition_goal(theorem, "alchemy_tree_t0_condition_strengthened_goal_weakened", condition=condition, goal=goal),
        ]

        target_file = repo_path / file_path
        original = target_file.read_text(encoding="utf-8")
        target_file.write_text(original.rstrip() + "\n\n" + "\n\n".join(v["text"] for v in variants) + "\n", encoding="utf-8")
        try:
            proc = subprocess.run(["lake", "build"], cwd=repo_path, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        finally:
            target_file.write_text(original, encoding="utf-8")

        result.update({
            "build_returncode": proc.returncode,
            "build_output_tail": proc.stdout[-4000:],
            "variants": variants,
            "ok": proc.returncode == 0,
        })
    except Exception as exc:
        result.update({"error_type": type(exc).__name__, "error": repr(exc), "traceback": traceback.format_exc()})

    result["seconds"] = round(time.time() - started, 3)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
