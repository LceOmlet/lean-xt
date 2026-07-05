from pathlib import Path
from types import SimpleNamespace

from lean_dojo import LeanGitRepo, trace
from lean_dojo.data_extraction.traced_data import TracedFile


def find_theorem(repo_path: Path, commit: str, theorem_name: str, file_path: Path):
    repo_path = repo_path.resolve()
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
