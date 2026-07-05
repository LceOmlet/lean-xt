from pathlib import Path
import subprocess
from types import SimpleNamespace

from lean_dojo import LeanGitRepo, trace
from lean_dojo.data_extraction.traced_data import TracedFile


def _head(repo_path: Path) -> str:
    proc = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo_path, text=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    return proc.stdout.strip() if proc.returncode == 0 else ""


def _traced_file(root: Path, ast_path: Path, repo):
    traced_file = TracedFile.from_traced_file(root, ast_path, repo)
    traced_file.traced_repo = SimpleNamespace(repo=repo, dependencies={})
    return traced_file


def _ast_candidates(repo_path: Path, commit: str, file_path: Path, repo):
    repo_path = repo_path.resolve()
    cache_root = Path.home() / ".cache" / "lean_dojo" / f"gitpython-{repo_path.name}-{commit}" / repo_path.name
    local_ast = repo_path / ".lake" / "build" / "ir" / file_path.with_suffix(".ast.json")
    cached_ast = cache_root / ".lake" / "build" / "ir" / file_path.with_suffix(".ast.json")
    if _head(repo_path) == commit and local_ast.exists():
        yield _traced_file(repo_path, local_ast, repo)
    if cached_ast.exists():
        yield _traced_file(cache_root, cached_ast, repo)


def find_theorem(repo_path: Path, commit: str, theorem_name: str, file_path: Path):
    repo_path = repo_path.resolve()
    repo = LeanGitRepo(str(repo_path), commit)
    for traced_file in _ast_candidates(repo_path, commit, file_path, repo):
        for theorem in traced_file.get_traced_theorems():
            if theorem.theorem.full_name == theorem_name:
                return theorem

    traced_repo = trace(repo, build_deps=False)
    for theorem in traced_repo.get_traced_theorems():
        if theorem.theorem.full_name == theorem_name:
            return theorem
    raise ValueError(f"Theorem not found: {theorem_name}")


def traced_theorems_in_file(repo_path: Path, commit: str, file_path: Path):
    repo_path = repo_path.resolve()
    repo = LeanGitRepo(str(repo_path), commit)
    for traced_file in _ast_candidates(repo_path, commit, file_path, repo):
        return list(traced_file.get_traced_theorems())

    traced_repo = trace(repo, build_deps=False)
    return [theorem for theorem in traced_repo.get_traced_theorems() if Path(theorem.file_path) == file_path]
