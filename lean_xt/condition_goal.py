from dataclasses import dataclass
from typing import Optional, Sequence


@dataclass(frozen=True)
class ConditionBridge:
    old_hypothesis: str
    new_hypotheses: Sequence[str]
    tactic: str


@dataclass(frozen=True)
class GoalBridge:
    new_goal: str
    tactic: str


def _decl_nodes(traced_theorem, raw_string=False):
    from lean_dojo.data_extraction.ast import (
        AtomNode,
        CommandDeclidNode,
        CommandDeclmodifiersNode,
        CommandDeclsigNode,
        CommandDeclvaleqnsNode,
        CommandDeclvalsimpleNode,
        CommandWherestructinstNode,
    )

    nodes = {}
    proof_classes = (CommandDeclvalsimpleNode, CommandDeclvaleqnsNode, CommandWherestructinstNode)

    def visit(node, _):
        if isinstance(node, CommandDeclidNode):
            nodes["id"] = node
        elif isinstance(node, CommandDeclsigNode):
            nodes["decl"] = node
        elif isinstance(node, proof_classes):
            nodes["proof"] = node

    ast = traced_theorem.ast
    ast.traverse_preorder(visit, node_cls=None)
    if not raw_string:
        return nodes["id"], nodes["decl"], nodes["proof"]

    id_node, decl_node, proof_node = nodes["id"], nodes["decl"], nodes["proof"]
    children = ast.children
    if isinstance(children[0], AtomNode):
        keyword_start = children[0].start
    elif isinstance(children[0], CommandDeclmodifiersNode):
        keyword_start = children[1].children[0].start
    else:
        keyword_start = ast.start
    return (
        id_node,
        decl_node,
        proof_node,
        id_node.lean_file[id_node.start:id_node.end],
        decl_node.lean_file[keyword_start:decl_node.end],
        proof_node.lean_file[proof_node.start:proof_node.end],
    )


def _hypotheses(statement_node):
    from lean_dojo.data_extraction.ast import IdentNode, NullNode, TermExplicitbinderNode

    names = []
    binders = []
    in_binder = False

    def visit(node, _):
        nonlocal in_binder
        if isinstance(node, TermExplicitbinderNode):
            if in_binder:
                return True
            in_binder = True
            name_node = node.children[1]
            type_node = node.children[2]
            names.append([c.raw_val for c in name_node.children if isinstance(c, IdentNode) and c.raw_val != "_"])
            binders.append(statement_node.lean_file[name_node.start:type_node.end])
            in_binder = False
            return True
        return False

    root = statement_node.children[0]
    assert isinstance(root, NullNode)
    root.traverse_preorder(visit, node_cls=None)
    return names, binders


def _conclusion(statement_node):
    from lean_dojo.data_extraction.ast import TermTypespecNode

    found = {}

    def visit(node, _):
        if isinstance(node, TermTypespecNode):
            child = node.children[1]
            found["text"] = statement_node.lean_file[child.start:child.end]

    statement_node.traverse_preorder(visit, node_cls=None)
    return found["text"]


def _decl_keyword_and_name(target_theorem):
    from lean_dojo.data_extraction.ast import AtomNode, CommandDeclmodifiersNode

    ast = target_theorem.ast
    children = ast.children
    if isinstance(children[0], AtomNode):
        keyword_start, id_end = children[0].start, children[1].end
    elif isinstance(children[0], CommandDeclmodifiersNode):
        group = children[1]
        keyword_start, id_end = group.children[0].start, group.children[1].end
    else:
        raise ValueError("Unsupported theorem declaration shape")
    return ast.lean_file[keyword_start:id_end]


def _last_replace(text: str, old: str, new: str) -> str:
    idx = text.rfind(old)
    if idx == -1:
        raise ValueError(f"Cannot find text to replace: {old}")
    return text[:idx] + new + text[idx + len(old):]


def _rename_decl(target_theorem, statement: str, child_name: str) -> str:
    old_decl = _decl_keyword_and_name(target_theorem)
    return statement.replace(old_decl, f"{old_decl.split()[0]} {child_name}", 1)


def _replace_hypothesis(target_theorem, statement: str, bridge: ConditionBridge) -> str:
    statement_node = _decl_nodes(target_theorem)[1]
    for names, old_hypo in zip(*_hypotheses(statement_node)):
        if bridge.old_hypothesis in names:
            old_binder = f"({old_hypo})"
            new_binders = " ".join(f"({hypo})" for hypo in bridge.new_hypotheses)
            if old_binder not in statement:
                raise ValueError(f"Cannot locate old hypothesis binder: {old_binder}")
            return statement.replace(old_binder, new_binders, 1)
    raise ValueError(f"Unknown explicit hypothesis: {bridge.old_hypothesis}")


def _replace_goal(target_theorem, statement: str, bridge: GoalBridge) -> str:
    old_goal = _conclusion(_decl_nodes(target_theorem)[1])
    return _last_replace(statement, old_goal, bridge.new_goal)


def _proof(parent_name: str, condition: Optional[ConditionBridge], goal: Optional[GoalBridge]) -> str:
    lines = [":= by"]
    if goal is not None:
        lines.append(f"  {goal.tactic}")
    lines.append(f"  apply {parent_name}")
    if condition is None:
        lines.append("  all_goals assumption")
    else:
        lines.extend(["  all_goals first", "    | assumption", f"    | {condition.tactic}"])
    return "\n".join(lines)


def modify_theorem_condition_goal(
    target_theorem,
    child_name: str,
    condition: Optional[ConditionBridge] = None,
    goal: Optional[GoalBridge] = None,
    parent_name: Optional[str] = None,
) -> dict:
    if condition is None and goal is None:
        raise ValueError("At least one condition or goal bridge is required")

    _, _, _, _, statement, _ = _decl_nodes(target_theorem, raw_string=True)
    if condition is not None:
        statement = _replace_hypothesis(target_theorem, statement, condition)
    if goal is not None:
        statement = _replace_goal(target_theorem, statement, goal)
    statement = _rename_decl(target_theorem, statement, child_name)

    parent_name = parent_name or target_theorem.theorem.full_name
    return {
        "child_name": child_name,
        "parent_name": parent_name,
        "mutation_type": (
            "condition_strengthen_goal_weaken" if condition and goal
            else "condition_strengthen" if condition
            else "goal_weaken"
        ),
        "condition_delta": None if condition is None else {
            "old_hypothesis": condition.old_hypothesis,
            "new_hypotheses": list(condition.new_hypotheses),
            "bridge_tactic": condition.tactic,
        },
        "goal_delta": None if goal is None else {
            "new_goal": goal.new_goal,
            "bridge_tactic": goal.tactic,
        },
        "text": statement.rstrip() + " " + _proof(parent_name, condition, goal),
    }
