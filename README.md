# lean-xt

`lean-xt` contains Lean theorem-change utilities for verified condition and goal mutations.

The current module implements three bridge-witness mutations:

| Mutation | Meaning |
|---|---|
| `condition_strengthen` | replace an old hypothesis `P` with new hypotheses `P'` plus a Lean tactic proving `P' -> P` |
| `goal_weaken` | replace an old goal `Q` with a new goal `Q'` plus a Lean tactic proving `Q -> Q'` |
| `condition_strengthen_goal_weaken` | combine both bridges in one child theorem |

Each generated edge records `parent_name`, `mutation_type`, `condition_delta`, `goal_delta`, and the generated Lean theorem text. Correctness is delegated to Lean: generated children are only accepted after `lake build`.

## Validation

The validation script uses a real Mathlib-based Lean project and LeanDojo traced theorem ASTs:

```bash
python scripts/validate_condition_goal_mutation.py \
  /path/to/depth3_lean420_clean \
  bb1fe98b37ed2780ce69867e9be9f59a45a79782 \
  alchemy_tree_t0 \
  AlchemyTree/Depth3.lean \
  results/condition_goal_mutation_test.json
```

The latest validation generated and verified three children from `alchemy_tree_t0`:

- condition strengthened: `hab : a.Coprime b` -> `hrel : IsRelPrime a b`
- goal weakened: `Disjoint ...` -> pairwise non-membership contradiction
- combined condition-strengthening plus goal-weakening

Result: `lake build` completed successfully.

## v1 interrupt-following / theorem-update benchmark generator

The v1 benchmark generator is `scripts/expand_tactic_bridge_forest.py`.
It builds verified theorem-update trees for interrupt-following experiments:

```text
T0 original theorem
 -> interrupt: update condition and/or goal
 -> child theorem with Lean-verified bridge proof
 -> repeat to depth 3
```

This version allows only the Lean tactics needed for theorem-update bridges:
`apply`, `exact`, and `assumption`.  Each candidate bridge is first emitted as a
Lean probe theorem and accepted only after `lake build`; the expanded forest is
then verified again with `lake build`.

Latest verified run:

| Metric | Value |
|---|---:|
| Mode | `apply_exact_assumption` |
| Bridge probes | 25 |
| Trees | 100 |
| Depth | 3 |
| Verified nodes / edges | 1326 / 1326 |
| Leaf count range | 2-12 |
| Empty delta edges | 0 |
| Build result | success |

Compared with the apply-only generator, this v1 line increases goal-change
coverage from 3 to 10 goal bridge schemas while keeping every edge Lean
verified.
