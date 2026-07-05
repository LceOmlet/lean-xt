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
