# MatrixFoundations

A Lean 4 / mathlib formalization. Three threads:

1. **Textbook matrix algebra** — composition of linear maps, the matrix-multiplication formula, change of basis. Self-contained, zero axioms.
2. **The Sheffer framework and the EML obstruction** — a minimal-basis obstruction theory, instantiated for Odrzywołek's exp-minus-log operator `eml(x, y) = exp(x) − log(y)`. Includes the first formal proof of an EML depth lower bound, plus a fully constructive analogue for polynomial-activation networks.
3. **Algebraic-complexity-theory foundations** — arithmetic circuits, the VP / VNP classes, and `perm ∈ VNP` via Ryser's formula.

Built against `mathlib v4.29.1` / `leanprover/lean4:v4.29.1`.

## Headline results

| Theorem | File | Status |
|---|---|---|
| `depth_global_xy_ge_four` — `v_0 + v_1` requires EML depth ≥ 4 | `Sheffer/Examples/Eml.lean` | proved (0 sorry) |
| `quintic_not_in_eml_basis` — no EML-term globally represents the generic quintic root | `Sheffer/Examples/Eml.lean` | proved subject to two analytic axioms (Khovanskii's lemma + classical S₅ Galois fact) |
| `x_pow_9_not_representable_at_depth_3` — depth-3 polynomial-activation networks of degree ≤ 2 cannot represent `x⁹` | `Sheffer/Examples/PolyAct.lean` | proved (0 axioms) |
| `sheffer_complete` — every Boolean function is NAND-expressible via DNF | `Sheffer/Examples/Nand.lean` | proved (0 axioms) |
| `permanent_in_VNP` — `perm` is in VNP via Ryser's formula, explicit circuit size `2n² + 5n + 2` | `Sheffer/Foundations/PermanentVNP.lean` | proved (0 axioms) |

## Layout

```
MatrixFoundations/
├── Basic.lean           — scratch / basics
├── MatMul.lean          — composition → matrix multiplication → algebra laws → change of basis
├── Eml.lean             — early EML exploration (one legacy sorry placeholder)
├── JunkValueTest.lean   — meta-claim about mathlib's junk-value convention
└── Sheffer/
    ├── Core.lean                              — minimal-basis obstruction-theory framework
    ├── Examples/
    │   ├── Eml.lean                           — quintic-root non-expressibility +
    │   │                                        H1.4 depth lower bound for x + y
    │   ├── Nand.lean                          — Sheffer 1913 functional completeness
    │   └── PolyAct.lean                       — polynomial-activation networks
    └── Foundations/
        ├── MonodromyGroup.lean                — monodromy as a group action
        ├── MultivaluedAnalytic.lean           — covering map / per-sheet value functions
        ├── SolvableMonodromy.lean             — concrete `hasSolvableMonodromy`
        ├── ArithCircuit.lean                  — arithmetic circuits, VP, VNP
        ├── PermanentVNP.lean                  — `perm ∈ VNP` via Ryser
        └── PolyActVP.lean                     — connects PolyAct to VP
```

## Building

```sh
lake exe cache get   # download the mathlib build cache
lake build
```

Expect 5–15 minutes on a clean machine. Build is clean (no `sorry` in the headline files apart from the two analytic placeholders documented below).

## Axioms

Across the whole library, the remaining axioms are:

- `eml_preserves_solvableMonodromy` — Khovanskii's lemma: solvable-monodromy is preserved under EML composition. A Lean discharge requires covering-space monodromy infrastructure in mathlib; this is the next major work item.
- `quinticRoot_has_S5_monodromy_universal` — the classical Galois fact that the generic quintic root has `S₅` monodromy.

Both are theorems with established proofs in the analytic-Galois literature; they are axiomatized in the Lean source to let the surrounding structural proof go through.

## License

Apache-2.0. See `LICENSE`.
