# MatrixFoundations

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Lean](https://img.shields.io/badge/Lean-v4.29.1-blue.svg)](https://github.com/leanprover/lean4)
[![Mathlib](https://img.shields.io/badge/mathlib-v4.29.1-blue.svg)](https://github.com/leanprover-community/mathlib4)
[![CI](https://github.com/dangoodface/matrix-foundations/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/dangoodface/matrix-foundations/actions/workflows/lean_action_ci.yml)

A Lean 4 / mathlib formalization sitting at the intersection of textbook matrix algebra, minimal-basis obstruction theory, and algebraic complexity. The headline result is, to my knowledge, the **first formal proof of an EML depth lower bound**.

```lean
theorem depth_global_xy_ge_four :
    ¬ ∃ (T : MinimalBasis.Term EmlBasis 2), T.depth ≤ 3 ∧
        T.representsGlobally (fun v : Fin 2 → ℝ => v 0 + v 1)
```

Read: *no depth-≤ 3 tree over Odrzywołek's `eml(x, y) = exp(x) − log(y)` operator globally represents the addition function `(x, y) ↦ x + y`.*

## Status — paused, open for adoption

This repository is the publicly preserved state of a solo formalization effort that has run for several weeks and is now being put on hold. The owner is moving on to other things. **It is published in the hope that the framework, the theorems, and the partial Khovanskii infrastructure are useful to someone**: a graduate student looking for a tractable formalization project, a mathlib contributor interested in the covering-space / monodromy track, or anyone curious about obstruction theory in Lean.

The codebase is in a clean state — `Sheffer/Examples/Eml.lean` is file-level sorry-free, the build is green, and the two remaining axioms are clearly documented below. Open issues / PRs welcome; the license is Apache-2.0 so feel free to fork.

## What is proved

| Theorem | File | Status |
|---|---|---|
| `depth_global_xy_ge_four` — `v_0 + v_1` requires EML depth ≥ 4 | `Sheffer/Examples/Eml.lean` | **proved** (0 sorry) |
| `no_eml_term_represents_quintic` — no EML-term globally represents the generic quintic root | `Sheffer/Examples/Eml.lean` | proved subject to two analytic axioms (see below) |
| `x_pow_9_not_representable_at_depth_3` — depth-3 polynomial-activation networks of degree ≤ 2 cannot represent `x⁹` | `Sheffer/Examples/PolyAct.lean` | **proved** (0 axioms) |
| `sheffer_complete` — every Boolean function on `n` inputs is NAND-expressible via DNF | `Sheffer/Examples/Nand.lean` | **proved** (0 axioms) |
| `permanent_in_VNP_via_arity` — `perm` is in VNP via Ryser's formula, explicit circuit size `2n² + 5n + 2` | `Sheffer/Foundations/PermanentVNP.lean` | **proved** (0 axioms) |

The minimal-basis obstruction theory in `Sheffer/Core.lean` is the framework that ties the EML, NAND, and PolyAct examples together. The arithmetic-circuit / VP / VNP foundations in `Sheffer/Foundations/{ArithCircuit, PermanentVNP, PolyActVP}.lean` follow Bürgisser–Clausen–Shokrollahi 1997 §5.2 (generalised to arbitrary input-variable types).

## Layout

```
MatrixFoundations/
├── Basic.lean           — basics
├── MatMul.lean          — composition → matrix multiplication → algebra laws → change of basis
├── Eml.lean             — early exploratory EML file; superseded by Sheffer/Examples/Eml.lean
├── JunkValueTest.lean   — meta-claim about mathlib's junk-value convention
└── Sheffer/
    ├── Core.lean                                — minimal-basis obstruction-theory framework
    ├── Examples/
    │   ├── Eml.lean                             — quintic-root non-expressibility theorem
    │   │                                          + the depth ≥ 4 lower bound for x + y
    │   ├── Nand.lean                            — Sheffer 1913 functional completeness via DNF
    │   └── PolyAct.lean                         — polynomial-activation networks
    └── Foundations/
        ├── MonodromyGroup.lean                  — monodromy as a group action
        ├── MultivaluedAnalytic.lean             — covering maps / per-sheet value functions
        ├── SolvableMonodromy.lean               — concrete `hasSolvableMonodromy`
        ├── ArithCircuit.lean                    — arithmetic circuits, VP, VNP
        ├── PermanentVNP.lean                    — `perm ∈ VNP` via Ryser
        └── PolyActVP.lean                       — connects PolyAct to VP
```

## Building

You need a working Lean 4 install — see the [Lean installation instructions](https://leanprover-community.github.io/get_started.html) (Regular install).

```sh
lake exe cache get   # fetch the mathlib build cache
lake build           # build the project
```

On a clean machine with a warm cache, expect 5–15 minutes for the first build, after which incremental builds are fast.

## Where this paused — work for future researchers

The H1.4 depth lower bound was the natural closure for this phase of the project. The next planned target was the Khovanskii descent — discharging the first of the two remaining axioms in `Sheffer/Examples/Eml.lean`. The opening sub-target was scoped and dispatched, the framework scaffolding is in place with theorem statements written and proof bodies left as `sorry`, but no full discharge landed before the pause. The section below is everything someone picking this up would need to resume.

### The two remaining axioms

Both live in `Sheffer/Examples/Eml.lean`:

- **`eml_preserves_solvableMonodromy`** — Khovanskii's lemma. If `f` and `g` have solvable monodromy, so does `eml(f, g)`. A Lean discharge wants covering-space / Riemann-surface monodromy infrastructure in mathlib that does not yet exist. This was the immediate next target.
- **`quinticRoot_has_S5_monodromy_universal`** — the classical Galois fact that the generic quintic root function has `S₅` monodromy. Standard analytic-Galois material.

The const and var cases of the EML structural induction were originally part of a four-axiom set; they are now theorems, discharged against the concrete `hasSolvableMonodromy` predicate in `Sheffer/Foundations/SolvableMonodromy.lean`. The two axioms above are what survive.

### Khovanskii roadmap

The infrastructure for the descent is already on disk: `MonodromyGroup.lean` defines monodromy as a group action, `MultivaluedAnalytic.lean` builds the covering-map / per-sheet machinery, and `SolvableMonodromy.lean` gives the concrete predicate plus statement-level theorem skeletons (with `sorry` proof bodies) for each sub-target. What remains, in increasing order of difficulty:

1. **`sub_solvableMonodromy`** — preservation under pullback by subtraction. Statement skeleton in place at `SolvableMonodromy.lean`; proof body is `sorry`. Was the next dispatched target (~100–150 lines, medium-hard).
2. **`log_solvableMonodromy`** — preservation under composition with `log`. The hard one (~100–150 lines, wants universal-cover infrastructure not yet in mathlib).
3. **Final Khovanskii closure** — composes the two above into `eml_preserves_solvableMonodromy` proper. The statement skeleton with a `sorry` proof body lives alongside the axiom version (~50 lines once the pieces land).

`MultivaluedAnalytic.lean` also contains three further `sorry`-marked scaffolds (local-triviality and lift lemmas) supporting the descent. None are blocking the headline files.

Whoever wants to take this on: the cleanest first step is `sub_solvableMonodromy` — the most contained of the three, and landing it discharges one of the two remaining axioms once the Khovanskii closure factors through. A natural parallel track is upstreaming the local `MonodromyGroup` / `MultivaluedAnalytic` material into mathlib proper.

### Other open scaffolding

- `MatrixFoundations/Eml.lean` (the early exploratory file, predates the framework) contains one legacy `sorry` for the original Khovanskii–Stylewarning theorem statement. It is superseded by the framework version in `Sheffer/Examples/Eml.lean` and can be deleted once anyone confirms nothing depends on it.
- `Sheffer/Foundations/ArithCircuit.lean` has one private definitional-lemma `sorry` (`evalBoolSubstitute_m_zero` at line 295). The arithmetic-circuit / VP / VNP results still go through; closing the lemma is a straightforward `Sum.elim` / `Fin 0` exercise.

Open an issue, or just fork — the license is Apache-2.0.

## References

- Odrzywołek, *EML and its identities*, [arXiv:2603.21852](https://arxiv.org/abs/2603.21852), April 2026 — source for the `eml(x, y) = exp(x) − log(y)` operator and the depth-bound conjecture proved here.
- Sheffer, *A set of five independent postulates for Boolean algebras*, Trans. Amer. Math. Soc. 14 (1913), 481–488 — functional completeness of NAND.
- Ryser, *Combinatorial Mathematics*, Carus Math. Monograph 14 (1963) — the permanent-as-Boolean-cube-sum formula.
- Valiant, *Completeness classes in algebra*, STOC 1979 — VP / VNP and the permanent-in-VNP result.
- Bürgisser, Clausen, Shokrollahi, *Algebraic Complexity Theory*, Springer 1997 — the §5.2 development of arithmetic circuits we follow.
- Khovanskii, *Fewnomials*, AMS 1991 / *Topological Galois theory*, Springer 2014 — the analytic-Galois framework behind the EML obstruction.

## License

Apache-2.0. See [`LICENSE`](LICENSE).
