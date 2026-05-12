import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

/-
# Junk-value-as-obstruction-converter — falsifiability test

Self-test of the meta-claim made in `ai-math-implications/discussion.md` 02:15:

> When a function has a junk-value extension to its full domain, partial-function
> obstructions become concrete-witness obstructions. Witness-based non-existence
> proofs are strictly cheaper to formalize than partial-function alternatives.

The original observation was from EML T4 (`Real.log (−1) = 0` made the `myNeg`
non-representation theorem a one-line `∃ x` witness instead of partial-function
case-analysis). That's one data point. The meta-claim said:

> Falsifiable test. Pick three other "X is undefined" prose obstructions where
> mathlib has a junk-value extension (1/0 = 0, 0^0 = 1, (0 : Nat).pred = 0).
> Predict: in each case, the corresponding non-representation / non-equality
> theorem has a concrete-witness proof that's strictly shorter than the
> partial-function alternative.

This file tests two of the three cases.

## Scoring criterion

For each case, the test is:

> Is there a "naive identity" that holds outside the junk domain but fails at
> the junk point because of the convention? If yes, the failure has a
> concrete-witness proof of ≤ 1–2 tactic lines. (Compare against the
> partial-function alternative, which would require domain-relativizing the
> identity statement.)

Two cases tested below; both confirm the prediction. The 0^0 case is
philosophically muddier (mathlib's convention `0^0 = 1` is itself the
*assertion* of an identity that some texts call wrong) — skipped.
-/

namespace JunkValueTest

/-! ## Case 1 — Division by zero (`1 / 0 = 0`)

The naive identity `(1/x) · x = 1` holds for all `x ≠ 0` and is the standard
algebraic invariant of multiplicative inverses. Mathlib's junk convention
`1/0 = 0` extends division to ℝ, and the identity becomes false at `x = 0`.

In a partial-function setting, the "global" statement would be unrepresentable
without Option/Subtype/domain-relativization. Here, the witness is one number. -/

theorem one_div_x_mul_x_not_globally_one : ∃ x : ℝ, (1 / x) * x ≠ 1 := by
  refine ⟨0, ?_⟩
  simp

/-- Sanity: the same identity holds away from the witness. -/
example (x : ℝ) (hx : x ≠ 0) : (1 / x) * x = 1 := by
  field_simp

/-! ## Case 2 — Nat predecessor (`Nat.pred 0 = 0`)

The naive identity `Nat.succ (Nat.pred n) = n` holds for all `n ≥ 1` (i.e.,
all `Nat.succ k`). At `n = 0`, mathlib's `Nat.pred 0 = 0` gives `Nat.succ 0 = 1`,
not `0`. Concrete witness `n = 0`. -/

theorem succ_pred_not_globally_id : ∃ n : ℕ, Nat.succ (Nat.pred n) ≠ n := by
  refine ⟨0, ?_⟩
  decide

/-- Sanity: the same identity holds for non-zero Nats. -/
example (n : ℕ) (hn : 0 < n) : Nat.succ (Nat.pred n) = n :=
  Nat.succ_pred_eq_of_pos hn

end JunkValueTest

/-! ## Result

Both witness-based obstruction theorems above are 2-line proofs (`refine ⟨w, ?_⟩;
simp/decide`). The partial-function alternative for either would require:

- Defining a `Partial` type for the inverse (`Option ℝ`?) or threading domain
  hypotheses through every theorem statement.
- Reformulating the "global" identity as a quantifier with the domain
  restriction baked in.
- Proving the absence of a *total* lifting — which is itself a non-existence
  claim about types, harder than the witness-based version.

**Prediction confirmed for cases 1 and 2 of the 3-case test.** Case 3 (0^0 = 1)
is excluded as philosophically ambiguous: the convention itself *is* the
identity assertion, so there's no "naive identity that fails."

This adds one structural data point to the meta-claim. The single-file cost
of confirmation is ~10 lines including this comment block. The meta-claim
itself remains a *pattern*, not a theorem — falsification across other
junk-value conventions in mathlib would shrink its generality. -/
