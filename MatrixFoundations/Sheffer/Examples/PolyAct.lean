/-
# Sheffer.Examples.PolyAct — polynomial-activation networks (Target A)

The AI-architectural, negative-obstruction example. Single arity-1 operator
that applies a polynomial of degree ≤ k to one real input. Function class:
polynomials of degree ≤ k^d, by `Polynomial.natDegree_comp_le` applied at each
tree level.

**Fully constructive — no axioms.** This is the cleanest of the three substrate
examples; replaces EML's analytic-continuation barrier with elementary
polynomial degree arithmetic.

Headline: `x_pow_9_not_representable_at_depth_3`. -/

import MatrixFoundations.Sheffer.Core
import MatrixFoundations.Eml  -- transitively pulls Real / Infinite ℝ instance
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.NormNum
-- Note: cleaner import for `Infinite ℝ` (e.g. Mathlib.SetTheory.Cardinal.Basic
-- per researcher's 0820 suggestion) attempted and didn't carry the instance
-- in this mathlib snapshot. Tracking-and-grep through mathlib for the actual
-- carrier of `Infinite ℝ` is more work than the cosmetic ugliness justifies;
-- staying with the Eml-transitive route. Revisit if Eml import becomes a
-- circular-dependency concern.

namespace MinimalBasis.PolyAct

open MinimalBasis

/-- The operator-symbol type for polynomial activations of degree ≤ k. -/
abbrev PolyActOp (k : ℕ) : Type := { p : Polynomial ℝ // p.natDegree ≤ k }

/-- The polynomial-activation basis at degree `k`: each operator is a univariate
polynomial of degree ≤ k. Arity 1. -/
noncomputable def PolyActBasis (k : ℕ) : MinimalBasis.OperatorBasis ℝ where
  Op := PolyActOp k
  arity _ := 1
  eval p args := p.val.eval (args 0)

/-! ### Term depth — basis-specific for PolyAct (arity 1) -/

/-- Helper: the single child index for arity-1 operators. -/
def _root_.MinimalBasis.PolyAct.singleChild {k : ℕ}
    (op : (PolyActBasis k).Op) : Fin ((PolyActBasis k).arity op) := by
  refine ⟨0, ?_⟩
  change 0 < 1
  decide

/-- Structural depth of a `PolyActBasis k` term. Lives in `MinimalBasis.Term`
namespace via `_root_` so dot-notation `T.polyDepth` resolves. -/
def _root_.MinimalBasis.Term.polyDepth {k : ℕ} :
    MinimalBasis.Term (PolyActBasis k) 1 → ℕ
  | .const _     => 0
  | .var _       => 0
  | .app op kids => 1 + (kids (MinimalBasis.PolyAct.singleChild op)).polyDepth

/-! ### Polynomial extraction + degree bound -/

/-- A function `f : (Fin 1 → ℝ) → ℝ` has a polynomial representation of degree
at most `D`. -/
def hasPolyDegLe (D : ℕ) (f : (Fin 1 → ℝ) → ℝ) : Prop :=
  ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ ∀ env, p.eval (env 0) = f env

/-- Extract the underlying univariate polynomial. -/
noncomputable def _root_.MinimalBasis.Term.toPoly {k : ℕ} :
    MinimalBasis.Term (PolyActBasis k) 1 → Polynomial ℝ
  | .const c    => Polynomial.C c
  | .var _      => Polynomial.X
  | .app op kids => op.val.comp ((kids (MinimalBasis.PolyAct.singleChild op)).toPoly)

/-- The associated polynomial evaluates to the same function as the term. -/
theorem Term.toPoly_eval_eq {k : ℕ} (T : MinimalBasis.Term (PolyActBasis k) 1)
    (env : Fin 1 → ℝ) : T.toPoly.eval (env 0) = T.eval env := by
  induction T with
  | const c => simp [MinimalBasis.Term.toPoly, MinimalBasis.Term.eval]
  | var i =>
      have hi : i = 0 := Subsingleton.elim i 0
      simp [MinimalBasis.Term.toPoly, MinimalBasis.Term.eval, hi]
  | app op kids ih =>
      change Polynomial.eval (env 0)
          (op.val.comp (kids (MinimalBasis.PolyAct.singleChild op)).toPoly)
        = (PolyActBasis k).eval op (fun j => (kids j).eval env)
      rw [Polynomial.eval_comp, ih (MinimalBasis.PolyAct.singleChild op)]
      rfl

/-- The polynomial's `natDegree` is bounded by `k^T.polyDepth`. -/
theorem Term.toPoly_natDegree_le {k : ℕ}
    (T : MinimalBasis.Term (PolyActBasis k) 1) :
    T.toPoly.natDegree ≤ k ^ T.polyDepth := by
  induction T with
  | const c =>
      simp [MinimalBasis.Term.toPoly, MinimalBasis.Term.polyDepth, Polynomial.natDegree_C]
  | var i =>
      simp [MinimalBasis.Term.toPoly, MinimalBasis.Term.polyDepth, Polynomial.natDegree_X]
  | app op kids ih =>
      let i := MinimalBasis.PolyAct.singleChild op
      change (op.val.comp (kids i).toPoly).natDegree ≤ k ^ (1 + (kids i).polyDepth)
      calc (op.val.comp (kids i).toPoly).natDegree
          ≤ op.val.natDegree * (kids i).toPoly.natDegree :=
              Polynomial.natDegree_comp_le
        _ ≤ k * k ^ (kids i).polyDepth :=
              Nat.mul_le_mul op.property (ih i)
        _ = k ^ (1 + (kids i).polyDepth) := by
              rw [Nat.add_comm, pow_succ, Nat.mul_comm]

/-- **Degree-bound theorem (Target A core).** Every term of `polyDepth ≤ d`
evaluates to a polynomial of degree `≤ k^d`. Requires `1 ≤ k`. -/
theorem Term.eval_hasPolyDegLe (k d : ℕ) (hk : 1 ≤ k)
    (T : MinimalBasis.Term (PolyActBasis k) 1)
    (hT : T.polyDepth ≤ d) : hasPolyDegLe (k ^ d) T.eval := by
  refine ⟨T.toPoly, ?_, ?_⟩
  · calc T.toPoly.natDegree ≤ k ^ T.polyDepth := Term.toPoly_natDegree_le T
      _ ≤ k ^ d := Nat.pow_le_pow_right hk hT
  · intro env
    exact Term.toPoly_eval_eq T env

/-- **Headline theorem.** `x ↦ x^9` is not representable by any term over
`PolyActBasis 2` of depth ≤ 3. -/
theorem x_pow_9_not_representable_at_depth_3 :
    ¬ ∃ T : MinimalBasis.Term (PolyActBasis 2) 1,
      T.polyDepth ≤ 3 ∧ T.representsGlobally (fun env => (env 0)^9) := by
  rintro ⟨T, hd, hT⟩
  obtain ⟨p, hp_deg, hp_eq⟩ := Term.eval_hasPolyDegLe 2 3 (by norm_num) T hd
  have h_eq : ∀ x : ℝ, p.eval x = x^9 := by
    intro x
    have h1 := hp_eq (fun _ => x)
    have h2 := hT (fun _ => x)
    simp_all
  have h_zero : p - Polynomial.X ^ 9 = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have h_every_root : ∀ x : ℝ, (p - Polynomial.X ^ 9).IsRoot x := by
      intro x
      change (p - Polynomial.X ^ 9).eval x = 0
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, h_eq x]
      ring
    have h_set_eq : { x : ℝ | (p - Polynomial.X ^ 9).IsRoot x } = Set.univ :=
      Set.eq_univ_of_forall h_every_root
    rw [h_set_eq]
    exact Set.infinite_univ
  have h_p_eq : p = Polynomial.X ^ 9 := sub_eq_zero.mp h_zero
  rw [h_p_eq, Polynomial.natDegree_X_pow] at hp_deg
  norm_num at hp_deg

end MinimalBasis.PolyAct
