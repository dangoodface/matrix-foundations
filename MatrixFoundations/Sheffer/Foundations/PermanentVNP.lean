import MatrixFoundations.Sheffer.Foundations.ArithCircuit
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic.Linarith

/-
# Sheffer.Foundations.PermanentVNP — permanent ∈ VNP via Ryser's formula

Phase 3 Round 2.3: prove the permanent family is in VNP.

## Source

**Ryser 1963** — *Combinatorial Mathematics*, Carus Mathematical Monographs.
Cleaner than Valiant's original cycle-cover construction (which we'd
otherwise have to extract from Bürgisser §5.3): the auxiliary polynomial
uses `m(n) = n` Boolean variables instead of `n²`, and admits a closed form
rather than an indicator-times-product.

## The Ryser construction

For an `n × n` matrix of formal variables `X_{ij}` and `n` Boolean variables
`e_1, …, e_n`:

  permRyserAux_n(X, e) =
      (-1)^n · ∏_{j=1}^n (1 − 2·e_j) · ∏_{i=1}^n (∑_{j=1}^n e_j · X_{i,j})

Then `∑_{e : Fin n → Bool} permRyserAux_n(X, e) = permanent(X)`. Hand-verified
by a worked example for `n = 2`: four cube terms sum to `ad + bc`,
matching `permanent [[a,b],[c,d]]`.

## Why this fits VNP

- The Boolean cube has size `2^n`, but the *number of Boolean variables* is
  `n`, satisfying VNP's `m(n) ≤ poly(n)` requirement with `m(n) = n`.
- Auxiliary polynomial has `O(n²)` arithmetic operations: `n` inner sums of
  `n` terms each, plus `n` outer-product factors and `n` sign-factor terms.

## Why `CommRing`, not just `CommSemiring`

The factor `1 - 2·e_j` uses subtraction. `VPOverArity` and `VNPOverArity`
are stated over `CommSemiring`; we instantiate at `CommRing` here.
`CommRing R → CommSemiring R` is automatic, so the framework's predicates
type-check.

## Round 2.3 scope

This commit lands the Ryser scaffold — types and the `permanentRyserAux`
definition (no def-level sorry). Replaces the earlier n²-variable
cycle-cover scaffold per the design note.

Per the design plan:

- **This session:** scaffold and definition.
- **Session N:** `evalBoolSubstitute_permanentRyserAux` (Ryser's identity;
  likely the harder lemma, ~3–5 days).
- **Session N+1:** `permanentRyserAux_in_VPOver` (explicit O(n²) circuit;
  ~1–2 days).
- **Session final:** combine into `permanent_in_VNP_via_arity` (trivial once
  the two lemmas land).

## Sanity check pending

A design note records a checked entry confirming the formula
matches `Matrix.permanent` once a non-trivial proof lands here, in case of
Wikipedia transcription error. A worked-out example verifies `n = 2` by hand;
a Lean-level `n = 2` `decide`-style check is a reasonable next safety net
when starting work on `evalBoolSubstitute_permanentRyserAux`.

## Sorry discipline

Two sorries this session, both on the deep theorems. The Ryser construction
itself is in code and type-checks. -/

namespace Sheffer.PermanentVNP

open Sheffer.ArithCircuit
open MvPolynomial Finset

/-! ## The auxiliary polynomial -/

/-- **The Ryser auxiliary polynomial.**

Polynomial in `n² + n` variables:
- `n²` matrix variables `X_{i,j}` indexed by `Sum.inl (i, j)`.
- `n` Boolean-substitution variables `e_j` indexed by `Sum.inr j`.

When summed over all `e : Fin n → Bool`, it equals `permanentVar R n`
(see `evalBoolSubstitute_permanentRyserAux`). -/
noncomputable def permanentRyserAux (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n ⊕ Fin n) R :=
  (-1)^n *
    (∏ j : Fin n,
      (1 - 2 * (X (Sum.inr j) : MvPolynomial (Fin n × Fin n ⊕ Fin n) R))) *
    (∏ i : Fin n, ∑ j : Fin n,
      (X (Sum.inr j) : MvPolynomial (Fin n × Fin n ⊕ Fin n) R) *
        X (Sum.inl (i, j)))

/-! ## Ryser identity — proof scaffolding

The full identity is the long pole. We split it into reusable steps:
distribute `evalBoolSubstitute` through the construction (mechanical, lands
this session), then perform the combinatorial reduction (inclusion-exclusion;
sorried for follow-up sessions). -/

/-- **Step 1 of Ryser identity.** After substituting `e : Fin n → Bool`
through `permanentRyserAux`, the result has the form
`(-1)^n · ∏_j (1 - 2·c_j) · ∏_i ∑_j c_j · X_{i,j}`, where
`c_j = if e j then 1 else 0` is in the constant subring `C R`.

This is mechanical pushing of `evalBoolSubstitute` through `*`, `^`, `-`, `∏`,
`∑` via the ring-hom helpers in `ArithCircuit.lean`. The combinatorial
content is in the next step. -/
private lemma evalBoolSubstitute_permanentRyserAux_step1
    (R : Type*) [CommRing R] (n : ℕ) (e : Fin n → Bool) :
    evalBoolSubstitute (permanentRyserAux R n) e =
      ((-1) : MvPolynomial (Fin n × Fin n) R)^n *
      (∏ j : Fin n,
        (1 - 2 * MvPolynomial.C (if e j then (1 : R) else 0))) *
      (∏ i : Fin n, ∑ j : Fin n,
        MvPolynomial.C (if e j then (1 : R) else 0) *
        MvPolynomial.X (i, j)) := by
  unfold permanentRyserAux
  simp only [evalBoolSubstitute_mul, evalBoolSubstitute_pow,
             evalBoolSubstitute_prod, evalBoolSubstitute_sum,
             evalBoolSubstitute_sub, evalBoolSubstitute_X_inl,
             evalBoolSubstitute_X_inr, evalBoolSubstitute_one,
             evalBoolSubstitute_neg, evalBoolSubstitute_two]

/-- **Step 2 of Ryser identity.** Each sign factor `1 - 2·C(if b then 1 else 0)`
collapses to a single constant `C(if b then -1 else 1)` — i.e., `+1` when
`e_j = false` and `-1` when `e_j = true`.

The product `∏_j` of these factors thus equals `(-1)^|supp e|` (formalized as
a follow-up). -/
private lemma sign_factor_eq {R : Type*} [CommRing R] {σ : Type*} (b : Bool) :
    (1 : MvPolynomial σ R) - 2 * MvPolynomial.C (if b then (1 : R) else 0) =
      MvPolynomial.C (if b then (-1 : R) else 1) := by
  cases b
  · simp
  · simp only [if_true]
    rw [show (2 : MvPolynomial σ R) = MvPolynomial.C 2 from rfl,
        show (1 : MvPolynomial σ R) = MvPolynomial.C 1 from rfl,
        ← map_mul, ← map_sub]
    norm_num

/-- **Step 3 of Ryser identity.** The full sign-factor product collapses to
a scalar `C`-image: each factor `1 - 2·C(if e j then 1 else 0)` is a constant
(`+1` or `-1`) by step 2, and `C` distributes over `∏`. -/
private lemma sign_product_eq {R : Type*} [CommRing R] {σ : Type*} (n : ℕ)
    (e : Fin n → Bool) :
    (∏ j : Fin n,
      ((1 : MvPolynomial σ R) -
        2 * MvPolynomial.C (if e j then (1 : R) else 0))) =
      MvPolynomial.C
        (∏ j : Fin n, (if e j then (-1 : R) else 1)) := by
  rw [map_prod]
  exact Finset.prod_congr rfl (fun j _ => sign_factor_eq (e j))

/-- **Step 4 of Ryser identity.** Each row's inner sum reduces from a
linear-combination-with-Boolean-coefficients to an `if`-gated sum: a term is
either `X (i, j)` (when `e j = true`) or `0` (when `e j = false`). -/
private lemma row_sum_eq {R : Type*} [CommRing R] (n : ℕ)
    (e : Fin n → Bool) (i : Fin n) :
    (∑ j : Fin n, MvPolynomial.C (if e j then (1 : R) else 0) *
      (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) R)) =
    ∑ j : Fin n, (if e j then MvPolynomial.X (i, j) else 0) := by
  apply Finset.sum_congr rfl
  intros j _
  by_cases h : e j
  · simp [h]
  · simp [h]

/-- **Combined steps 1 + 3 + 4.** After substituting `e` and simplifying the
sign factors and inner sums, `permanentRyserAux R n` evaluated at `e` becomes:

  `(-1)^n · C(∏_j (if e j then -1 else 1)) · ∏_i ∑_j (if e j then X_{i,j} else 0)`

This is the form on which the combinatorial argument operates: outer-product
expansion, swap-of-summation, and inclusion-exclusion. -/
private lemma evalBoolSubstitute_permanentRyserAux_clean
    (R : Type*) [CommRing R] (n : ℕ) (e : Fin n → Bool) :
    evalBoolSubstitute (permanentRyserAux R n) e =
      ((-1) : MvPolynomial (Fin n × Fin n) R)^n *
      MvPolynomial.C (∏ j : Fin n, (if e j then (-1 : R) else 1)) *
      (∏ i : Fin n, ∑ j : Fin n,
        (if e j then (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) R)
         else 0)) := by
  rw [evalBoolSubstitute_permanentRyserAux_step1, sign_product_eq]
  congr 1
  apply Finset.prod_congr rfl
  intros i _
  exact row_sum_eq n e i

/-- **Step 5 of Ryser identity.** The outer product
`∏_i (∑_j (if e j then X_{i,j} else 0))` expands as a sum over functions
`f : Fin n → Fin n` of the term-wise product of selectors and matrix variables.

This is the standard "expand a product of sums" identity, packaged via
mathlib's `Finset.prod_univ_sum` + `Fintype.piFinset_univ`. -/
private lemma row_product_expand {R : Type*} [CommRing R] (n : ℕ)
    (e : Fin n → Bool) :
    (∏ i : Fin n, ∑ j : Fin n,
      (if e j then (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) R)
       else 0)) =
    ∑ f : Fin n → Fin n, ∏ i : Fin n,
      (if e (f i) then MvPolynomial.X (i, f i) else 0) := by
  rw [show ((∏ i : Fin n, ∑ j : Fin n,
        (if e j then (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) R)
         else 0))) =
      ∏ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)),
        (if e j then (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) R)
         else 0) from rfl]
  rw [Finset.prod_univ_sum]
  rw [show (Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (Fin n)))) =
      (Finset.univ : Finset (Fin n → Fin n)) from Fintype.piFinset_univ]

/-- **Step 6 of Ryser identity.** Combine all the algebraic-side simplifications
and swap the orders of summation. The Boolean-cube sum becomes a sum over
function-substitutions `f : Fin n → Fin n`, with the inclusion-exclusion
content remaining inside a per-`f` Boolean-cube sum. -/
private lemma sum_evalBoolSubstitute_swap {R : Type*} [CommRing R] (n : ℕ) :
    (∑ e : Fin n → Bool, evalBoolSubstitute (permanentRyserAux R n) e) =
    ∑ f : Fin n → Fin n, ∑ e : Fin n → Bool,
      ((-1) : MvPolynomial (Fin n × Fin n) R)^n *
      MvPolynomial.C (∏ j : Fin n, (if e j then (-1 : R) else 1)) *
      (∏ i : Fin n, (if e (f i) then
        (MvPolynomial.X (i, f i) : MvPolynomial (Fin n × Fin n) R)
        else 0)) := by
  conv_lhs =>
    rw [show (∑ e : Fin n → Bool, evalBoolSubstitute (permanentRyserAux R n) e) =
          ∑ e : Fin n → Bool, ((-1) : MvPolynomial (Fin n × Fin n) R)^n *
            MvPolynomial.C (∏ j : Fin n, (if e j then (-1 : R) else 1)) *
            (∑ f : Fin n → Fin n, ∏ i : Fin n,
              (if e (f i) then MvPolynomial.X (i, f i) else 0)) from by
          apply Finset.sum_congr rfl
          intros e _
          rw [evalBoolSubstitute_permanentRyserAux_clean, row_product_expand]]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **Step 7a of Ryser identity.** Factor the X-product out of the
indicator-gated outer product: `∏_i (if e (f i) then X (i, f i) else 0)`
equals `(∏_i (if e (f i) then 1 else 0)) * (∏_i X (i, f i))`. The `X`-product
is then independent of `e` and can be pulled out of the Boolean-cube sum. -/
private lemma row_product_factor {R : Type*} [CommRing R] (n : ℕ)
    (e : Fin n → Bool) (f : Fin n → Fin n) :
    (∏ i : Fin n, (if e (f i) then
      (MvPolynomial.X (i, f i) : MvPolynomial (Fin n × Fin n) R)
      else 0)) =
    (∏ i : Fin n,
      (if e (f i) then (1 : MvPolynomial (Fin n × Fin n) R) else 0)) *
    (∏ i : Fin n,
      (MvPolynomial.X (i, f i) : MvPolynomial (Fin n × Fin n) R)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intros i _
  by_cases h : e (f i)
  · simp [h]
  · simp [h]

/-- **Step 7 — bijective case.** When `f` is bijective, reindex the
`∏_i (if e (f i) then 1 else 0)` factor to `∏_j (if e j then 1 else 0)` via
`Function.Bijective.prod_comp`. The merged product is non-zero only at
`e = const true`, where it evaluates to `1`; the C-coefficient there is
`C((-1)^n) = (-1)^n`. -/
private lemma inner_sum_bij {R : Type*} [CommRing R] (n : ℕ)
    (f : Fin n → Fin n) (hf : Function.Bijective f) :
    (∑ e : Fin n → Bool,
      MvPolynomial.C (∏ j : Fin n, (if e j then (-1 : R) else 1)) *
      (∏ i : Fin n,
        (if e (f i) then (1 : MvPolynomial (Fin n × Fin n) R) else 0))) =
    ((-1) : MvPolynomial (Fin n × Fin n) R)^n := by
  rw [show (∑ e : Fin n → Bool,
        MvPolynomial.C (∏ j : Fin n, (if e j then (-1 : R) else 1)) *
        (∏ i : Fin n,
          (if e (f i) then (1 : MvPolynomial (Fin n × Fin n) R) else 0))) =
      ∑ e : Fin n → Bool,
        MvPolynomial.C (∏ j : Fin n, (if e j then (-1 : R) else 1)) *
        (∏ j : Fin n,
          (if e j then (1 : MvPolynomial (Fin n × Fin n) R) else 0)) from by
    apply Finset.sum_congr rfl
    intros e _
    rw [hf.prod_comp
      (fun j => if e j then (1 : MvPolynomial (Fin n × Fin n) R) else 0)]]
  rw [Finset.sum_eq_single (fun _ : Fin n => true)
        (fun e _ hne => ?_) (fun h => absurd (Finset.mem_univ _) h)]
  · -- e = const_true case: simp reduces if-True to base value
    simp only [if_true]
    rw [Finset.prod_const_one, mul_one,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        map_pow, map_neg, map_one]
  · -- e ≠ const_true case: ∃ j, e j = false; that factor zeros the product
    have ⟨j, hj⟩ : ∃ j, e j = false := by
      by_contra h
      apply hne
      funext j
      cases hej : e j with
      | true => rfl
      | false =>
        exact absurd ⟨j, hej⟩ h
    rw [show (∏ j' : Fin n, (if e j' then
        (1 : MvPolynomial (Fin n × Fin n) R) else 0)) = 0 from
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj]; rfl), mul_zero]

/-- **Step 7 — non-bijective case.** When `f` is not bijective, the inner
Boolean-cube sum vanishes. Proof outline (deferred):

- `f` not bijective ⇒ not surjective (`Fin n → Fin n` finite) ⇒ `∃ j₀ ∉ image f`.
- Split the Boolean cube via `Equiv.funSplitAt j₀` into `Bool × ((Fin n - {j₀}) → Bool)`.
- For each fixed `e'` on the complement, the sum over `b : Bool`
  factors out `C(if b then -1 else 1)` (since j₀ ∉ image f, the X-product
  is independent of b). `∑_b C(if b then -1 else 1) = C(-1) + C(1) = 0`.
- Total: `∑_{e'} 0 = 0`. -/
private lemma inner_sum_not_bij {R : Type*} [CommRing R] (n : ℕ)
    (f : Fin n → Fin n) (hf : ¬ Function.Bijective f) :
    (∑ e : Fin n → Bool,
      MvPolynomial.C (∏ j : Fin n, (if e j then (-1 : R) else 1)) *
      (∏ i : Fin n,
        (if e (f i) then (1 : MvPolynomial (Fin n × Fin n) R) else 0))) =
    0 := by
  -- Extract j₀ ∉ image f via not-surjective
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n, ∀ i, f i ≠ j₀ := by
    by_contra h
    push Not at h
    exact hf ⟨Finite.injective_iff_surjective.mpr h, h⟩
  -- Pair-cancel via the involution e ↦ Function.update e j₀ (!e j₀)
  apply Finset.sum_ninvolution (fun e : Fin n → Bool =>
    Function.update e j₀ (!e j₀))
  · -- Main: f e + f (g e) = 0
    intros e
    -- The indicator product is invariant: for every i, f i ≠ j₀, so update doesn't touch e (f i).
    have h_ind_pointwise : ∀ i : Fin n,
        (Function.update e j₀ (!e j₀)) (f i) = e (f i) :=
      fun i => Function.update_of_ne (hj₀ i) _ _
    have h_ind :
        (∏ i : Fin n, (if (Function.update e j₀ (!e j₀)) (f i) then
            (1 : MvPolynomial (Fin n × Fin n) R) else 0)) =
        ∏ i : Fin n, (if e (f i) then
            (1 : MvPolynomial (Fin n × Fin n) R) else 0) :=
      Finset.prod_congr rfl (fun i _ => by rw [h_ind_pointwise i])
    -- The sign product flips: at j₀ the factor flips, others unchanged.
    have h_sign :
        (∏ j : Fin n, (if (Function.update e j₀ (!e j₀)) j then (-1 : R) else 1)) =
        - ∏ j : Fin n, (if e j then (-1 : R) else 1) := by
      rw [show (∏ j : Fin n, (if (Function.update e j₀ (!e j₀)) j then (-1 : R) else 1)) =
            (if (Function.update e j₀ (!e j₀)) j₀ then (-1 : R) else 1) *
            ∏ j ∈ (Finset.univ : Finset (Fin n)) \ {j₀},
              (if (Function.update e j₀ (!e j₀)) j then (-1 : R) else 1) from
          Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ j₀) _]
      rw [show (∏ j : Fin n, (if e j then (-1 : R) else 1)) =
            (if e j₀ then (-1 : R) else 1) *
            ∏ j ∈ (Finset.univ : Finset (Fin n)) \ {j₀},
              (if e j then (-1 : R) else 1) from
          Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ j₀) _]
      rw [Function.update_self]
      have h_others :
          (∏ j ∈ (Finset.univ : Finset (Fin n)) \ {j₀},
            (if (Function.update e j₀ (!e j₀)) j then (-1 : R) else 1)) =
          ∏ j ∈ (Finset.univ : Finset (Fin n)) \ {j₀},
            (if e j then (-1 : R) else 1) := by
        apply Finset.prod_congr rfl
        intros j hj
        have hjj₀ : j ≠ j₀ := by
          intro h
          rw [h] at hj
          exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_singleton.mpr rfl)
        rw [Function.update_of_ne hjj₀]
      rw [h_others]
      cases hb : e j₀
      · simp
      · simp
    rw [h_ind, h_sign, map_neg]
    ring
  · -- f e ≠ 0 → g e ≠ e: g flips e at j₀, so g e ≠ e always
    intros e _ h_eq
    have h := congrFun h_eq j₀
    rw [Function.update_self] at h
    cases hb : e j₀ <;> rw [hb] at h <;> simp at h
  · -- g e ∈ univ
    intros _; exact Finset.mem_univ _
  · -- g (g e) = e
    intros e
    funext j
    by_cases h : j = j₀
    · subst h; rw [Function.update_self, Function.update_self, Bool.not_not]
    · rw [Function.update_of_ne h, Function.update_of_ne h]

/-- **Step 7 of Ryser identity — the inclusion-exclusion key.** For each
fixed `f : Fin n → Fin n`, the Boolean-cube sum of
`C(sign factor) * ∏_i (if e (f i) then 1 else 0)` collapses to
`(-1)^n` when `f` is bijective, and `0` otherwise.

Proof outline (deferred):
1. Reindex `∏_i (if e (f i) then 1 else 0)` over fibers of `f`: equals
   `∏_{j ∈ image f} (if e j then 1 else 0)^{|f⁻¹ j|}`.
2. For `j ∈ image f`, `|f⁻¹ j| ≥ 1`, so the factor is `(if e j then 1 else 0)`
   (idempotent in `R`).
3. Combined with the C-coefficient `∏_j C(if e j then -1 else 1)`, the
   e-dependent integrand is a per-coordinate product `∏_j H_j(e j)` where
   `H_j(b) = C(if b then -1 else 1) · (if j ∈ image f then if b then 1 else 0 else 1)`.
4. Apply `Finset.prod_univ_sum.symm` (with `β _ = Bool`) to swap
   `∑_e ∏_j` into `∏_j ∑_b`.
5. Per-coordinate sums:
   - `j ∈ image f`: `∑_b H_j b = -1 + 0 = -1`.
   - `j ∉ image f`: `∑_b H_j b = -1 + 1 = 0`.
6. Total `∏_j (∑_b H_j b)`: `(-1)^n` if `image f = univ` (i.e., `f`
   bijective), else `0`.

Mathlib helpers expected: `Finset.prod_fiberwise_of_maps_to` for fiber
reindexing; `Finset.prod_univ_sum.symm` for the sum-product swap. -/
private lemma inner_sum_indicator_eq_bijective {R : Type*} [CommRing R] (n : ℕ)
    (f : Fin n → Fin n) :
    (∑ e : Fin n → Bool,
      MvPolynomial.C (∏ j : Fin n, (if e j then (-1 : R) else 1)) *
      (∏ i : Fin n,
        (if e (f i) then (1 : MvPolynomial (Fin n × Fin n) R) else 0))) =
    if Function.Bijective f then
      ((-1) : MvPolynomial (Fin n × Fin n) R)^n
    else 0 := by
  by_cases h : Function.Bijective f
  · rw [if_pos h]; exact inner_sum_bij n f h
  · rw [if_neg h]; exact inner_sum_not_bij n f h

/-- **Step 8 — per-`f` collapse.** Combines `row_product_factor` (X-product
out of indicator) with `inner_sum_indicator_eq_bijective` and the
`(-1)^n · (-1)^n = (-1)^{2n} = 1` cancellation. Output: a clean
per-`f` indicator on bijectivity. -/
private lemma per_f_collapse {R : Type*} [CommRing R] (n : ℕ)
    (f : Fin n → Fin n) :
    (∑ e : Fin n → Bool,
      ((-1 : MvPolynomial (Fin n × Fin n) R))^n *
      MvPolynomial.C (∏ j : Fin n, (if e j then (-1 : R) else 1)) *
      (∏ i : Fin n, (if e (f i) then
        (MvPolynomial.X (i, f i) : MvPolynomial (Fin n × Fin n) R) else 0))) =
    if Function.Bijective f then
      ∏ i : Fin n, MvPolynomial.X (i, f i)
    else 0 := by
  -- Step 1: factor X-product out via row_product_factor; rearrange.
  have h_factor : ∀ e : Fin n → Bool,
      ((-1 : MvPolynomial (Fin n × Fin n) R))^n *
      MvPolynomial.C (∏ j : Fin n, (if e j then (-1 : R) else 1)) *
      (∏ i : Fin n, (if e (f i) then
        (MvPolynomial.X (i, f i) : MvPolynomial (Fin n × Fin n) R) else 0)) =
      (((-1 : MvPolynomial (Fin n × Fin n) R))^n *
        (∏ i : Fin n, MvPolynomial.X (i, f i))) *
      (MvPolynomial.C (∏ j : Fin n, (if e j then (-1 : R) else 1)) *
        (∏ i : Fin n, (if e (f i) then
          (1 : MvPolynomial (Fin n × Fin n) R) else 0))) := by
    intros e
    rw [row_product_factor n e f]; ring
  simp_rw [h_factor]
  rw [← Finset.mul_sum]
  rw [inner_sum_indicator_eq_bijective n f]
  by_cases hbij : Function.Bijective f
  · rw [if_pos hbij, if_pos hbij]
    rw [show ((-1 : MvPolynomial (Fin n × Fin n) R))^n *
        (∏ i : Fin n, MvPolynomial.X (i, f i)) *
        ((-1 : MvPolynomial (Fin n × Fin n) R))^n =
        (((-1 : MvPolynomial (Fin n × Fin n) R))^n *
          ((-1 : MvPolynomial (Fin n × Fin n) R))^n) *
        (∏ i : Fin n, MvPolynomial.X (i, f i)) from by ring]
    rw [show ((-1 : MvPolynomial (Fin n × Fin n) R))^n *
        ((-1 : MvPolynomial (Fin n × Fin n) R))^n = 1 from by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]]
    rw [one_mul]
  · rw [if_neg hbij, if_neg hbij, mul_zero]

/-- **Step 9 — bijective functions ↔ permutations.** A sum over `Fin n → Fin n`
gated on `Function.Bijective` converts to a sum over `Equiv.Perm (Fin n)`,
via the `Equiv.toFun` ↔ `Equiv.ofBijective` correspondence. -/
private lemma sum_bijective_eq_sum_perm {R : Type*} [AddCommMonoid R] (n : ℕ)
    (g : (Fin n → Fin n) → R) :
    (∑ f : Fin n → Fin n, (if Function.Bijective f then g f else 0)) =
    ∑ σ : Equiv.Perm (Fin n), g σ := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun σ _ => σ.toFun) ?_ ?_ ?_ ?_
  · intros σ _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, σ.bijective⟩
  · intros σ _ τ _ h
    exact Equiv.ext (congrFun h)
  · intros f hf
    rw [Finset.mem_filter] at hf
    exact ⟨Equiv.ofBijective f hf.2, Finset.mem_univ _, rfl⟩
  · intros σ _; rfl

/-! ## The verification theorems (Ryser identity sorry'd this session) -/

/-- **Ryser's identity.** The Boolean-cube projection of `permanentRyserAux`
recovers the permanent of the matrix of variables.

Proof outline (Ryser 1963):
1. Expand `∏_i ∑_j e_j X_{i,j}` as a sum over functions `f : Fin n → Fin n` of
   `(∏_i e_{f(i)}) · (∏_i X_{i, f(i)})`.
2. Combine with the sign factor `∏_j (1 − 2 e_j) = ∏_j (-1)^{e_j} = (-1)^{|supp(e)|}`.
3. The sum over `e ∈ {0,1}^n` of `(∏_i e_{f(i)}) · (-1)^{|supp(e)|}` is non-zero
   only when `f` is a permutation; in that case it equals `(-1)^n`, which
   cancels the leading `(-1)^n`.
4. Summing over permutations recovers `Matrix.permanent`.

Mathlib primitives expected to land cleanly: `MvPolynomial.eval₂` distributing
over `Finset.prod` / `Finset.sum`; `Finset.sum_pi_finset` (or `Fintype.sum_piFinset`)
for the cube-decomposition step; sign-factor combinatorics.

Estimated 3–5 days. Calibration check at day 7 if not landed. -/
theorem evalBoolSubstitute_permanentRyserAux
    (R : Type*) [CommRing R] (n : ℕ) :
    (∑ e : Fin n → Bool,
      evalBoolSubstitute (permanentRyserAux R n) e) =
        permanentVar R n := by
  rw [sum_evalBoolSubstitute_swap]
  simp_rw [per_f_collapse]
  rw [sum_bijective_eq_sum_perm n
      (fun f => ∏ i : Fin n, MvPolynomial.X (i, f i))]
  -- Goal: ∑ σ : Perm n, ∏ i, X (i, σ i) = permanentVar R n
  unfold permanentVar
  rw [← Matrix.permanent_transpose]
  -- Goal: ∑ σ, ∏ i, X (i, σ i) = (fun i j => X (i, j))ᵀ.permanent
  -- M^T (i, j) = M (j, i), so for our M, M^T (i, j) = X (j, i).
  -- permanent M^T = ∑ σ, ∏ i, M^T (σ i) i = ∑ σ, ∏ i, X (i, σ i).
  rfl

/-! ### Circuit construction for `permanentRyserAux`

Build an explicit `ArithmeticCircuit` whose `toMvPolynomial` recovers
`permanentRyserAux R n`, with size `O(n²)` (polynomial-bounded).

The construction mirrors the formula structure:
- `(-1)^n` as a chain of `(-1)` constants multiplied via `listMul`.
- Sign factors `1 - 2·e_j = 1 + (-2)·e_j` per-`j`, combined via `listMul`.
- Inner row sums `∑_j e_j · X_{i,j}` per-`i` via `listMul ∘ map mul ∘ finRange`,
  combined via `listAdd`. Outer product over rows via `listMul`. -/

private noncomputable def signFactorCircuit (R : Type*) [CommRing R] (n : ℕ)
    (j : Fin n) : ArithmeticCircuit R (Fin n × Fin n ⊕ Fin n) :=
  .add (.const 1) (.mul (.const (-2)) (.input (Sum.inr j)))

private noncomputable def innerTermCircuit (R : Type*) [CommRing R] (n : ℕ)
    (i j : Fin n) : ArithmeticCircuit R (Fin n × Fin n ⊕ Fin n) :=
  .mul (.input (Sum.inr j)) (.input (Sum.inl (i, j)))

private noncomputable def innerSumCircuit (R : Type*) [CommRing R] (n : ℕ)
    (i : Fin n) : ArithmeticCircuit R (Fin n × Fin n ⊕ Fin n) :=
  ArithmeticCircuit.listAdd
    ((List.finRange n).map (innerTermCircuit R n i))

/-- The arithmetic circuit witness for `permanentRyserAux R n`. -/
noncomputable def permanentRyserCircuit (R : Type*) [CommRing R] (n : ℕ) :
    ArithmeticCircuit R (Fin n × Fin n ⊕ Fin n) :=
  .mul
    (.mul
      (ArithmeticCircuit.listMul
        (List.replicate n (ArithmeticCircuit.const (-1))))
      (ArithmeticCircuit.listMul
        ((List.finRange n).map (signFactorCircuit R n))))
    (ArithmeticCircuit.listMul
      ((List.finRange n).map (innerSumCircuit R n)))

/-- Helper: `((finRange n).map g).sum = ∑ i : Fin n, g i`. The named
mathlib `Fin.sum_univ_def` (additive twin of `Fin.prod_univ_def`) doesn't
resolve in this snapshot; reproven inline. -/
private lemma sum_finRange_map_eq {R : Type*} [AddCommMonoid R] (n : ℕ)
    (g : Fin n → R) : ((List.finRange n).map g).sum = ∑ i : Fin n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.map_cons, List.sum_cons,
          Fin.sum_univ_succ]
      congr 1
      rw [List.map_map, ih (g ∘ Fin.succ)]
      rfl

private lemma signFactorCircuit_toMvPolynomial (R : Type*) [CommRing R] (n : ℕ)
    (j : Fin n) :
    (signFactorCircuit R n j).toMvPolynomial =
      1 - 2 * (MvPolynomial.X (Sum.inr j)
        : MvPolynomial (Fin n × Fin n ⊕ Fin n) R) := by
  unfold signFactorCircuit
  simp [ArithmeticCircuit.toMvPolynomial, MvPolynomial.C_neg,
        show ((2 : MvPolynomial (Fin n × Fin n ⊕ Fin n) R)) =
          MvPolynomial.C 2 from rfl]
  ring

private lemma innerTermCircuit_toMvPolynomial (R : Type*) [CommRing R] (n : ℕ)
    (i j : Fin n) :
    (innerTermCircuit R n i j).toMvPolynomial =
      (MvPolynomial.X (Sum.inr j) : MvPolynomial (Fin n × Fin n ⊕ Fin n) R) *
        MvPolynomial.X (Sum.inl (i, j)) := by
  unfold innerTermCircuit
  simp [ArithmeticCircuit.toMvPolynomial]

private lemma innerSumCircuit_toMvPolynomial (R : Type*) [CommRing R] (n : ℕ)
    (i : Fin n) :
    (innerSumCircuit R n i).toMvPolynomial =
      ∑ j : Fin n,
        (MvPolynomial.X (Sum.inr j)
          : MvPolynomial (Fin n × Fin n ⊕ Fin n) R) *
        MvPolynomial.X (Sum.inl (i, j)) := by
  unfold innerSumCircuit
  rw [ArithmeticCircuit.listAdd_toMvPolynomial]
  rw [List.map_map]
  rw [show (List.finRange n).map
      (ArithmeticCircuit.toMvPolynomial ∘ innerTermCircuit R n i) =
      (List.finRange n).map (fun j =>
        (MvPolynomial.X (Sum.inr j)
          : MvPolynomial (Fin n × Fin n ⊕ Fin n) R) *
        MvPolynomial.X (Sum.inl (i, j))) from by
    apply List.map_congr_left
    intros j _
    exact innerTermCircuit_toMvPolynomial R n i j]
  exact sum_finRange_map_eq n _

private lemma permanentRyserCircuit_toMvPolynomial
    (R : Type*) [CommRing R] (n : ℕ) :
    (permanentRyserCircuit R n).toMvPolynomial = permanentRyserAux R n := by
  unfold permanentRyserCircuit
  simp only [ArithmeticCircuit.toMvPolynomial,
             ArithmeticCircuit.listMul_toMvPolynomial]
  unfold permanentRyserAux
  -- 3 factors: (-1)^n × signProduct × outerProduct
  congr 1
  · congr 1
    · -- (-1)^n
      rw [List.map_replicate]
      simp [ArithmeticCircuit.toMvPolynomial]
    · -- ∏_j signFactor j
      rw [List.map_map]
      rw [show (List.finRange n).map
          (ArithmeticCircuit.toMvPolynomial ∘ signFactorCircuit R n) =
          (List.finRange n).map (fun j =>
            1 - 2 * (MvPolynomial.X (Sum.inr j)
              : MvPolynomial (Fin n × Fin n ⊕ Fin n) R)) from by
        apply List.map_congr_left
        intros j _
        exact signFactorCircuit_toMvPolynomial R n j]
      exact (Fin.prod_univ_def _).symm
  · -- ∏_i innerSum i
    rw [List.map_map]
    rw [show (List.finRange n).map
        (ArithmeticCircuit.toMvPolynomial ∘ innerSumCircuit R n) =
        (List.finRange n).map (fun i => ∑ j : Fin n,
          (MvPolynomial.X (Sum.inr j)
            : MvPolynomial (Fin n × Fin n ⊕ Fin n) R) *
          MvPolynomial.X (Sum.inl (i, j))) from by
      apply List.map_congr_left
      intros i _
      exact innerSumCircuit_toMvPolynomial R n i]
    exact (Fin.prod_univ_def _).symm

/-- **Polynomial-size circuit.** `permanentRyserAux R n` has an arithmetic
circuit of size `O(n²)`. Construction: `permanentRyserCircuit R n`. -/
theorem permanentRyserAux_in_VPOver (R : Type*) [CommRing R] :
    VPOverArity R (fun n => Fin n × Fin n ⊕ Fin n)
      (fun n => permanentRyserAux R n) := by
  -- The size of `permanentRyserCircuit R n` is `2n² + 5n + 2` (computed
  -- below). This is bounded by `n^k + k` for `k = 9`. Witness `k = 9`,
  -- prove the bound, exhibit the circuit.
  refine ⟨fun n => 2 * n * n + 5 * n + 2, ⟨9, fun n => ?_⟩, fun n => ?_⟩
  · -- IsPolyBound: 2n² + 5n + 2 ≤ n^9 + 9.
    -- Case-split: n ≤ 1 by decide; n ≥ 2 via `(n+2)^9 ≥ 128 (n+2)²` (which
    -- dominates `2(n+2)² + 5(n+2) + 2`).
    rcases n with _ | _ | n
    · decide
    · decide
    · have h2 : (2 : ℕ) ≤ n + 2 := by omega
      have h_pow7 : (128 : ℕ) ≤ (n + 2) ^ 7 := by
        calc 128 = 2 ^ 7 := by norm_num
          _ ≤ (n + 2) ^ 7 := Nat.pow_le_pow_left h2 7
      have h_pow9 : 128 * (n + 2) ^ 2 ≤ (n + 2) ^ 9 := by
        have h_split : (n + 2) ^ 9 = (n + 2) ^ 7 * (n + 2) ^ 2 := by ring
        rw [h_split]
        exact Nat.mul_le_mul_right ((n + 2) ^ 2) h_pow7
      have h_quad : 2 * (n + 2) * (n + 2) + 5 * (n + 2) + 2 ≤
          128 * (n + 2) ^ 2 + 9 := by
        have h_sq : (n + 2) ^ 2 = (n + 2) * (n + 2) := by ring
        rw [h_sq]
        nlinarith
      linarith
  · -- exhibit circuit + size + correctness
    refine ⟨permanentRyserCircuit R n, ?_, permanentRyserCircuit_toMvPolynomial R n⟩
    -- Size computation: unfold the construction's three layers and accumulate.
    -- - negOnePower: listMul (replicate n (const -1)) — size n
    -- - signProduct: listMul ((finRange n).map signFactor) — size 3n
    --   (each signFactor.size = 2)
    -- - outerProduct: listMul ((finRange n).map innerSum) — size 2n²+n
    --   (each innerSum.size = 2n)
    -- Final: 1 + (1 + n + 3n) + (2n²+n) = 2n² + 5n + 2.
    unfold permanentRyserCircuit
    simp only [ArithmeticCircuit.size, ArithmeticCircuit.listMul_size,
               List.length_replicate, List.map_replicate, List.length_map,
               List.length_finRange, List.sum_replicate, smul_zero]
    -- After simp: ... need to compute the per-element size sums.
    have h_signFactor_size : ∀ j : Fin n,
        (signFactorCircuit R n j).size = 2 := by
      intro j
      simp [signFactorCircuit, ArithmeticCircuit.size]
    have h_innerSum_size : ∀ i : Fin n,
        (innerSumCircuit R n i).size = 2 * n := by
      intro i
      simp only [innerSumCircuit, ArithmeticCircuit.listAdd_size,
                 List.length_map, List.length_finRange, List.map_map]
      have : ((List.finRange n).map (ArithmeticCircuit.size ∘
              (innerTermCircuit R n i))).sum = n := by
        rw [show (ArithmeticCircuit.size ∘ innerTermCircuit R n i) =
              (fun _ => 1) from by
          funext j
          simp [innerTermCircuit, ArithmeticCircuit.size]]
        rw [show ((List.finRange n).map (fun _ : Fin n => 1)) =
              List.replicate n 1 from by
          rw [show (fun _ : Fin n => (1 : ℕ)) = Function.const _ 1 from rfl]
          rw [List.map_const, List.length_finRange]]
        rw [List.sum_replicate, smul_eq_mul, mul_one]
      omega
    -- Combine signFactor sum
    have h_sign_sum : ((List.finRange n).map
        (ArithmeticCircuit.size ∘ signFactorCircuit R n)).sum = 2 * n := by
      rw [show (ArithmeticCircuit.size ∘ signFactorCircuit R n) =
            (fun _ : Fin n => 2) from by funext j; exact h_signFactor_size j]
      rw [show ((List.finRange n).map (fun _ : Fin n => (2 : ℕ))) =
            List.replicate n 2 from by
        rw [show (fun _ : Fin n => (2 : ℕ)) = Function.const _ 2 from rfl]
        rw [List.map_const, List.length_finRange]]
      rw [List.sum_replicate, smul_eq_mul]; omega
    have h_inner_sum : ((List.finRange n).map
        (ArithmeticCircuit.size ∘ innerSumCircuit R n)).sum = 2 * n * n := by
      rw [show (ArithmeticCircuit.size ∘ innerSumCircuit R n) =
            (fun _ : Fin n => 2 * n) from by funext i; exact h_innerSum_size i]
      rw [show ((List.finRange n).map (fun _ : Fin n => 2 * n)) =
            List.replicate n (2 * n) from by
        rw [show (fun _ : Fin n => 2 * n) = Function.const _ (2 * n) from rfl]
        rw [List.map_const, List.length_finRange]]
      rw [List.sum_replicate, smul_eq_mul]; ring
    rw [List.map_map, List.map_map, h_sign_sum, h_inner_sum]
    omega

/-! ## Headline — `permanent_in_VNP_via_arity` -/

/-- **The permanent family is in VNP.**

Witness: `permanentRyserAux R n` with `m n = n`. The polynomial bound on
`m` is trivial (`k = 1`). The two non-trivial pieces are
`permanentRyserAux_in_VPOver` (poly-size circuit) and
`evalBoolSubstitute_permanentRyserAux` (Boolean-cube collapses to permanent).

Specialized to `[CommRing R]` because Ryser's formula uses subtraction.
`CommRing R → CommSemiring R` is automatic, so the framework's
`VNPOverArity` predicate is satisfied. -/
theorem permanent_in_VNP_via_arity (R : Type*) [CommRing R] :
    VNPOverArity R (fun n => Fin n × Fin n)
      (fun n => permanentVar R n) := by
  refine ⟨fun n => n,
          fun n => permanentRyserAux R n,
          ?_, ?_, ?_⟩
  · refine ⟨1, fun n => ?_⟩
    simp
  · exact permanentRyserAux_in_VPOver R
  · intro n
    exact (evalBoolSubstitute_permanentRyserAux R n).symm

end Sheffer.PermanentVNP
