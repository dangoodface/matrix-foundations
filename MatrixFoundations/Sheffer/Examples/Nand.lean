/-
# Sheffer.Examples.Nand — NAND instantiation (positive completeness)

The Boolean, positive-completeness example. Sheffer 1913: every Boolean function
on `n` inputs is expressible as a NAND-term. Direct construction for NOT, AND,
OR; full completeness axiomatized (DNF mechanical proof skipped). -/

import MatrixFoundations.Sheffer.Core
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic

namespace MinimalBasis.NAND

open MinimalBasis

/-- The NAND operator-symbol. One element. -/
inductive NandOp : Type where
  | nand : NandOp
  deriving Inhabited, DecidableEq

/-- NAND on `Bool`: `nand a b := !(a && b)`. -/
def nand (a b : Bool) : Bool := !(a && b)

/-- The NAND operator-basis: single 2-ary operator interpreted as `nand`. -/
def NandBasis : MinimalBasis.OperatorBasis Bool where
  Op := NandOp
  arity _ := 2
  eval _ args := nand (args 0) (args 1)

/-! ### Three load-bearing constructions -/

/-- `notTree` over one variable: `nand x x = !x`. -/
def notTree : MinimalBasis.Term NandBasis 1 :=
  MinimalBasis.Term.app NandOp.nand (fun _ => MinimalBasis.Term.var 0)

/-- `notTree` represents Boolean negation. -/
theorem notTree_repr :
    notTree.representsGlobally (fun env => !(env 0)) := by
  intro env
  cases h : env 0 <;> simp [notTree, MinimalBasis.Term.eval, NandBasis, nand, h]

/-- `andTree` over two variables: `nand (nand x y) (nand x y) = x && y`. -/
def andTree : MinimalBasis.Term NandBasis 2 :=
  let xy : MinimalBasis.Term NandBasis 2 :=
    MinimalBasis.Term.app NandOp.nand
      (fun i => match i with
        | ⟨0, _⟩ => MinimalBasis.Term.var 0
        | ⟨1, _⟩ => MinimalBasis.Term.var 1)
  MinimalBasis.Term.app NandOp.nand (fun _ => xy)

/-- `andTree` represents Boolean conjunction. -/
theorem andTree_repr :
    andTree.representsGlobally (fun env => env 0 && env 1) := by
  intro env
  cases h0 : env 0 <;> cases h1 : env 1 <;>
    simp [andTree, MinimalBasis.Term.eval, NandBasis, nand, h0, h1]

/-- `orTree` over two variables: De Morgan via NAND. -/
def orTree : MinimalBasis.Term NandBasis 2 :=
  let nx : MinimalBasis.Term NandBasis 2 :=
    MinimalBasis.Term.app NandOp.nand (fun _ => MinimalBasis.Term.var 0)
  let ny : MinimalBasis.Term NandBasis 2 :=
    MinimalBasis.Term.app NandOp.nand (fun _ => MinimalBasis.Term.var 1)
  MinimalBasis.Term.app NandOp.nand
    (fun i => match i with
      | ⟨0, _⟩ => nx
      | ⟨1, _⟩ => ny)

/-- `orTree` represents Boolean disjunction. -/
theorem orTree_repr :
    orTree.representsGlobally (fun env => env 0 || env 1) := by
  intro env
  cases h0 : env 0 <;> cases h1 : env 1 <;>
    simp [orTree, MinimalBasis.Term.eval, NandBasis, nand, h0, h1]

/-! ### Sheffer functional completeness (axiomatized) -/

/-! ### Generic NAND-based Boolean operations

Lifting `notTree`/`andTree`/`orTree` from their concrete `var i` use sites
to generic `Term NandBasis n → Term NandBasis n` operations. These let us
build arbitrary Boolean compositions for the DNF-based completeness proof. -/

/-- Generic NOT: `genNot t = nand t t`. -/
def genNot {n : ℕ} (t : MinimalBasis.Term NandBasis n) :
    MinimalBasis.Term NandBasis n :=
  MinimalBasis.Term.app NandOp.nand (fun _ => t)

theorem genNot_eval {n : ℕ} (t : MinimalBasis.Term NandBasis n)
    (env : Fin n → Bool) :
    (genNot t).eval env = !(t.eval env) := by
  simp [genNot, MinimalBasis.Term.eval, NandBasis, nand, Bool.and_self]

/-- Generic AND: `genAnd a b = nand (nand a b) (nand a b)`. -/
def genAnd {n : ℕ} (a b : MinimalBasis.Term NandBasis n) :
    MinimalBasis.Term NandBasis n :=
  let nab : MinimalBasis.Term NandBasis n :=
    MinimalBasis.Term.app NandOp.nand
      (fun i => match i with
        | ⟨0, _⟩ => a
        | ⟨1, _⟩ => b)
  genNot nab

theorem genAnd_eval {n : ℕ} (a b : MinimalBasis.Term NandBasis n)
    (env : Fin n → Bool) :
    (genAnd a b).eval env = (a.eval env && b.eval env) := by
  simp [genAnd, genNot, MinimalBasis.Term.eval, NandBasis, nand]

/-- Generic OR via De Morgan: `genOr a b = nand (nand a a) (nand b b)`. -/
def genOr {n : ℕ} (a b : MinimalBasis.Term NandBasis n) :
    MinimalBasis.Term NandBasis n :=
  MinimalBasis.Term.app NandOp.nand
    (fun i => match i with
      | ⟨0, _⟩ => genNot a
      | ⟨1, _⟩ => genNot b)

theorem genOr_eval {n : ℕ} (a b : MinimalBasis.Term NandBasis n)
    (env : Fin n → Bool) :
    (genOr a b).eval env = (a.eval env || b.eval env) := by
  -- (genOr a b).eval env = nand (genNot a).eval env (genNot b).eval env
  --                     = nand (!a.eval env) (!b.eval env)
  --                     = !(!a.eval env && !b.eval env)
  --                     = a.eval env || b.eval env  (De Morgan)
  have h_unfold : (genOr a b).eval env =
      nand ((genNot a).eval env) ((genNot b).eval env) := rfl
  rw [h_unfold, genNot_eval, genNot_eval]
  cases a.eval env <;> cases b.eval env <;> rfl

/-! ### n-ary AND and OR via fold over `List`

Generalizes `genAnd`/`genOr` to lists of terms. Empty list folds to the
identity element (`true` for AND, `false` for OR). -/

/-- n-ary AND of a list of NAND-terms. Empty list → `Term.const true`. -/
def bigAnd {n : ℕ} : List (MinimalBasis.Term NandBasis n) →
    MinimalBasis.Term NandBasis n
  | []       => MinimalBasis.Term.const true
  | t :: rest => genAnd t (bigAnd rest)

theorem bigAnd_eval {n : ℕ} (ts : List (MinimalBasis.Term NandBasis n))
    (env : Fin n → Bool) :
    (bigAnd ts).eval env = (ts.map (·.eval env)).all id := by
  induction ts with
  | nil => simp [bigAnd, MinimalBasis.Term.eval]
  | cons t rest ih =>
    simp [bigAnd, genAnd_eval, ih, List.all_map]

/-- n-ary OR of a list of NAND-terms. Empty list → `Term.const false`. -/
def bigOr {n : ℕ} : List (MinimalBasis.Term NandBasis n) →
    MinimalBasis.Term NandBasis n
  | []       => MinimalBasis.Term.const false
  | t :: rest => genOr t (bigOr rest)

theorem bigOr_eval {n : ℕ} (ts : List (MinimalBasis.Term NandBasis n))
    (env : Fin n → Bool) :
    (bigOr ts).eval env = (ts.map (·.eval env)).any id := by
  induction ts with
  | nil => simp [bigOr, MinimalBasis.Term.eval]
  | cons t rest ih =>
    simp [bigOr, genOr_eval, ih, List.any_map]

/-! ### Min-term construction and DNF

For each `chosen : Fin n → Bool`, build the min-term that evaluates to
`true` exactly at `chosen` and `false` everywhere else. The DNF of a
Boolean function `f` is the OR over min-terms for all `chosen` with
`f chosen = true`. -/

/-- Min-term for a chosen input vector: `∧_i (if chosen i then var i else ¬var i)`. -/
def minTerm {n : ℕ} (chosen : Fin n → Bool) :
    MinimalBasis.Term NandBasis n :=
  bigAnd ((List.finRange n).map (fun i =>
    if chosen i then MinimalBasis.Term.var i
    else genNot (MinimalBasis.Term.var i)))

/-! ### DNF correctness via classical case-split

A design note suggests: avoid `simp [decide]` over-reduction by
case-splitting classically. Two helper lemmas:

- `minTerm_self_eval`: `(minTerm chosen).eval chosen = true`
- `minTerm_diff_eval`: `chosen ≠ env → (minTerm chosen).eval env = false`

These let the main `dnf_eval` go through Bool truth propagation rather
than `decide`-rewriting. -/

/-- Helper: per-`i` factor of min-term evaluates to true when env matches chosen at i. -/
private lemma minFactor_true_at_match {n : ℕ}
    (chosen env : Fin n → Bool) (i : Fin n) (h : env i = chosen i) :
    ((if chosen i then MinimalBasis.Term.var i
      else genNot (MinimalBasis.Term.var i) :
      MinimalBasis.Term NandBasis n).eval env) = true := by
  by_cases hc : chosen i
  · rw [if_pos hc]
    show (MinimalBasis.Term.var i (B := NandBasis)).eval env = true
    rw [show (MinimalBasis.Term.var i (B := NandBasis)).eval env = env i from rfl]
    rw [h, hc]
  · rw [if_neg hc]
    rw [genNot_eval]
    rw [show (MinimalBasis.Term.var i (B := NandBasis)).eval env = env i from rfl]
    rw [h]
    cases hc' : chosen i
    · rfl
    · exact absurd hc' hc

/-- Helper: per-`i` factor of min-term evaluates to false when env mismatches chosen at i. -/
private lemma minFactor_false_at_mismatch {n : ℕ}
    (chosen env : Fin n → Bool) (i : Fin n) (h : env i ≠ chosen i) :
    ((if chosen i then MinimalBasis.Term.var i
      else genNot (MinimalBasis.Term.var i) :
      MinimalBasis.Term NandBasis n).eval env) = false := by
  by_cases hc : chosen i
  · rw [if_pos hc]
    show (MinimalBasis.Term.var i (B := NandBasis)).eval env = false
    rw [show (MinimalBasis.Term.var i (B := NandBasis)).eval env = env i from rfl]
    cases he : env i
    · rfl
    · rw [hc] at h; exact absurd he h
  · rw [if_neg hc]
    rw [genNot_eval]
    rw [show (MinimalBasis.Term.var i (B := NandBasis)).eval env = env i from rfl]
    cases he : env i
    · cases hc' : chosen i
      · rw [hc'] at h; exact absurd he h
      · exact absurd hc' hc
    · rfl

/-- The min-term for `chosen` evaluates to `true` at `chosen` itself.
Every per-`i` factor evaluates to `true` (env i = chosen i for all i). -/
theorem minTerm_self_eval {n : ℕ} (chosen : Fin n → Bool) :
    (minTerm chosen).eval chosen = true := by
  unfold minTerm
  rw [bigAnd_eval, List.all_eq_true]
  intros b hb
  obtain ⟨t, ht_in, ht_eq⟩ := List.mem_map.mp hb
  obtain ⟨i, _, hi_eq⟩ := List.mem_map.mp ht_in
  subst hi_eq; subst ht_eq
  simp only [id_eq]
  exact minFactor_true_at_match chosen chosen i rfl

/-- If `chosen ≠ env`, the min-term for `chosen` evaluates to `false`
at `env`. Some `i` has `chosen i ≠ env i`; the corresponding factor is
`false`, killing the `bigAnd`. -/
theorem minTerm_diff_eval {n : ℕ} (chosen env : Fin n → Bool)
    (h : chosen ≠ env) :
    (minTerm chosen).eval env = false := by
  obtain ⟨i, hi⟩ : ∃ i, env i ≠ chosen i := by
    by_contra h_all
    push Not at h_all
    exact h (funext (fun i => (h_all i).symm))
  unfold minTerm
  rw [bigAnd_eval]
  apply List.all_eq_false.mpr
  refine ⟨((if chosen i then MinimalBasis.Term.var i
    else genNot (MinimalBasis.Term.var i) :
    MinimalBasis.Term NandBasis n).eval env), ?_, ?_⟩
  · -- Show the value is in the doubly-mapped list.
    exact List.mem_map.mpr
      ⟨_, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, rfl⟩
  · simp only [id_eq]
    rw [minFactor_false_at_mismatch chosen env i hi]
    decide

/-- The DNF representation of a Boolean function `f`: the OR of all
min-terms for inputs where `f` is true. -/
noncomputable def dnf {n : ℕ} (f : (Fin n → Bool) → Bool) :
    MinimalBasis.Term NandBasis n :=
  bigOr (((Finset.univ : Finset (Fin n → Bool)).filter
    (fun env => f env)).toList.map minTerm)

theorem dnf_eval {n : ℕ} (f : (Fin n → Bool) → Bool) (env : Fin n → Bool) :
    (dnf f).eval env = f env := by
  unfold dnf
  rw [bigOr_eval]
  cases hf : f env
  · -- f env = false: show no min-term in the disjunction evaluates to true.
    apply List.any_eq_false.mpr
    intros b hb
    obtain ⟨t, ht_in, ht_eq⟩ := List.mem_map.mp hb
    obtain ⟨chosen, h_chosen_in, hc_eq⟩ := List.mem_map.mp ht_in
    subst hc_eq; subst ht_eq
    rw [Finset.mem_toList, Finset.mem_filter] at h_chosen_in
    simp only [id_eq]
    have h_ne : chosen ≠ env := by
      intro h_eq
      rw [← h_eq] at hf
      exact absurd h_chosen_in.2 (by rw [hf]; exact Bool.false_ne_true)
    rw [minTerm_diff_eval chosen env h_ne]
    decide
  · -- f env = true: env is in the disjunction list, evaluates to true.
    apply List.any_eq_true.mpr
    refine ⟨true, ?_, rfl⟩
    -- Need: true ∈ list. Witness via env's min-term.
    exact List.mem_map.mpr
      ⟨minTerm env,
       List.mem_map.mpr ⟨env, by
         rw [Finset.mem_toList, Finset.mem_filter]
         exact ⟨Finset.mem_univ _, hf⟩, rfl⟩,
       minTerm_self_eval env⟩

/-- **Sheffer functional completeness, 1913.** Every Boolean function on
`n` inputs is representable as a NAND-term. Constructive proof via DNF. -/
theorem sheffer_complete (n : ℕ) (f : (Fin n → Bool) → Bool) :
    ∃ T : MinimalBasis.Term NandBasis n, T.representsGlobally f :=
  ⟨dnf f, fun env => dnf_eval f env⟩

end MinimalBasis.NAND
