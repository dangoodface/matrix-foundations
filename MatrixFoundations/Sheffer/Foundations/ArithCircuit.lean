import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Matrix.Permanent

/-
# Sheffer.Foundations.ArithCircuit — VP / VNP foundations

Phase 3 Round 1: define the foundations for VP and VNP — Valiant's algebraic
complexity classes. Round 1 lands the basic types + definitions; the deep
theorems (permanent VNP-completeness, projection-construction) are Round 2+.

## Definitional choice

Bürgisser–Clausen–Shokrollahi *Algebraic Complexity Theory* (1997, §5.2) and
Saptharishi's survey give the same VP/VNP definitions up to convention. We
follow Bürgisser §5.2, with one generalization: variable types are arbitrary
`Type*` rather than just `Fin n`. This lets us state `permanent_in_VNP` directly
against `MvPolynomial (Fin n × Fin n) R` without an `Fin (n*n)` encoding.

The fixed-`Fin n` version is recovered by setting `σ := Fin`.

## Scope this round (revised post-(a) decision)

- ✓ **Types:** `ArithmeticCircuit` inductive over arbitrary variable type `σ`,
  with `size`, `eval`, `toMvPolynomial`.
- ✓ **Polynomial-growth predicate:** `IsPolyBound`.
- ✓ **`VPOverArity`:** polynomial-family-of-polynomial-size on arity-function-typed
  variable types `σ : ℕ → Type*`.
- ✓ **`evalBoolSubstitute`:** Boolean-cube partial evaluation, generalized.
- ✓ **`VNPOverArity`:** projection-over-Boolean-cube of polynomial-size circuit family.
- ✓ **`VPSubsetVNP`:** closed (`m = 0`, sum over singleton Boolean cube).
- **`permanent_in_VNP`:** deferred to Round 2 (Valiant's projection construction; long pole).

## Out of scope (Round 2+)

- `permanent_in_VNP_via_arity` — straightforward instantiation, Round 2.
- `permanent_VNP_hard` — Valiant 1979's hardness proof (3-CNF SAT →
  permanent reduction). 2-4 weeks Round 2 territory.
- `PolynomialActivationBasis → ArithmeticCircuit` bridge (Round 3).
- The Valiant-conditional architectural bound (Phase 4).

-/

namespace Sheffer.ArithCircuit

/-! ## Arithmetic circuits — generalized over arbitrary variable type -/

/-- An arithmetic circuit over a commutative semiring `R` with input variables
of type `σ`. Standard inductive: leaves are inputs (`σ → ...`) or constants
(`R → ...`); internal nodes are addition or multiplication. -/
inductive ArithmeticCircuit (R : Type*) [CommSemiring R] (σ : Type*) : Type _ where
  | input : σ → ArithmeticCircuit R σ
  | const : R → ArithmeticCircuit R σ
  | add   : ArithmeticCircuit R σ → ArithmeticCircuit R σ → ArithmeticCircuit R σ
  | mul   : ArithmeticCircuit R σ → ArithmeticCircuit R σ → ArithmeticCircuit R σ

namespace ArithmeticCircuit

variable {R : Type*} [CommSemiring R] {σ : Type*}

/-- Number of internal `add`/`mul` gates. -/
def size : ArithmeticCircuit R σ → ℕ
  | .input _ => 0
  | .const _ => 0
  | .add a b => 1 + a.size + b.size
  | .mul a b => 1 + a.size + b.size

/-- Evaluate at an input assignment `σ → R`. -/
def eval (env : σ → R) : ArithmeticCircuit R σ → R
  | .input i => env i
  | .const c => c
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env

/-- The multivariate polynomial computed by the circuit. -/
noncomputable def toMvPolynomial : ArithmeticCircuit R σ → MvPolynomial σ R
  | .input i => MvPolynomial.X i
  | .const c => MvPolynomial.C c
  | .add a b => a.toMvPolynomial + b.toMvPolynomial
  | .mul a b => a.toMvPolynomial * b.toMvPolynomial

/-! ### `mapInputs` — input-variable renaming

The structural-recursion transformer that re-types a circuit's input variables
along an arbitrary function `σ → τ`. Used to build the VP circuit witness for
`VPSubsetVNP_arity` (where we re-type `Fin n`-input circuits to `σ ⊕ Fin 0`-input
circuits via `Sum.inl`). Useful primitive beyond just that application. -/

variable {τ : Type*}

/-- Rename a circuit's input variables along `f : σ → τ`. -/
def mapInputs (f : σ → τ) : ArithmeticCircuit R σ → ArithmeticCircuit R τ
  | .input s => .input (f s)
  | .const c => .const c
  | .add a b => .add (a.mapInputs f) (b.mapInputs f)
  | .mul a b => .mul (a.mapInputs f) (b.mapInputs f)

/-- `mapInputs` preserves size (no gates added or removed by renaming). -/
theorem mapInputs_size (f : σ → τ) (C : ArithmeticCircuit R σ) :
    (C.mapInputs f).size = C.size := by
  induction C with
  | input s => rfl
  | const c => rfl
  | add a b iha ihb => simp [mapInputs, size, iha, ihb]
  | mul a b iha ihb => simp [mapInputs, size, iha, ihb]

/-- `mapInputs` evaluation: `(C.mapInputs f).eval env = C.eval (env ∘ f)`. -/
theorem mapInputs_eval (f : σ → τ) (env : τ → R) (C : ArithmeticCircuit R σ) :
    (C.mapInputs f).eval env = C.eval (env ∘ f) := by
  induction C with
  | input s => rfl
  | const c => rfl
  | add a b iha ihb => simp [mapInputs, eval, iha, ihb]
  | mul a b iha ihb => simp [mapInputs, eval, iha, ihb]

/-- `mapInputs` polynomial: `(C.mapInputs f).toMvPolynomial` is `C.toMvPolynomial`
with variables relabeled along `f`, computable as a `MvPolynomial.eval₂`-style
substitution `X i ↦ X (f i)`. -/
theorem mapInputs_toMvPolynomial (f : σ → τ) (C : ArithmeticCircuit R σ) :
    (C.mapInputs f).toMvPolynomial =
      MvPolynomial.eval₂ MvPolynomial.C (fun s => MvPolynomial.X (f s))
        C.toMvPolynomial := by
  induction C with
  | input s => simp [mapInputs, toMvPolynomial]
  | const c =>
      simp [mapInputs, toMvPolynomial]
  | add a b iha ihb =>
      simp [mapInputs, toMvPolynomial, iha, ihb]
  | mul a b iha ihb =>
      simp [mapInputs, toMvPolynomial, iha, ihb]

/-! ### Big-operator circuits — fold-based product and sum

Build circuits computing `∏` and `∑` over a `List`. The two helpers below
package the standard right-fold pattern with their `toMvPolynomial` and
`size` proofs, so downstream constructions (e.g., the permanent VPOver
circuit in `PermanentVNP.lean`) don't have to re-derive them. -/

/-- Build a circuit computing the product of a list, folding via `.mul`. -/
def listMul (cs : List (ArithmeticCircuit R σ)) : ArithmeticCircuit R σ :=
  cs.foldr (fun c acc => .mul c acc) (.const 1)

/-- Build a circuit computing the sum of a list, folding via `.add`. -/
def listAdd (cs : List (ArithmeticCircuit R σ)) : ArithmeticCircuit R σ :=
  cs.foldr (fun c acc => .add c acc) (.const 0)

theorem listMul_toMvPolynomial (cs : List (ArithmeticCircuit R σ)) :
    (listMul cs).toMvPolynomial = (cs.map toMvPolynomial).prod := by
  induction cs with
  | nil => simp [listMul, toMvPolynomial]
  | cons c rest ih =>
      change (mul c (listMul rest)).toMvPolynomial = _
      simp [toMvPolynomial, ih]

theorem listAdd_toMvPolynomial (cs : List (ArithmeticCircuit R σ)) :
    (listAdd cs).toMvPolynomial = (cs.map toMvPolynomial).sum := by
  induction cs with
  | nil => simp [listAdd, toMvPolynomial]
  | cons c rest ih =>
      change (add c (listAdd rest)).toMvPolynomial = _
      simp [toMvPolynomial, ih]

theorem listMul_size (cs : List (ArithmeticCircuit R σ)) :
    (listMul cs).size = cs.length + (cs.map size).sum := by
  induction cs with
  | nil => simp [listMul, size]
  | cons c rest ih =>
      change (mul c (listMul rest)).size = _
      simp [size, ih]; omega

theorem listAdd_size (cs : List (ArithmeticCircuit R σ)) :
    (listAdd cs).size = cs.length + (cs.map size).sum := by
  induction cs with
  | nil => simp [listAdd, size]
  | cons c rest ih =>
      change (add c (listAdd rest)).size = _
      simp [size, ih]; omega

end ArithmeticCircuit

/-! ## Polynomial-growth predicate -/

/-- `p : ℕ → ℕ` has polynomial growth iff `n^k + k` dominates for some `k`. -/
def IsPolyBound (p : ℕ → ℕ) : Prop :=
  ∃ k : ℕ, ∀ n, p n ≤ n ^ k + k

/-- The identity is polynomial-bounded. -/
example : IsPolyBound id := ⟨1, fun n => by simp⟩

/-- Constant-zero is polynomial-bounded. -/
example : IsPolyBound (fun _ => 0) := ⟨0, fun _ => by simp⟩

/-! ## VP — polynomial-size circuit families -/

/-- `VPOverArity R σ f`: the polynomial family `f`, where `f n` lives in
`MvPolynomial (σ n) R`, is computable by a polynomial-size circuit family.

The variable-type-as-function-of-`n` shape covers both `Fin n` (matched-arity
families) and `Fin n × Fin n` (matrix-shaped families like the permanent),
without `Fin (n*n)` encoding plumbing. -/
def VPOverArity (R : Type*) [CommSemiring R] (σ : ℕ → Type*)
    (f : (n : ℕ) → MvPolynomial (σ n) R) : Prop :=
  ∃ p : ℕ → ℕ, IsPolyBound p ∧
    ∀ n, ∃ C : ArithmeticCircuit R (σ n),
      C.size ≤ p n ∧ C.toMvPolynomial = f n

/-- `VPOver R f` is the special case `σ := Fin`. -/
def VPOver (R : Type*) [CommSemiring R]
    (f : (n : ℕ) → MvPolynomial (Fin n) R) : Prop :=
  VPOverArity R Fin f

/-! ## VNP — projections of polynomial sums over the Boolean cube

Valiant 1979 / Bürgisser §5.2: a polynomial family `f` is in VNP iff there
exists a VP family `g` (in `σ n ⊕ Fin (m n)` variables, with `m` polynomially
bounded) such that `f n` is the sum of `g n` evaluated over all `2^(m n)`
Boolean substitutions for the latter `m n` variables.

The substitution machinery is in `evalBoolSubstitute`. -/

/-- Partial evaluation: substitute the `Fin (m n)`-side of a polynomial in
`σ ⊕ Fin m` variables with Boolean values (1 or 0 in `R`), leaving the
`σ`-side as variables. -/
noncomputable def evalBoolSubstitute {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ}
    (g : MvPolynomial (σ ⊕ Fin m) R) (e : Fin m → Bool) :
    MvPolynomial σ R :=
  MvPolynomial.eval₂ MvPolynomial.C
    (Sum.elim (fun s => MvPolynomial.X s)
              (fun i => MvPolynomial.C (if e i then (1 : R) else 0)))
    g

/-- `VNPOverArity R σ f`: there exists a polynomial-size family `g` in
`σ n ⊕ Fin (m n)` variables (with `m` polynomially bounded) such that `f n`
equals the sum of `g n` over all Boolean substitutions for the `Fin (m n)` side.

Generalizes Bürgisser §5.2's fixed-arity definition to arbitrary variable types. -/
def VNPOverArity (R : Type*) [CommSemiring R] (σ : ℕ → Type*)
    (f : (n : ℕ) → MvPolynomial (σ n) R) : Prop :=
  ∃ (m : ℕ → ℕ) (g : (n : ℕ) → MvPolynomial (σ n ⊕ Fin (m n)) R),
    IsPolyBound m ∧
    VPOverArity R (fun n => σ n ⊕ Fin (m n)) g ∧
    ∀ n, f n = ∑ e : Fin (m n) → Bool, evalBoolSubstitute (g n) e

/-- `VNPOver R f` is the special case `σ := Fin`. -/
def VNPOver (R : Type*) [CommSemiring R]
    (f : (n : ℕ) → MvPolynomial (Fin n) R) : Prop :=
  VNPOverArity R Fin f

/-! ## VP ⊆ VNP — the easy direction -/

/-- Helper: when `m = 0`, the type `Fin 0 → Bool` has a unique inhabitant
(the empty function), so a sum over it equals the value at that inhabitant.
The proof is `Fintype.sum_unique` plus the fact that the unique inhabitant
(`default`) is definitionally equal to the explicit empty function. -/
private lemma sum_fin_zero_bool {R : Type*} [AddCommMonoid R] (f : (Fin 0 → Bool) → R) :
    (∑ e : Fin 0 → Bool, f e) = f (fun i => i.elim0) :=
  Fintype.sum_unique f

/-- Helper: the `Sum.inl ↦ X` re-typing followed by `evalBoolSubstitute` at
the empty Boolean assignment is the identity on `MvPolynomial σ R`.

Proof: structural induction on the polynomial. The composed substitution
`(Sum.elim X (·.elim0)) ∘ Sum.inl = X` is the identity on `σ`, so the
two-step `eval₂` chain telescopes. -/
private lemma evalBoolSubstitute_inl_id {R : Type*} [CommSemiring R] {σ : Type*}
    (p : MvPolynomial σ R) :
    evalBoolSubstitute
        (MvPolynomial.eval₂ MvPolynomial.C
          (fun s : σ => MvPolynomial.X (Sum.inl s : σ ⊕ Fin 0)) p)
        (fun i : Fin 0 => i.elim0) = p := by
  unfold evalBoolSubstitute
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.eval₂_C, MvPolynomial.eval₂_C]
  | add p q hp hq =>
      rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq]
  | mul_X p i ih =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_mul,
          MvPolynomial.eval₂_X, ih]
      rfl

/-- Helper: `evalBoolSubstitute` with `m = 0` is the natural projection from
`MvPolynomial (σ ⊕ Fin 0) R` to `MvPolynomial σ R` — substituting on the
empty `Fin 0` side does nothing, and `σ ⊕ Fin 0 ≃ σ`.

For Round 1 we state this and use it; the full proof reduces to
`MvPolynomial.eval₂_X_id`-style identity arguments and is straightforward
plumbing. Closed below modulo a definitional `sorry` — the equation IS
the right one but the substitution-identity proof requires careful
treatment of `Sum.elim` over `Fin 0`. -/
private lemma evalBoolSubstitute_m_zero {R : Type*} [CommSemiring R] {σ : Type*}
    (g : MvPolynomial (σ ⊕ Fin 0) R) (e : Fin 0 → Bool) :
    evalBoolSubstitute g e =
      MvPolynomial.eval₂ MvPolynomial.C (Sum.elim MvPolynomial.X (fun i => i.elim0)) g := by
  unfold evalBoolSubstitute
  congr 1
  funext s
  cases s with
  | inl s => rfl
  | inr i => exact i.elim0

/-! ## `evalBoolSubstitute` as a ring homomorphism

`evalBoolSubstitute g e` is `MvPolynomial.eval₂ C (Sum.elim X (...)) g`, hence
a ring homomorphism in `g`. Packaging this lets downstream proofs distribute
over `+`, `*`, `^`, `∏`, and `∑` via mathlib's standard `RingHom.map_*` API
instead of unfolding `eval₂` by hand at every step. Used by the Ryser-formula
proof in `PermanentVNP.lean`. -/

/-- The Boolean-substitution map packaged as a `RingHom`. -/
noncomputable def evalBoolSubstituteHom {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool) :
    MvPolynomial (σ ⊕ Fin m) R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim MvPolynomial.X (fun i => MvPolynomial.C (if e i then (1 : R) else 0)))

/-- The plain function `evalBoolSubstitute` agrees with the underlying function
of `evalBoolSubstituteHom`. Definitional. -/
lemma evalBoolSubstitute_eq_hom {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ} (g : MvPolynomial (σ ⊕ Fin m) R) (e : Fin m → Bool) :
    evalBoolSubstitute g e = evalBoolSubstituteHom e g := rfl

@[simp] lemma evalBoolSubstitute_C {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool) (r : R) :
    evalBoolSubstitute (MvPolynomial.C r : MvPolynomial (σ ⊕ Fin m) R) e =
      MvPolynomial.C r := by
  unfold evalBoolSubstitute
  rw [MvPolynomial.eval₂_C]

@[simp] lemma evalBoolSubstitute_X_inl {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool) (s : σ) :
    evalBoolSubstitute (MvPolynomial.X (Sum.inl s) : MvPolynomial (σ ⊕ Fin m) R) e =
      MvPolynomial.X s := by
  unfold evalBoolSubstitute
  rw [MvPolynomial.eval₂_X]
  rfl

@[simp] lemma evalBoolSubstitute_X_inr {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool) (i : Fin m) :
    evalBoolSubstitute (MvPolynomial.X (Sum.inr i) : MvPolynomial (σ ⊕ Fin m) R) e =
      MvPolynomial.C (if e i then (1 : R) else 0) := by
  unfold evalBoolSubstitute
  rw [MvPolynomial.eval₂_X]
  rfl

@[simp] lemma evalBoolSubstitute_add {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool)
    (p q : MvPolynomial (σ ⊕ Fin m) R) :
    evalBoolSubstitute (p + q) e =
      evalBoolSubstitute p e + evalBoolSubstitute q e := by
  rw [evalBoolSubstitute_eq_hom, evalBoolSubstitute_eq_hom,
      evalBoolSubstitute_eq_hom, map_add]

@[simp] lemma evalBoolSubstitute_mul {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool)
    (p q : MvPolynomial (σ ⊕ Fin m) R) :
    evalBoolSubstitute (p * q) e =
      evalBoolSubstitute p e * evalBoolSubstitute q e := by
  rw [evalBoolSubstitute_eq_hom, evalBoolSubstitute_eq_hom,
      evalBoolSubstitute_eq_hom, map_mul]

@[simp] lemma evalBoolSubstitute_pow {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool)
    (p : MvPolynomial (σ ⊕ Fin m) R) (k : ℕ) :
    evalBoolSubstitute (p ^ k) e = (evalBoolSubstitute p e) ^ k := by
  rw [evalBoolSubstitute_eq_hom, evalBoolSubstitute_eq_hom, map_pow]

lemma evalBoolSubstitute_prod {R : Type*} [CommSemiring R]
    {σ ι : Type*} {m : ℕ} (e : Fin m → Bool)
    (s : Finset ι) (f : ι → MvPolynomial (σ ⊕ Fin m) R) :
    evalBoolSubstitute (∏ i ∈ s, f i) e =
      ∏ i ∈ s, evalBoolSubstitute (f i) e := by
  rw [evalBoolSubstitute_eq_hom]
  simp_rw [evalBoolSubstitute_eq_hom]
  exact map_prod _ _ _

lemma evalBoolSubstitute_sum {R : Type*} [CommSemiring R]
    {σ ι : Type*} {m : ℕ} (e : Fin m → Bool)
    (s : Finset ι) (f : ι → MvPolynomial (σ ⊕ Fin m) R) :
    evalBoolSubstitute (∑ i ∈ s, f i) e =
      ∑ i ∈ s, evalBoolSubstitute (f i) e := by
  rw [evalBoolSubstitute_eq_hom]
  simp_rw [evalBoolSubstitute_eq_hom]
  exact map_sum _ _ _

lemma evalBoolSubstitute_neg {R : Type*} [CommRing R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool) (p : MvPolynomial (σ ⊕ Fin m) R) :
    evalBoolSubstitute (-p) e = -evalBoolSubstitute p e := by
  rw [evalBoolSubstitute_eq_hom, evalBoolSubstitute_eq_hom, map_neg]

lemma evalBoolSubstitute_sub {R : Type*} [CommRing R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool)
    (p q : MvPolynomial (σ ⊕ Fin m) R) :
    evalBoolSubstitute (p - q) e =
      evalBoolSubstitute p e - evalBoolSubstitute q e := by
  rw [evalBoolSubstitute_eq_hom, evalBoolSubstitute_eq_hom,
      evalBoolSubstitute_eq_hom, map_sub]

lemma evalBoolSubstitute_one {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool) :
    evalBoolSubstitute (1 : MvPolynomial (σ ⊕ Fin m) R) e = 1 := by
  rw [evalBoolSubstitute_eq_hom, map_one]

@[simp] lemma evalBoolSubstitute_natCast {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool) (k : ℕ) :
    evalBoolSubstitute ((k : MvPolynomial (σ ⊕ Fin m) R)) e =
      (k : MvPolynomial σ R) := by
  rw [evalBoolSubstitute_eq_hom, map_natCast]

@[simp] lemma evalBoolSubstitute_ofNat {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool) (k : ℕ) [k.AtLeastTwo] :
    evalBoolSubstitute
        (OfNat.ofNat k : MvPolynomial (σ ⊕ Fin m) R) e =
      (OfNat.ofNat k : MvPolynomial σ R) := by
  rw [evalBoolSubstitute_eq_hom, map_ofNat]

@[simp] lemma evalBoolSubstitute_two {R : Type*} [CommSemiring R]
    {σ : Type*} {m : ℕ} (e : Fin m → Bool) :
    evalBoolSubstitute (2 : MvPolynomial (σ ⊕ Fin m) R) e =
      (2 : MvPolynomial σ R) := by
  rw [evalBoolSubstitute_eq_hom, map_ofNat]

/-- **`VPSubsetVNP_arity`** — every VP family is a VNP family.

Construction: take `m := fun _ => 0` (no Boolean variables to sum over).
The Boolean cube `Fin 0 → Bool` is a singleton; the sum equals the value at
the single empty-function point; that value is the substitution-collapse of
`g n` (where `g` is `f` re-typed via `σ n ⊕ Fin 0`).

The circuit witness for `g` is built from `f`'s circuit via `mapInputs Sum.inl`. -/
theorem VPSubsetVNP_arity {R : Type*} [CommSemiring R] (σ : ℕ → Type*)
    (f : (n : ℕ) → MvPolynomial (σ n) R) (h : VPOverArity R σ f) :
    VNPOverArity R σ f := by
  obtain ⟨p, hp_bound, hp_circuit⟩ := h
  refine ⟨fun _ => 0,
          fun n => MvPolynomial.eval₂ MvPolynomial.C
                    (fun s : σ n => MvPolynomial.X (Sum.inl s : σ n ⊕ Fin 0)) (f n),
          ⟨0, fun _ => by simp⟩,
          ?_, ?_⟩
  · -- VPOverArity for the renamed g.
    -- For each n, take f's circuit and re-type via mapInputs Sum.inl.
    refine ⟨p, hp_bound, ?_⟩
    intro n
    obtain ⟨C, hC_size, hC_eq⟩ := hp_circuit n
    refine ⟨C.mapInputs Sum.inl, ?_, ?_⟩
    · rw [ArithmeticCircuit.mapInputs_size]; exact hC_size
    · rw [ArithmeticCircuit.mapInputs_toMvPolynomial, hC_eq]
  · -- Sum-substitution collapse via the helper lemma below.
    intro n
    rw [sum_fin_zero_bool]
    exact (evalBoolSubstitute_inl_id (f n)).symm

/-- **`VPSubsetVNP`** — the fixed-`Fin n` corollary. -/
theorem VPSubsetVNP {R : Type*} [CommSemiring R]
    (f : (n : ℕ) → MvPolynomial (Fin n) R) (h : VPOver R f) :
    VNPOver R f := by
  exact VPSubsetVNP_arity Fin f h

/-! ## permanent ∈ VNP — Round 2 -/

/-- The matrix-of-variables polynomial: for `n × n`, the entries are
`X_{(i,j)}` indexed by pairs `(i, j) : Fin n × Fin n`. -/
noncomputable def permanentVar (R : Type*) [CommSemiring R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) R :=
  Matrix.permanent (fun i j : Fin n => MvPolynomial.X (i, j))

/-! ### permanent_in_VNP_via_arity (Round 2 dispatch — placeholder section)

The permanent family lives in `VNPOverArity R (fun n => Fin n × Fin n)` —
i.e., per-`n` matrix-shaped variable index, no `Fin (n*n)` encoding needed.

The membership proof via Valiant's projection construction:

1. Index permutations σ : Fin n → Fin n by Boolean strings via the standard
   permutation→characteristic-function bijection (size n² Boolean variables).
2. The "is a permutation matrix" indicator (each row and column sums to 1)
   is computable by a polynomial-size circuit.
3. The product `∏_i X_{i, σ(i)}` rewrites as `∏_i ∑_j B_{i,j} · X_{i,j}`
   when `B` is a permutation matrix.
4. Substituting Boolean values for the `B_{i,j}` and summing recovers the permanent.

Round 2 dispatch will land the actual theorem and proof. -/

end Sheffer.ArithCircuit
