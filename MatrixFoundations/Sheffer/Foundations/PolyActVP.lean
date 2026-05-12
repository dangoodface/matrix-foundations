import MatrixFoundations.Sheffer.Core
import MatrixFoundations.Sheffer.Foundations.ArithCircuit
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases

open Sheffer.ArithCircuit

/-
# Sheffer.Foundations.PolyActVP — bridge from polynomial-activation networks
to arithmetic circuits, with the conditional architectural bound.

Phase 4 deliverable. Three parts:

- **Phase 4.1 (this file core)**: `polyActToArithCircuit` — the load-bearing
  bridge. Given a `Term (PolyActBasis R k) m` (a polynomial-activation
  network with `m` inputs), construct an `ArithmeticCircuit R (Fin m)`
  computing the same multivariate polynomial. Plus a size-bound lemma.

- **Phase 4.2**: `polyAct_in_VP` — corollary: a polynomial-size
  polynomial-activation network represents a polynomial in VP, via the
  bridge.

- **Phase 4.3**: Theorems A and B — the conditional architectural bounds
  ("polyAct cannot represent permanent if perm ∉ VP", and the
  Valiant-conditional corollary using Round 2.3's `permanent_in_VNP_via_arity`).

## Generalization from `Examples/PolyAct.lean`

The existing `PolyActBasis` lives in `Examples/PolyAct.lean` over `ℝ`
specifically (used for the concrete obstruction-theory example
`x_pow_9_not_representable_at_depth_3`). Phase 4 needs a generalized
version over any `[CommRing R]`, so we redefine `PolyActBasis` here in
`Foundations.PolyActVP` namespace. The `Examples/PolyAct.lean` definitions
remain as-is (specialized to ℝ) for the obstruction-theory example. -/

namespace MinimalBasis.PolyActVP

open MinimalBasis

/-! ## Generalized `PolyActBasis` over an arbitrary commutative semiring -/

/-- Polynomial-activation operator: a univariate polynomial of degree ≤ k. -/
abbrev PolyActOp (R : Type) [CommSemiring R] (k : ℕ) : Type _ :=
  { p : Polynomial R // p.natDegree ≤ k }

/-- The polynomial-activation operator basis at degree `k` over `R`. Single
arity-1 operator family (each operator is a univariate polynomial of
degree ≤ k). -/
noncomputable def PolyActBasis (R : Type) [CommSemiring R] (k : ℕ) :
    MinimalBasis.OperatorBasis R where
  Op := PolyActOp R k
  arity _ := 1
  eval p args := p.val.eval (args 0)

/-! ## Multivariate polynomial extraction — `Term.toMvPoly`

Given a `Term (PolyActBasis R k) m` (a polynomial-activation network with
`m` inputs from `R`), extract the multivariate polynomial in
`MvPolynomial (Fin m) R` it computes. Recursive structural definition:

- `Term.const c` → `MvPolynomial.C c`
- `Term.var i` → `MvPolynomial.X i`
- `Term.app op kids` → substitute the child's MvPoly into op's univariate
  polynomial via `Polynomial.eval₂ MvPolynomial.C`. -/

/-- Helper: the single child index for arity-1 operators in `PolyActBasis R k`. -/
def singleChild {R : Type} [CommSemiring R] {k : ℕ}
    (op : (PolyActBasis R k).Op) : Fin ((PolyActBasis R k).arity op) := by
  refine ⟨0, ?_⟩
  change 0 < 1
  decide

/-- The multivariate polynomial computed by a polynomial-activation
network. -/
noncomputable def Term.toMvPoly {R : Type} [CommSemiring R] {k m : ℕ} :
    MinimalBasis.Term (PolyActBasis R k) m → MvPolynomial (Fin m) R
  | .const c     => MvPolynomial.C c
  | .var i       => MvPolynomial.X i
  | .app op kids =>
    Polynomial.eval₂ MvPolynomial.C
      (Term.toMvPoly (kids (singleChild op))) op.val

/-! ## Phase 4.1 — Bridge `polyActToArithCircuit`

Construct an `ArithmeticCircuit R (Fin m)` that computes the same polynomial
as a `Term (PolyActBasis R k) m`. Recursive structural construction:

- `Term.const c` → `ArithmeticCircuit.const c`
- `Term.var i` → `ArithmeticCircuit.input i`
- `Term.app op kids` → expand `op.val` (a univariate polynomial in
  `Polynomial R`) as a sum of monomials, each a product of
  `(child.toCircuit)`-powers, summed into one circuit.

The polynomial expansion uses `op.val.coeff j * X^j` summed over `j ∈ Fin (k+1)`.
For each `j`, we build `(.const (op.val.coeff j)) * child^j` and sum the
results. Net circuit size for one `app` node: `O(k²)` gates — `k+1` monomials,
each ≤ `k` multiplications + 1 const + 1 add. -/

/-- Build a circuit computing `child^j` (j-fold self-product) of a child
circuit. -/
private def powCircuit {R : Type} [CommSemiring R] {σ : Type*}
    (child : ArithmeticCircuit R σ) : ℕ → ArithmeticCircuit R σ
  | 0     => .const 1
  | j + 1 => .mul child (powCircuit child j)

/-- The `j`-th monomial of the polynomial expansion: `(C coeff_j) * child^j`. -/
private noncomputable def monomialCircuit {R : Type} [CommSemiring R] {σ : Type*}
    (coeff_j : R) (child : ArithmeticCircuit R σ) (j : ℕ) :
    ArithmeticCircuit R σ :=
  .mul (.const coeff_j) (powCircuit child j)

/-- Build a circuit computing `p` evaluated at the child circuit:
`∑_{j=0}^{p.natDegree} (p.coeff j) · child^j`. The iteration uses
`p.natDegree + 1` terms; `p.coeff j = 0` for `j > p.natDegree` so the
bound is exact regardless of the upstream degree-bound parameter. -/
private noncomputable def applyOpCircuit {R : Type} [CommSemiring R] {σ : Type*}
    (p : Polynomial R) (child : ArithmeticCircuit R σ) :
    ArithmeticCircuit R σ :=
  ArithmeticCircuit.listAdd
    ((List.range (p.natDegree + 1)).map
      (fun j => monomialCircuit (p.coeff j) child j))

/-- The bridge: convert a polynomial-activation network to an arithmetic
circuit computing the same multivariate polynomial. -/
noncomputable def polyActToArithCircuit {R : Type} [CommSemiring R] {k m : ℕ} :
    MinimalBasis.Term (PolyActBasis R k) m → ArithmeticCircuit R (Fin m)
  | .const c     => .const c
  | .var i       => .input i
  | .app op kids =>
    applyOpCircuit op.val (polyActToArithCircuit (kids (singleChild op)))

/-! ## Bridge correctness

Three sub-lemmas culminate in `polyActToArithCircuit_toMvPolynomial`:
- `powCircuit_toMvPolynomial`:
  `(powCircuit child j).toMvPolynomial = child.toMvPolynomial ^ j`
- `monomialCircuit_toMvPolynomial`:
  `(monomialCircuit c child j).toMvPolynomial = C c * child.toMvPolynomial^j`
- `applyOpCircuit_toMvPolynomial`:
  `(applyOpCircuit p child).toMvPolynomial =
     Polynomial.eval₂ C child.toMvPolynomial p` -/

private lemma powCircuit_toMvPolynomial {R : Type} [CommSemiring R] {σ : Type*}
    (child : ArithmeticCircuit R σ) (j : ℕ) :
    (powCircuit child j).toMvPolynomial = child.toMvPolynomial ^ j := by
  induction j with
  | zero => simp [powCircuit, ArithmeticCircuit.toMvPolynomial]
  | succ j ih =>
    change (ArithmeticCircuit.mul child (powCircuit child j)).toMvPolynomial = _
    simp [ArithmeticCircuit.toMvPolynomial, ih, pow_succ, mul_comm]

private lemma monomialCircuit_toMvPolynomial {R : Type} [CommSemiring R]
    {σ : Type*} (c : R) (child : ArithmeticCircuit R σ) (j : ℕ) :
    (monomialCircuit c child j).toMvPolynomial =
      MvPolynomial.C c * child.toMvPolynomial ^ j := by
  unfold monomialCircuit
  simp [ArithmeticCircuit.toMvPolynomial, powCircuit_toMvPolynomial]

private lemma applyOpCircuit_toMvPolynomial {R : Type} [CommSemiring R]
    {σ : Type*} (p : Polynomial R) (child : ArithmeticCircuit R σ) :
    (applyOpCircuit p child).toMvPolynomial =
      Polynomial.eval₂ MvPolynomial.C child.toMvPolynomial p := by
  unfold applyOpCircuit
  rw [ArithmeticCircuit.listAdd_toMvPolynomial]
  rw [List.map_map]
  rw [show (List.range (p.natDegree + 1)).map
      (ArithmeticCircuit.toMvPolynomial ∘
        fun j => monomialCircuit (p.coeff j) child j) =
      (List.range (p.natDegree + 1)).map
        (fun j => MvPolynomial.C (p.coeff j) * child.toMvPolynomial ^ j) from by
    apply List.map_congr_left
    intros j _
    exact monomialCircuit_toMvPolynomial (p.coeff j) child j]
  -- Goal: ((range (p.natDegree+1)).map (fun j => C (p.coeff j) * child^j)).sum
  --     = Polynomial.eval₂ C child p
  -- Polynomial.eval₂_eq_sum_range expands eval₂ as a Finset sum over range.
  rw [Polynomial.eval₂_eq_sum_range]
  -- Reconcile List sum and Finset sum: Finset.range n's underlying multiset
  -- is the coercion of List.range n.
  rw [show (∑ j ∈ Finset.range (p.natDegree + 1),
        MvPolynomial.C (p.coeff j) * child.toMvPolynomial ^ j) =
      ((List.range (p.natDegree + 1)).map
        (fun j => MvPolynomial.C (p.coeff j) * child.toMvPolynomial ^ j)).sum
        from by
    rw [Finset.sum_eq_multiset_sum]
    rw [show (Finset.range (p.natDegree + 1)).val =
        ↑(List.range (p.natDegree + 1)) from by
      rw [Finset.range_val, Multiset.coe_range]]
    rfl]

theorem polyActToArithCircuit_toMvPolynomial {R : Type} [CommSemiring R]
    {k m : ℕ} (T : MinimalBasis.Term (PolyActBasis R k) m) :
    (polyActToArithCircuit T).toMvPolynomial = Term.toMvPoly T := by
  induction T with
  | const c => simp [polyActToArithCircuit, ArithmeticCircuit.toMvPolynomial,
                     Term.toMvPoly]
  | var i => simp [polyActToArithCircuit, ArithmeticCircuit.toMvPolynomial,
                   Term.toMvPoly]
  | app op kids ih =>
    change (applyOpCircuit op.val
      (polyActToArithCircuit (kids (singleChild op)))).toMvPolynomial = _
    rw [applyOpCircuit_toMvPolynomial]
    rw [ih (singleChild op)]
    rfl

/-! ## Term size — number of nodes in a polynomial-activation network -/

/-- Structural size: count of all leaves and internal nodes in the term.
Lives in `MinimalBasis.Term` namespace via `_root_` so dot-notation
`T.polyActSize` resolves. -/
def _root_.MinimalBasis.Term.polyActSize {R : Type} [CommSemiring R] {k m : ℕ} :
    MinimalBasis.Term (PolyActBasis R k) m → ℕ
  | .const _     => 1
  | .var _       => 1
  | .app op kids => 1 + (kids (singleChild op)).polyActSize

/-! ## Circuit size bound

For a `Term (PolyActBasis R k) m` of structural size `s`, the bridge
produces a circuit of size at most `s * ((k+1)*(k+2) + 1) + 1`. The key
observation is that each `.app` node adds `O(k²)` gates (the
`applyOpCircuit` expansion of the polynomial activation), and the term
has at most `s - 1` `.app` nodes. -/

private lemma powCircuit_size {R : Type} [CommSemiring R] {σ : Type*}
    (child : ArithmeticCircuit R σ) (j : ℕ) :
    (powCircuit child j).size = j * (1 + child.size) := by
  induction j with
  | zero => simp [powCircuit, ArithmeticCircuit.size]
  | succ j ih =>
    change (ArithmeticCircuit.mul child (powCircuit child j)).size = _
    simp [ArithmeticCircuit.size, ih]; ring

private lemma monomialCircuit_size {R : Type} [CommSemiring R] {σ : Type*}
    (c : R) (child : ArithmeticCircuit R σ) (j : ℕ) :
    (monomialCircuit c child j).size = 1 + j * (1 + child.size) := by
  unfold monomialCircuit
  simp [ArithmeticCircuit.size, powCircuit_size]

private lemma applyOpCircuit_size_le {R : Type} [CommSemiring R] {σ : Type*}
    (p : Polynomial R) (child : ArithmeticCircuit R σ) :
    (applyOpCircuit p child).size ≤
      (p.natDegree + 1) * ((p.natDegree + 1) * (1 + child.size) + 2) := by
  unfold applyOpCircuit
  rw [ArithmeticCircuit.listAdd_size]
  rw [List.length_map, List.length_range]
  rw [List.map_map]
  -- (cs.map size).sum where each element has size 1 + j*(1+child.size) for j ≤ p.natDegree
  -- sum ≤ (p.natDegree+1) * (1 + p.natDegree * (1+child.size))
  have h_per : ∀ j ∈ List.range (p.natDegree + 1),
      (ArithmeticCircuit.size ∘
        fun j => monomialCircuit (p.coeff j) child j) j ≤
        1 + p.natDegree * (1 + child.size) := by
    intros j hj
    simp [Function.comp, monomialCircuit_size]
    rw [List.mem_range] at hj
    have hj' : j ≤ p.natDegree := by omega
    nlinarith [Nat.zero_le child.size, Nat.zero_le j]
  have h_sum_le : ((List.range (p.natDegree + 1)).map
      (ArithmeticCircuit.size ∘
        fun j => monomialCircuit (p.coeff j) child j)).sum ≤
      (p.natDegree + 1) * (1 + p.natDegree * (1 + child.size)) := by
    calc ((List.range (p.natDegree + 1)).map
            (ArithmeticCircuit.size ∘
              fun j => monomialCircuit (p.coeff j) child j)).sum
        ≤ ((List.range (p.natDegree + 1)).map
            (fun _ => 1 + p.natDegree * (1 + child.size))).sum := by
          apply List.sum_le_sum
          · intros j hj
            exact h_per j hj
      _ = (p.natDegree + 1) * (1 + p.natDegree * (1 + child.size)) := by
          rw [show (fun _ : ℕ => 1 + p.natDegree * (1 + child.size)) =
              Function.const ℕ (1 + p.natDegree * (1 + child.size)) from rfl]
          rw [List.map_const, List.length_range, List.sum_replicate, smul_eq_mul]
  calc p.natDegree + 1 + ((List.range (p.natDegree + 1)).map
        (ArithmeticCircuit.size ∘
          fun j => monomialCircuit (p.coeff j) child j)).sum
      ≤ p.natDegree + 1 + (p.natDegree + 1) * (1 + p.natDegree * (1 + child.size)) := by
        omega
    _ ≤ (p.natDegree + 1) * ((p.natDegree + 1) * (1 + child.size) + 2) := by
        nlinarith

/-! ## Term depth — for log-depth size analysis

The bridge size grows multiplicatively per `.app` node (each polynomial
expansion duplicates the child circuit `O(k²)` times). Polynomial-size
networks of *log-depth* therefore produce polynomial-size circuits;
poly-depth networks produce super-polynomial circuits. We use depth
rather than `polyActSize` for the log-depth size bound. -/

/-- Structural depth of a polynomial-activation network. For arity-1
networks this equals the number of `.app` nodes from root to leaf. -/
def _root_.MinimalBasis.Term.polyActDepth {R : Type} [CommSemiring R] {k m : ℕ} :
    MinimalBasis.Term (PolyActBasis R k) m → ℕ
  | .const _     => 0
  | .var _       => 0
  | .app op kids => 1 + (kids (singleChild op)).polyActDepth

/-- Recursive size bound: at depth `d` over a degree-`k` activation basis,
the bridge produces a circuit of size at most `polyActSizeBound k d`,
where the recurrence captures the per-`.app` multiplicative blowup. -/
def polyActSizeBound (k : ℕ) : ℕ → ℕ
  | 0     => 0
  | d + 1 => (k + 1) * ((k + 1) * (1 + polyActSizeBound k d) + 2)

/-- Size bound: the bridge's circuit size is bounded by the recursive
`polyActSizeBound` evaluated at the term's depth. -/
theorem polyActToArithCircuit_size_le {R : Type} [CommSemiring R] {k m : ℕ}
    (T : MinimalBasis.Term (PolyActBasis R k) m) :
    (polyActToArithCircuit T).size ≤ polyActSizeBound k T.polyActDepth := by
  induction T with
  | const c =>
    simp [polyActToArithCircuit, ArithmeticCircuit.size,
          MinimalBasis.Term.polyActDepth, polyActSizeBound]
  | var i =>
    simp [polyActToArithCircuit, ArithmeticCircuit.size,
          MinimalBasis.Term.polyActDepth, polyActSizeBound]
  | app op kids ih =>
    change (applyOpCircuit op.val
      (polyActToArithCircuit (kids (singleChild op)))).size ≤ _
    have h_natDeg : op.val.natDegree ≤ k := op.property
    have h_apply := applyOpCircuit_size_le op.val
      (polyActToArithCircuit (kids (singleChild op)))
    have h_child := ih (singleChild op)
    -- Combine: (op.natDegree + 1) ≤ (k + 1), and use h_child + h_apply.
    change (applyOpCircuit op.val
      (polyActToArithCircuit (kids (singleChild op)))).size ≤
      polyActSizeBound k (1 + (kids (singleChild op)).polyActDepth)
    rw [show polyActSizeBound k (1 + (kids (singleChild op)).polyActDepth) =
        (k + 1) * ((k + 1) *
          (1 + polyActSizeBound k (kids (singleChild op)).polyActDepth) + 2)
        from by
      rw [show 1 + (kids (singleChild op)).polyActDepth =
          (kids (singleChild op)).polyActDepth + 1 from by omega]
      rfl]
    calc (applyOpCircuit op.val
            (polyActToArithCircuit (kids (singleChild op)))).size
        ≤ (op.val.natDegree + 1) * ((op.val.natDegree + 1) *
            (1 + (polyActToArithCircuit (kids (singleChild op))).size) + 2) :=
          h_apply
      _ ≤ (k + 1) * ((k + 1) *
            (1 + polyActSizeBound k (kids (singleChild op)).polyActDepth) + 2) := by
          have h1 : op.val.natDegree + 1 ≤ k + 1 := by omega
          have h2 : 1 + (polyActToArithCircuit (kids (singleChild op))).size ≤
              1 + polyActSizeBound k (kids (singleChild op)).polyActDepth := by
            omega
          have h_inner : (op.val.natDegree + 1) *
              (1 + (polyActToArithCircuit (kids (singleChild op))).size) ≤
              (k + 1) *
              (1 + polyActSizeBound k (kids (singleChild op)).polyActDepth) :=
            Nat.mul_le_mul h1 h2
          have h_inner2 : (op.val.natDegree + 1) *
              (1 + (polyActToArithCircuit (kids (singleChild op))).size) + 2 ≤
              (k + 1) *
              (1 + polyActSizeBound k (kids (singleChild op)).polyActDepth) + 2 :=
            Nat.add_le_add_right h_inner 2
          exact Nat.mul_le_mul h1 h_inner2

/-! ## Phase 4.2 — `polyAct_in_VP_log_depth`

For log-depth polynomial-activation networks, the bridge produces
polynomial-size circuits, hence the network's polynomial is in VP.

The proof composes:
- `polyActToArithCircuit_size_le`: size is bounded by `polyActSizeBound k T.polyActDepth`
- `polyActToArithCircuit_toMvPolynomial`: the circuit computes the right polynomial
- A polynomial-bound chain showing `polyActSizeBound k (c · Nat.log2 n)` is
  polynomial in `n` (the load-bearing arithmetic, sorried for now). -/

/-- Closed-form upper bound: `polyActSizeBound k d ≤ (k+2)^(2d+1)`.

Proof by induction on `d`. The recurrence
`s_{d+1} = (k+1)²(1 + s_d) + 2(k+1)` is dominated by `(k+2)^(2d+3)` when
`s_d ≤ (k+2)^(2d+1)`, using `(k+2)² - (k+1)² = 2k+3` and small algebra. -/
theorem polyActSizeBound_le_pow (k d : ℕ) :
    polyActSizeBound k d ≤ (k + 2) ^ (2 * d + 1) := by
  induction d with
  | zero => simp [polyActSizeBound]
  | succ d ih =>
    change polyActSizeBound k (d + 1) ≤ (k + 2) ^ (2 * (d + 1) + 1)
    -- s_{d+1} = (k+1)²(1+s_d) + 2(k+1); bounded above by (k+2)^(2d+3)
    have h_pow_succ : (k + 2) ^ (2 * (d + 1) + 1) =
        (k + 2) ^ (2 * d + 1) * ((k + 2) * (k + 2)) := by
      rw [show 2 * (d + 1) + 1 = (2 * d + 1) + 2 from by omega, pow_add]
      ring
    rw [h_pow_succ]
    -- Need: (k+1) * ((k+1)*(1+s_d) + 2) ≤ (k+2)^(2d+1) * (k+2)²
    -- i.e., (k+1)² + (k+1)² * s_d + 2(k+1) ≤ (k+2)² * (k+2)^(2d+1)
    -- = (k+1)²(k+2)^(2d+1) + (2k+3)(k+2)^(2d+1)
    -- So need (k+1)² + 2(k+1) ≤ (2k+3) * (k+2)^(2d+1) - (k+1)²((k+2)^(2d+1)-s_d)
    -- Simpler: use s_d ≤ (k+2)^(2d+1) to get (k+1)²*s_d ≤ (k+1)²*(k+2)^(2d+1).
    -- Then need (k+1)² + 2(k+1) ≤ (2k+3) * (k+2)^(2d+1).
    -- (k+2)^(2d+1) ≥ k+2, so (2k+3)(k+2)^(2d+1) ≥ (2k+3)(k+2) = 2k²+7k+6.
    -- (k+1)² + 2(k+1) = k²+4k+3 ≤ 2k²+7k+6.
    have h_pow_ge : (k + 2) ≤ (k + 2) ^ (2 * d + 1) := by
      have : (k + 2) ^ 1 ≤ (k + 2) ^ (2 * d + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    have h_arith : (k + 1) ^ 2 + 2 * (k + 1) ≤ (2 * k + 3) * (k + 2) := by
      nlinarith
    have h_arith2 : (k + 1) ^ 2 + 2 * (k + 1) ≤ (2 * k + 3) * (k + 2) ^ (2 * d + 1) := by
      calc (k + 1) ^ 2 + 2 * (k + 1)
          ≤ (2 * k + 3) * (k + 2) := h_arith
        _ ≤ (2 * k + 3) * (k + 2) ^ (2 * d + 1) :=
              Nat.mul_le_mul_left _ h_pow_ge
    have h_main : (k + 1) * ((k + 1) * (1 + polyActSizeBound k d) + 2) ≤
        (k + 2) ^ (2 * d + 1) * ((k + 2) * (k + 2)) := by
      have h1 : (k + 1) ^ 2 * polyActSizeBound k d ≤
          (k + 1) ^ 2 * (k + 2) ^ (2 * d + 1) := Nat.mul_le_mul_left _ ih
      nlinarith [h1, h_arith2, ih, sq_nonneg (k + 1), sq_nonneg (k + 2),
                 Nat.zero_le (polyActSizeBound k d)]
    exact h_main

/-- Polynomial-bound for the size bound under log-depth restriction.
For depth `d ≤ c · Nat.log2 n` and fixed `k`, `polyActSizeBound k d ≤
(k+2)^(2d+1) ≤ (k+2)^(2c·log₂ n + 1)`, which is polynomial in `n`. -/
theorem polyActSizeBound_log_depth_poly (k c : ℕ) :
    ∃ K : ℕ, ∀ n d, d ≤ c * Nat.log2 n →
      polyActSizeBound k d ≤ n ^ K + K := by
  -- Witness K large enough to dominate (k+2) * n^(...) plus base cases.
  refine ⟨Nat.log 2 ((k + 2) ^ (2 * c)) + (k + 2) + 2, ?_⟩
  intros n d hd
  set K := Nat.log 2 ((k + 2) ^ (2 * c)) + (k + 2) + 2
  -- Step 1: polyActSizeBound k d ≤ (k+2)^(2d+1)
  have h_step1 : polyActSizeBound k d ≤ (k + 2) ^ (2 * d + 1) :=
    polyActSizeBound_le_pow k d
  -- Step 2: 2*d + 1 ≤ 2c * Nat.log2 n + 1, hence (k+2)^(2d+1) ≤ (k+2)^(2c*Nat.log2 n + 1)
  have h_step2 : (k + 2) ^ (2 * d + 1) ≤ (k + 2) ^ (2 * c * Nat.log2 n + 1) := by
    apply Nat.pow_le_pow_right (by omega : 1 ≤ k + 2)
    have : 2 * d ≤ 2 * c * Nat.log2 n := by
      have : 2 * d ≤ 2 * (c * Nat.log2 n) := Nat.mul_le_mul_left 2 hd
      linarith
    omega
  -- Step 3: case split on n
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- n = 0: hd gives d ≤ c * Nat.log2 0 = 0, so polyActSizeBound k 0 = 0
    subst hn0
    simp [Nat.log2_zero] at hd
    simp [hd, polyActSizeBound]
  -- n ≥ 1
  -- Step 4: (k+2)^(2c*Nat.log2 n + 1) = (k+2) * ((k+2)^(2c))^(Nat.log2 n)
  have h_step4 : (k + 2) ^ (2 * c * Nat.log2 n + 1) =
      (k + 2) * ((k + 2) ^ (2 * c)) ^ (Nat.log2 n) := by
    rw [show 2 * c * Nat.log2 n + 1 = 1 + (2 * c) * Nat.log2 n from by ring]
    rw [pow_add, pow_mul, pow_one]
  -- Step 5: ((k+2)^(2c))^(Nat.log2 n) ≤ n^(Nat.log 2 ((k+2)^(2c)) + 1)
  have h_step5 : ((k + 2) ^ (2 * c)) ^ (Nat.log2 n) ≤
      n ^ (Nat.log 2 ((k + 2) ^ (2 * c)) + 1) := by
    have hM_lt : (k + 2) ^ (2 * c) < 2 ^ (Nat.log 2 ((k + 2) ^ (2 * c)) + 1) :=
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) _
    have h_2_log_n : 2 ^ (Nat.log 2 n) ≤ n :=
      Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · interval_cases n
      simp [Nat.log2_eq_log_two, Nat.log_one_right]
    · calc ((k + 2) ^ (2 * c)) ^ (Nat.log2 n)
          ≤ (2 ^ (Nat.log 2 ((k + 2) ^ (2 * c)) + 1)) ^ (Nat.log2 n) := by
            apply Nat.pow_le_pow_left
            omega
        _ = (2 ^ (Nat.log2 n)) ^ (Nat.log 2 ((k + 2) ^ (2 * c)) + 1) := by
            rw [Nat.log2_eq_log_two, ← pow_mul, ← pow_mul, mul_comm]
        _ ≤ n ^ (Nat.log 2 ((k + 2) ^ (2 * c)) + 1) := by
            rw [Nat.log2_eq_log_two]
            exact Nat.pow_le_pow_left h_2_log_n _
  -- Step 6: combine
  have h_combined : (k + 2) * ((k + 2) ^ (2 * c)) ^ (Nat.log2 n) ≤
      (k + 2) * n ^ (Nat.log 2 ((k + 2) ^ (2 * c)) + 1) :=
    Nat.mul_le_mul_left _ h_step5
  -- Step 7: (k+2) * n^(M+1) ≤ n^K (for n ≥ 2 and K ≥ M+1+(k+2))
  -- Or equivalently ≤ n^K + K (looser bound)
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · -- n = 1: bound trivially ≤ K
    interval_cases n
    -- d ≤ c * Nat.log2 1 = 0
    simp [Nat.log2_eq_log_two, Nat.log_one_right] at hd
    simp [hd, polyActSizeBound]
  · -- n ≥ 2
    have h_n_pow_kplus2 : k + 2 ≤ n ^ (k + 2) := by
      have : 2 ^ (k + 2) ≤ n ^ (k + 2) := Nat.pow_le_pow_left hn2 _
      have h_2pow : k + 2 ≤ 2 ^ (k + 2) := Nat.lt_two_pow_self.le
      omega
    have h_final : (k + 2) * n ^ (Nat.log 2 ((k + 2) ^ (2 * c)) + 1) ≤ n ^ K := by
      have h_factor : (k + 2) ≤ n ^ (k + 2) * n := by
        calc k + 2 ≤ n ^ (k + 2) := h_n_pow_kplus2
          _ ≤ n ^ (k + 2) * n := Nat.le_mul_of_pos_right _ (by omega : 0 < n)
      -- Rewrite n^K via explicit pow chain (using conv_rhs to avoid over-rewriting).
      have hPow : n ^ K = n ^ (Nat.log 2 ((k + 2) ^ (2 * c)) + 1) *
          n ^ (k + 2) * n := by
        change n ^ (Nat.log 2 ((k + 2) ^ (2 * c)) + (k + 2) + 2) = _
        rw [show Nat.log 2 ((k + 2) ^ (2 * c)) + (k + 2) + 2 =
            (Nat.log 2 ((k + 2) ^ (2 * c)) + 1) + (k + 2) + 1 from by omega]
        rw [pow_succ, pow_add]
      rw [hPow]
      -- Goal: (k+2) * X ≤ X * n^(k+2) * n with h_factor.
      set X := n ^ (Nat.log 2 ((k + 2) ^ (2 * c)) + 1) with _hX_def
      calc (k + 2) * X
          ≤ (n ^ (k + 2) * n) * X := Nat.mul_le_mul_right _ h_factor
        _ = X * (n ^ (k + 2) * n) := mul_comm _ _
        _ = X * n ^ (k + 2) * n := (mul_assoc _ _ _).symm
    calc polyActSizeBound k d
        ≤ (k + 2) ^ (2 * d + 1) := h_step1
      _ ≤ (k + 2) ^ (2 * c * Nat.log2 n + 1) := h_step2
      _ = (k + 2) * ((k + 2) ^ (2 * c)) ^ (Nat.log2 n) := h_step4
      _ ≤ (k + 2) * n ^ (Nat.log 2 ((k + 2) ^ (2 * c)) + 1) := h_combined
      _ ≤ n ^ K := h_final
      _ ≤ n ^ K + K := Nat.le_add_right _ _

/-- **Phase 4.2 — `polyAct_in_VP_log_depth`.** A log-depth
polynomial-activation network family produces a polynomial in VP.

Hypotheses:
- `T n` is a polynomial-activation network with `m n` inputs.
- `(T n).polyActDepth ≤ c · Nat.log2 n` for some constant `c`.

Conclusion: the family `n ↦ (T n).toMvPoly` is in `VPOverArity`. -/
theorem polyAct_in_VP_log_depth {R : Type} [CommRing R] {k c : ℕ}
    {m : ℕ → ℕ} (T : (n : ℕ) → MinimalBasis.Term (PolyActBasis R k) (m n))
    (h_depth : ∀ n, (T n).polyActDepth ≤ c * Nat.log2 n) :
    Sheffer.ArithCircuit.VPOverArity R (fun n => Fin (m n))
      (fun n => MinimalBasis.PolyActVP.Term.toMvPoly (T n)) := by
  obtain ⟨K, hK⟩ := polyActSizeBound_log_depth_poly k c
  refine ⟨fun n => n ^ K + K, ⟨K, fun n => ?_⟩, fun n => ?_⟩
  · -- IsPolyBound: n^K + K ≤ n^K + K (refl)
    exact le_refl _
  · refine ⟨polyActToArithCircuit (T n), ?_, polyActToArithCircuit_toMvPolynomial (T n)⟩
    calc (polyActToArithCircuit (T n)).size
        ≤ polyActSizeBound k (T n).polyActDepth :=
          polyActToArithCircuit_size_le (T n)
      _ ≤ n ^ K + K := hK n (T n).polyActDepth (h_depth n)

/-! ## Phase 4.3 — Theorems A and B (architectural bounds)

**Theorem A** (direct form): if the target polynomial family is not in VP,
no log-depth polynomial-activation network family represents it.
Contrapositive of `polyAct_in_VP_log_depth`.

**Theorem B** (Valiant-conditional corollary): combining Theorem A with
Round 2.3's `permanent_in_VNP_via_arity`, conditional on Valiant's
hypothesis (VP ≠ VNP), no log-depth polynomial-activation network
represents the permanent. -/

/-- **Theorem A.** No log-depth polynomial-activation network represents
a target polynomial that lies outside VP. -/
theorem polyAct_cannot_represent_target_not_in_VP {R : Type} [CommRing R]
    {m : ℕ → ℕ} (target : (n : ℕ) → MvPolynomial (Fin (m n)) R)
    (h_target_not_VP :
      ¬ Sheffer.ArithCircuit.VPOverArity R (fun n => Fin (m n)) target) :
    ¬ ∃ (k c : ℕ) (T : (n : ℕ) → MinimalBasis.Term (PolyActBasis R k) (m n)),
        (∀ n, (T n).polyActDepth ≤ c * Nat.log2 n) ∧
        (∀ n, MinimalBasis.PolyActVP.Term.toMvPoly (T n) = target n) := by
  rintro ⟨k, c, T, h_depth, h_eq⟩
  apply h_target_not_VP
  have h_target_eq :
      (fun n => MinimalBasis.PolyActVP.Term.toMvPoly (T n)) = target := by
    funext n; exact h_eq n
  rw [← h_target_eq]
  exact polyAct_in_VP_log_depth T h_depth

/-- **Theorem B (corollary).** Specialized to the permanent: if the
permanent is not in VP, no log-depth polynomial-activation network
represents the permanent (after re-indexing the matrix-shaped variables
to a flat `Fin (n*n)` index via `finProdFinEquiv`).

Note: a Valiant-conditional version "VP ≠ VNP ⟹ permanent ∉ VP ⟹ this
conclusion" requires `permanent`'s VNP-completeness (Round 3 / Valiant
hardness reduction), which is sequel work. The current theorem ships as
"if permanent ∉ VP." Round 2.3's `permanent_in_VNP_via_arity` shows
`permanent ∈ VNP`, so `permanent ∉ VP` is the operative non-trivial
hypothesis for the architectural bound. -/
theorem polyAct_cannot_represent_permanent_if_perm_not_in_VP
    (R : Type) [CommRing R]
    (h_perm : ¬ Sheffer.ArithCircuit.VPOverArity R (fun n => Fin (n * n))
      (fun n => MvPolynomial.rename
        (Equiv.toFun (finProdFinEquiv (m := n) (n := n)))
        (Sheffer.ArithCircuit.permanentVar R n))) :
    ¬ ∃ (k c : ℕ)
        (T : (n : ℕ) → MinimalBasis.Term (PolyActBasis R k) (n * n)),
        (∀ n, (T n).polyActDepth ≤ c * Nat.log2 n) ∧
        (∀ n, MinimalBasis.PolyActVP.Term.toMvPoly (T n) =
          MvPolynomial.rename
            (Equiv.toFun (finProdFinEquiv (m := n) (n := n)))
            (Sheffer.ArithCircuit.permanentVar R n)) :=
  polyAct_cannot_represent_target_not_in_VP _ h_perm

end MinimalBasis.PolyActVP
