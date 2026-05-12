/-
# Sheffer.Foundations.MonodromyGroup — Path A.0a: monodromy as a group action

For a covering map `p : E → X` and basepoint `x : X`, define:
- `IsCoveringMap.monodromyPerm`: the monodromy of a homotopy-class loop as
  `Equiv.Perm (p ⁻¹' {x})`, derived from the bijectivity of `cov.monodromy`.
- `IsCoveringMap.monodromyHom`: the monodromy action as a group homomorphism
  `FundamentalGroup X x →* Equiv.Perm (p ⁻¹' {x})`.
- `IsCoveringMap.MonodromyGroup`: the image subgroup; the *monodromy group*
  of the covering at basepoint `x`.

Foundation for Path A (EML axiom-discharge via Khovanskii / topological Galois).
The next step (A.0b) is to define multivalued analytic functions and connect
the monodromy group of such functions' "covering of regular sheets" to
`MonodromyGroup` here.
-/

import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.Solvable

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X} (cov : IsCoveringMap p)

/-! ## Monodromy as a permutation -/

/-- The monodromy of a homotopy-class loop at `x` as an `Equiv.Perm (p ⁻¹' {x})`.

Built from `cov.monodromy γ` (a function) using its bijectivity
(`monodromy_bijective`) via `Equiv.ofBijective`. -/
noncomputable def monodromyPerm {x : X} (γ : Path.Homotopic.Quotient x x) :
    Equiv.Perm (p ⁻¹' {x}) :=
  Equiv.ofBijective (cov.monodromy γ) (cov.monodromy_bijective γ)

@[simp] theorem monodromyPerm_apply {x : X} (γ : Path.Homotopic.Quotient x x)
    (e : p ⁻¹' {x}) : cov.monodromyPerm γ e = cov.monodromy γ e := rfl

theorem monodromyPerm_refl {x : X} :
    cov.monodromyPerm (Path.Homotopic.Quotient.refl x) = 1 := by
  ext e
  simp only [monodromyPerm_apply, cov.monodromy_refl, id_eq,
             Equiv.Perm.one_apply]

theorem monodromyPerm_trans {x : X} (γ₁ γ₂ : Path.Homotopic.Quotient x x) :
    cov.monodromyPerm (γ₁.trans γ₂) =
      cov.monodromyPerm γ₂ * cov.monodromyPerm γ₁ := by
  -- monodromy_trans_apply: monodromy (γ.trans γ') = monodromy γ' ∘ monodromy γ
  -- Equiv.Perm.mul_apply: (f * g) x = f (g x) (right-to-left).
  -- So monodromyPerm (γ₁.trans γ₂) = monodromyPerm γ₂ * monodromyPerm γ₁.
  ext e
  simp only [monodromyPerm_apply, cov.monodromy_trans_apply,
             Equiv.Perm.mul_apply]

/-! ## Monodromy as a group homomorphism -/

/-- The monodromy homomorphism `π₁(X, x) → Equiv.Perm (p ⁻¹' {x})`.

The fundamental group is `End (FundamentalGroupoid.mk x)`; `γ.toPath` extracts
the underlying `Path.Homotopic.Quotient x x`.

**Convention reconciliation.** `End.mul_def : xs * ys = ys ≫ xs` (right-to-left
composition in End), and `FundamentalGroupoid.comp_eq : p ≫ q = p.trans q`. So
`(γ₁ * γ₂).toPath = γ₂.toPath.trans γ₁.toPath`. Combined with `monodromy_trans_apply`
(monodromy of `γ.trans γ'` is monodromy γ' ∘ monodromy γ) and Perm right-to-left
multiplication (`(f * g) x = f (g x)`): the conventions align and the raw monodromy
becomes a proper homomorphism. -/
noncomputable def monodromyHom (x : X) :
    FundamentalGroup X x →* Equiv.Perm (p ⁻¹' {x}) where
  toFun γ := cov.monodromyPerm γ.toPath
  map_one' := cov.monodromyPerm_refl
  map_mul' γ₁ γ₂ := by
    -- (γ₁ * γ₂) in End reduces to γ₂ ≫ γ₁ (End.mul_def); on FundamentalGroupoid
    -- this is γ₂.toPath.trans γ₁.toPath.
    have h : ((γ₁ * γ₂).toPath : Path.Homotopic.Quotient x x) =
             γ₂.toPath.trans γ₁.toPath := rfl
    change cov.monodromyPerm ((γ₁ * γ₂).toPath) = _
    rw [h, cov.monodromyPerm_trans]

@[simp] theorem monodromyHom_apply (x : X) (γ : FundamentalGroup X x)
    (e : p ⁻¹' {x}) :
    cov.monodromyHom x γ e = cov.monodromy γ.toPath e := rfl

/-! ## The monodromy group -/

/-- The **monodromy group** of the covering map `p` at basepoint `x` ∈ `X`:
the image of `FundamentalGroup X x` under the monodromy homomorphism. -/
noncomputable def MonodromyGroup (x : X) :
    Subgroup (Equiv.Perm (p ⁻¹' {x})) :=
  (cov.monodromyHom x).range

theorem mem_MonodromyGroup_iff (x : X) (σ : Equiv.Perm (p ⁻¹' {x})) :
    σ ∈ cov.MonodromyGroup x ↔
      ∃ γ : FundamentalGroup X x, cov.monodromyHom x γ = σ :=
  Iff.rfl

end IsCoveringMap
