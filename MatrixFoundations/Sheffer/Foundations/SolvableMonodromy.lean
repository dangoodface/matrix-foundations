/-
# Sheffer.Foundations.SolvableMonodromy — Path A.0c: concrete `hasSolvableMonodromy`

Replaces the opaque `EML.hasSolvableMonodromy` (in `Sheffer/Examples/Eml.lean`)
with a concrete definition based on A.0b's `MultivaluedAnalytic`:

> A real function `f : (Fin n → ℝ) → ℝ` has solvable monodromy iff there
> exists a `MultivaluedAnalytic n` extension `F` of `f` such that `F`'s
> monodromy group is solvable.

"Extension" here means: when `F.value` is evaluated at points in the image of
`(ℝⁿ ↪ ℂⁿ)` (the real embedding), it agrees with `f` on the corresponding
single-valued real branch.

Once this is in place, the four EML Path-B axioms (`const_solvableMonodromy`,
`var_solvableMonodromy`, `eml_preserves_solvableMonodromy`,
`quinticRoot_not_solvableMonodromy`) become *theorems* discharged in A.1, A.2,
A.3 respectively.
-/

import MatrixFoundations.Sheffer.Foundations.MultivaluedAnalytic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.GroupTheory.Solvable

namespace Path_A

/-! ## Helper: identity is a covering map

Mathlib doesn't have `IsCoveringMap.id` directly. We construct it here for the
trivial-cover constructions used in `constAsMultivalued`, `varAsMultivalued`,
and inner pieces of `expAsMultivalued`. -/

/-- The identity map is a covering map (trivially, with single-point fibers). -/
theorem id_isCoveringMap {X : Type*} [TopologicalSpace X] :
    IsCoveringMap (id : X → X) := by
  intro x
  -- IsEvenlyCovered id x (id ⁻¹' {x}):
  -- The fiber over x is the subsingleton {z : X // z = x}.
  haveI hsub : Subsingleton (↥(id ⁻¹' {x} : Set X)) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have ha : a.val = x := a.property
    have hb : b.val = x := b.property
    rw [ha, hb]
  refine ⟨inferInstance, Set.univ, Set.mem_univ x, isOpen_univ, isOpen_univ, ?_, ?_⟩
  · -- The equiv id⁻¹' univ ≃ₜ univ × (id ⁻¹' {x}).
    let H : (↥(id ⁻¹' (Set.univ : Set X))) ≃ₜ
            (↥(Set.univ : Set X)) × ↥(id ⁻¹' {x} : Set X) := {
      toFun := fun u => (⟨u.val, trivial⟩, ⟨x, rfl⟩)
      invFun := fun p => ⟨p.1.val, trivial⟩
      left_inv := fun u => rfl
      right_inv := fun p => by
        refine Prod.ext rfl ?_
        exact Subtype.ext p.2.property.symm
      continuous_toFun := by
        apply Continuous.prodMk
        · exact (continuous_subtype_val.comp continuous_id).subtype_mk _
        · exact continuous_const
      continuous_invFun := by
        exact (continuous_subtype_val.comp continuous_fst).subtype_mk _
    }
    exact H
  · intro u; rfl



/-- Real-to-complex coordinate-wise embedding `ℝⁿ ↪ ℂⁿ`. -/
def realToComplexEmbed {n : ℕ} (v : Fin n → ℝ) : Fin n → ℂ :=
  fun i => (v i : ℂ)

/-- A real function `f : (Fin n → ℝ) → ℝ` is *extended by* a
`MultivaluedAnalytic n` complex function `F` iff:
- the real point `(v : Fin n → ℝ)` embeds via `realToComplexEmbed` into `F.domain`,
- there exists a sheet `p : F.cover` projecting to that embedded point,
- and `F.value p` is the real complex value `(f v : ℂ)`.

This captures the "single-valued real branch" condition. -/
def IsRealExtension {n : ℕ} (F : MultivaluedAnalytic n)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ v : Fin n → ℝ, ∀ h_dom : realToComplexEmbed v ∈ F.domain,
    ∃ p : F.cover, (F.proj p : Fin n → ℂ) = realToComplexEmbed v ∧
                   F.value p = (f v : ℂ)

/-- A real function `f : (Fin n → ℝ) → ℝ` has **solvable monodromy** iff it
admits a `MultivaluedAnalytic` extension with solvable monodromy at every
basepoint. -/
def hasSolvableMonodromy {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ F : MultivaluedAnalytic.{0} n,
    IsRealExtension F f ∧ F.hasSolvableMonodromy

/-! ## Discharge targets (A.1 / A.2 / A.3)

These are the *theorem versions* of the four EML Path-B axioms. Each is
sorry'd here; the actual discharges come in dedicated A.1 / A.2 / A.3 files
(once `expAsMultivalued`, `logAsMultivalued`, `emlAsMultivalued`, and the
Khovanskii structure theorem are in place).

These can be moved to the EML namespace to fully replace the axioms in
`Sheffer/Examples/Eml.lean`. -/

/-- The `constAsMultivalued` extension of a real constant: single-sheet
covering (identity on the base), value identically `(c : ℂ)`. -/
noncomputable def constAsMultivalued (n : ℕ) (c : ℂ) :
    MultivaluedAnalytic.{0} n where
  domain := Set.univ
  open_domain := isOpen_univ
  cover := ↥(Set.univ : Set (Fin n → ℂ))
  topology_cover := instTopologicalSpaceSubtype
  proj := id
  proj_isCovering := id_isCoveringMap
  value := fun _ => c
  value_continuous := continuous_const
  value_locallyHolo := by
    intro p
    refine ⟨Set.univ, isOpen_univ, trivial, fun _ => c, ?_, fun _ _ => rfl⟩
    exact analyticOn_const

/-- **Discharge target (A.1).** Constants have solvable monodromy. -/
theorem const_solvableMonodromy {n : ℕ} (c : ℝ) :
    hasSolvableMonodromy (n := n) (fun _ => c) := by
  refine ⟨constAsMultivalued n (c : ℂ), ?_, ?_⟩
  · -- IsRealExtension: at each real v, the sheet p = ⟨realToComplexEmbed v, trivial⟩
    --   projects to realToComplexEmbed v, value = c (as complex).
    intro v _
    refine ⟨⟨realToComplexEmbed v, trivial⟩, rfl, rfl⟩
  · -- hasSolvableMonodromy: monodromy group at every basepoint is bot (subsingleton fiber).
    intro x
    apply MultivaluedAnalytic.hasSolvableMonodromyAt_of_bot
    apply MultivaluedAnalytic.monodromyGroup_eq_bot_of_subsingleton_fiber
    -- Fiber over x: {z : cover | proj z = x} = {x} as subtype (proj = id ⟹ subsingleton).
    refine ⟨fun a b => Subtype.ext ?_⟩
    have ha : a.val = x := a.property
    have hb : b.val = x := b.property
    exact ha.trans hb.symm

/-- The `varAsMultivalued` extension of a coordinate projection: single-sheet
covering, value at sheet `z` is the `i`-th component of `z`. -/
noncomputable def varAsMultivalued (n : ℕ) (i : Fin n) :
    MultivaluedAnalytic.{0} n where
  domain := Set.univ
  open_domain := isOpen_univ
  cover := ↥(Set.univ : Set (Fin n → ℂ))
  topology_cover := instTopologicalSpaceSubtype
  proj := id
  proj_isCovering := id_isCoveringMap
  value := fun z => z.val i
  value_continuous := (continuous_apply i).comp continuous_subtype_val
  value_locallyHolo := by
    intro p
    refine ⟨Set.univ, isOpen_univ, trivial, fun env => env i, ?_, fun _ _ => rfl⟩
    -- Coordinate projection is analytic on univ (via ContinuousLinearMap.analyticOn).
    exact (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticOn _

/-- **Discharge target (A.1).** Variable projections have solvable monodromy. -/
theorem var_solvableMonodromy {n : ℕ} (i : Fin n) :
    hasSolvableMonodromy (fun env : Fin n → ℝ => env i) := by
  refine ⟨varAsMultivalued n i, ?_, ?_⟩
  · -- IsRealExtension: at v, sheet p = ⟨realToComplexEmbed v, _⟩; value = v i (complexified).
    intro v _
    refine ⟨⟨realToComplexEmbed v, trivial⟩, rfl, ?_⟩
    -- value at p = (realToComplexEmbed v) i = (v i : ℂ).
    rfl
  · -- Same subsingleton-fiber argument as const case.
    intro x
    apply MultivaluedAnalytic.hasSolvableMonodromyAt_of_bot
    apply MultivaluedAnalytic.monodromyGroup_eq_bot_of_subsingleton_fiber
    refine ⟨fun a b => Subtype.ext ?_⟩
    have ha : a.val = x := a.property
    have hb : b.val = x := b.property
    exact ha.trans hb.symm

/-! ## A.2 stepping-stones — exp closure (easy half of Khovanskii)

The eml-preserves theorem decomposes into:
1. `exp_solvableMonodromy`: exp of solvable-monodromy is solvable-monodromy.
   (Easy: `compExp` doesn't add monodromy.)
2. `log_solvableMonodromy`: log of solvable-monodromy is solvable-monodromy.
   (Hard: log adds ℤ-monodromy; needs universal-cover construction.)
3. `sub_solvableMonodromy`: difference of solvable-monodromy is solvable.
   (Medium: pullback of covers; solvable × solvable in product.)

We discharge (1) here using `MultivaluedAnalytic.compExp`; (2) and (3) remain
deferred to the multi-week A.2 work. -/

/-- **Composition lemma (exp).** If `f` has solvable monodromy, so does
`Real.exp ∘ f`. Uses `MultivaluedAnalytic.compExp` (cover unchanged,
value post-composed with `Complex.exp`). -/
theorem exp_solvableMonodromy {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : hasSolvableMonodromy f) :
    hasSolvableMonodromy (fun env : Fin n → ℝ => Real.exp (f env)) := by
  obtain ⟨F, hext, hsolv⟩ := hf
  refine ⟨F.compExp, ?_, (F.compExp_hasSolvableMonodromy_iff).mpr hsolv⟩
  -- IsRealExtension: at v, sheet p from hext gives F.value p = (f v : ℂ).
  -- F.compExp.value p = Complex.exp (F.value p) = Complex.exp (f v : ℂ)
  --                  = (Real.exp (f v) : ℂ).
  intro v h_dom
  obtain ⟨p, hp_proj, hp_val⟩ := hext v h_dom
  refine ⟨p, hp_proj, ?_⟩
  show Complex.exp (F.value p) = _
  rw [hp_val, ← Complex.ofReal_exp]

/-- **Composition lemma (negation).** If `f` has solvable monodromy, so
does `-f`. Uses `MultivaluedAnalytic.compNeg` (cover unchanged, value
negated). -/
theorem neg_solvableMonodromy {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : hasSolvableMonodromy f) :
    hasSolvableMonodromy (fun env : Fin n → ℝ => -(f env)) := by
  obtain ⟨F, hext, hsolv⟩ := hf
  refine ⟨F.compNeg, ?_, (F.compNeg_hasSolvableMonodromy_iff).mpr hsolv⟩
  intro v h_dom
  obtain ⟨p, hp_proj, hp_val⟩ := hext v h_dom
  refine ⟨p, hp_proj, ?_⟩
  show -F.value p = _
  rw [hp_val, ← Complex.ofReal_neg]

/-- **Composition lemma (subtraction).** If `f` and `g` both have solvable
monodromy, so does `f - g`. Uses `MultivaluedAnalytic.compSub` (fiber product
of covers; sum of negated values).

**Proof obligation:** the IsRealExtension half requires extracting agreeing-
base-point sheets from F (extending f) and G (extending g) at each real input.
Deferred to A.2 grind alongside the underlying `compAdd_hasSolvableMonodromy`. -/
theorem sub_solvableMonodromy {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : hasSolvableMonodromy f) (hg : hasSolvableMonodromy g) :
    hasSolvableMonodromy (fun env : Fin n → ℝ => f env - g env) := by
  obtain ⟨F, hf_ext, hf_solv⟩ := hf
  obtain ⟨G, hg_ext, hg_solv⟩ := hg
  refine ⟨F.compSub G, ?_, F.compSub_hasSolvableMonodromy G hf_solv hg_solv⟩
  -- IsRealExtension: at v, find sheets p in F.cover and q in G.cover both
  -- projecting to realToComplexEmbed v. Then the FibProdCover element
  -- ⟨(p, compNeg(q-sheet)), agreement⟩ projects correctly with value
  -- F.value p + (-G.value q) = (f v - g v : ℂ).
  sorry

/-- **Discharge target (A.2).** `eml(f, g) = exp(f) - log(g)` preserves
solvable monodromy. This is the Khovanskii content. -/
theorem eml_preserves_solvableMonodromy {n : ℕ}
    (f g : (Fin n → ℝ) → ℝ) :
    hasSolvableMonodromy f → hasSolvableMonodromy g →
    hasSolvableMonodromy (fun env : Fin n → ℝ =>
      Real.exp (f env) - Real.log (g env)) := by
  -- exp_solvableMonodromy handles the exp half; the log half + difference
  -- still require log_solvableMonodromy + sub_solvableMonodromy.
  sorry

/-! ## A.3 infrastructure — `S₅` injects into the monodromy group ⟹ non-solvable

The Galois-content side of Path A: if `Equiv.Perm (Fin 5)` injects into a
function's monodromy group at some basepoint, the function does not have
solvable monodromy. This is the lemma that bridges mathlib's
`Equiv.Perm.fin_5_not_solvable` (group-theoretic) to our `hasSolvableMonodromy`
predicate.

Discharging the EML `quinticRoot_not_solvableMonodromy` axiom amounts to
establishing the `S₅`-monodromy structure of the generic quintic root in any
of its `MultivaluedAnalytic` extensions — the analytic content. The
group-theoretic step is what these lemmas provide. -/

/-- **A.3 helper.** If `Equiv.Perm (Fin 5)` injects into a group `G`,
then `G` is not solvable. -/
theorem not_isSolvable_of_S5_injects {G : Type*} [Group G]
    (φ : Equiv.Perm (Fin 5) →* G) (hφ : Function.Injective φ) :
    ¬ IsSolvable G := fun _ =>
  Equiv.Perm.fin_5_not_solvable (solvable_of_solvable_injective hφ)

/-- **A.3 helper.** If a `MultivaluedAnalytic` function has `Equiv.Perm (Fin 5)`
injecting into its monodromy group at some basepoint, the function's monodromy
is not globally solvable. -/
theorem MultivaluedAnalytic.not_hasSolvableMonodromy_of_S5_in_monodromy
    {n : ℕ} (F : MultivaluedAnalytic.{0} n) (x : F.domain)
    (φ : Equiv.Perm (Fin 5) →* F.monodromyGroup x)
    (hφ : Function.Injective φ) :
    ¬ F.hasSolvableMonodromy := fun h =>
  not_isSolvable_of_S5_injects φ hφ (h x)

/-- **A.3 helper.** Real-function version: if every `MultivaluedAnalytic`
real-extension `F` of `f` admits `Equiv.Perm (Fin 5)` injecting into its
monodromy group at some basepoint, then `f` does not have solvable monodromy. -/
theorem not_hasSolvableMonodromy_of_S5_universal
    {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (h : ∀ F : MultivaluedAnalytic.{0} n, IsRealExtension F f →
         ∃ x : F.domain, ∃ φ : Equiv.Perm (Fin 5) →* F.monodromyGroup x,
                          Function.Injective φ) :
    ¬ hasSolvableMonodromy f := by
  rintro ⟨F, hext, hsolv⟩
  obtain ⟨x, φ, hφ⟩ := h F hext
  exact not_isSolvable_of_S5_injects φ hφ (hsolv x)

end Path_A
