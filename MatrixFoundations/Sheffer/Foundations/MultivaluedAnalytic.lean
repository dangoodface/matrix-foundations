/-
# Sheffer.Foundations.MultivaluedAnalytic — Path A.0b: multivalued analytic functions

A `MultivaluedAnalytic n` is a multivalued analytic function on (an open subset
of) `ℂⁿ`, modeled as a covering map over its single-valued domain with a
per-sheet value function.

This is the structural backbone of Path A (axiom-discharge for EML). Concrete
instances — `exp` (trivial), `log` (universal cover via `Complex.exp`), and
`eml(f, g) = exp(f) - log(g)` — are defined separately in A.1 / A.2.

Built on:
- `Mathlib.Topology.Covering.Basic` — `IsCoveringMap` infrastructure.
- `Mathlib.Analysis.Analytic.Basic` — `AnalyticOn`.
- `MatrixFoundations.Sheffer.Foundations.MonodromyGroup` — A.0a, the
  `MonodromyGroup` as a subgroup of `Equiv.Perm (proj ⁻¹' {x})`.
-/

import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Constructions
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import MatrixFoundations.Sheffer.Foundations.MonodromyGroup

namespace Path_A

universe u

/-- A **multivalued analytic function** on (an open subset of) `ℂⁿ`,
modeled as a covering map over a single-valued domain with a per-sheet value.

- `domain` is an open subset of `ℂⁿ` where the function is well-defined
  (excludes branch points where the function "blows up", e.g. `0` for `log`).
- `cover` is the covering space; its connected components index the "sheets"
  of the multivalued function (the distinct branches).
- `proj` is the covering projection from sheets to base points.
- `value` reads off the function value per sheet.
- `value_locallyHolo` enforces per-sheet holomorphicity: each sheet locally
  agrees with a single-valued analytic function on the base.

The monodromy group of the function is the action of `π₁(domain, x)` on the
fiber `proj ⁻¹' {x}`, mediated through `IsCoveringMap.MonodromyGroup` (A.0a). -/
structure MultivaluedAnalytic (n : ℕ) where
  /-- Open subset of `ℂⁿ` where the function is single-valued-defined. -/
  domain : Set (Fin n → ℂ)
  open_domain : IsOpen domain
  /-- Covering space — sheets of the analytic continuation. -/
  cover : Type u
  topology_cover : TopologicalSpace cover
  /-- Covering projection. -/
  proj : cover → (Subtype (· ∈ domain))
  proj_isCovering : @IsCoveringMap cover (Subtype (· ∈ domain)) topology_cover
                      instTopologicalSpaceSubtype proj
  /-- Per-sheet function value. -/
  value : cover → ℂ
  value_continuous : @Continuous cover ℂ topology_cover _ value
  /-- Per-sheet holomorphicity: each sheet locally agrees with a single-valued
  analytic function on the base. -/
  value_locallyHolo :
    ∀ p : cover,
      ∃ U : Set cover,
        @IsOpen cover topology_cover U ∧ p ∈ U ∧
        ∃ f : (Fin n → ℂ) → ℂ,
          AnalyticOn ℂ f ((proj '' U).image (·.val)) ∧
          ∀ q ∈ U, value q = f ((proj q).val)

namespace MultivaluedAnalytic

variable {n : ℕ}

/-- Make the `cover`'s topology accessible. -/
instance (F : MultivaluedAnalytic n) : TopologicalSpace F.cover := F.topology_cover

/-- The monodromy group of the multivalued function at a basepoint, as a
subgroup of permutations of the fiber over that basepoint. Uses A.0a. -/
noncomputable def monodromyGroup (F : MultivaluedAnalytic n) (x : F.domain) :
    Subgroup (Equiv.Perm (F.proj ⁻¹' {x})) :=
  F.proj_isCovering.MonodromyGroup x

/-- The multivalued function has **solvable monodromy at** basepoint `x` iff
its monodromy group there is solvable in the group-theoretic sense. -/
def hasSolvableMonodromyAt (F : MultivaluedAnalytic n) (x : F.domain) : Prop :=
  IsSolvable (F.monodromyGroup x)

/-- The multivalued function has **solvable monodromy** (globally) iff its
monodromy group is solvable at every basepoint in the domain. -/
def hasSolvableMonodromy (F : MultivaluedAnalytic n) : Prop :=
  ∀ x : F.domain, F.hasSolvableMonodromyAt x

/-! ## Trivial cases — single-sheet covers have trivial (hence solvable) monodromy -/

/-- A single-sheet covering map (i.e., a homeomorphism, or any covering with
unique-lift property and connected total space) has trivial monodromy group. -/
theorem monodromyGroup_eq_bot_of_subsingleton_fiber
    (F : MultivaluedAnalytic n) (x : F.domain)
    (h_fiber : Subsingleton (F.proj ⁻¹' {x})) :
    F.monodromyGroup x = ⊥ := by
  -- If the fiber is a subsingleton, Equiv.Perm of the fiber is subsingleton
  -- (any two equivs on a singleton agree), so its only subgroup is ⊥.
  haveI : Subsingleton (Equiv.Perm (F.proj ⁻¹' {x})) :=
    ⟨fun a b => Equiv.ext fun x => Subsingleton.elim _ _⟩
  exact Subgroup.eq_bot_of_subsingleton _

/-- If the monodromy group is `⊥`, it's trivially solvable. -/
theorem hasSolvableMonodromyAt_of_bot
    (F : MultivaluedAnalytic n) (x : F.domain)
    (h : F.monodromyGroup x = ⊥) :
    F.hasSolvableMonodromyAt x := by
  unfold hasSolvableMonodromyAt
  rw [h]
  infer_instance

/-! ## Composition transformations — A.2 building blocks

`compExp` post-composes `Complex.exp` at the value level. The covering space
and projection are unchanged; only the value function shifts. Since
`Complex.exp` is single-valued, no new monodromy is added — `F.compExp`
inherits `F`'s monodromy group at every basepoint, and its solvability
properties follow.

`compLog` (post-compose `Complex.log`) is more subtle — the cover must
absorb the ℤ-monodromy of log around branch points. Deferred to A.2 proper. -/

/-- Post-compose a `MultivaluedAnalytic` with `Complex.exp` at the value
level. Cover, projection, and monodromy are unchanged. -/
noncomputable def compExp (F : MultivaluedAnalytic n) : MultivaluedAnalytic n where
  domain := F.domain
  open_domain := F.open_domain
  cover := F.cover
  topology_cover := F.topology_cover
  proj := F.proj
  proj_isCovering := F.proj_isCovering
  value := fun p => Complex.exp (F.value p)
  value_continuous := Complex.continuous_exp.comp F.value_continuous
  value_locallyHolo := by
    intro p
    obtain ⟨U, hU_open, hp_in_U, f, hf_analytic, hf_eq⟩ := F.value_locallyHolo p
    refine ⟨U, hU_open, hp_in_U, fun env => Complex.exp (f env), ?_, ?_⟩
    · exact hf_analytic.cexp
    · intro q hq
      rw [hf_eq q hq]

/-- `F.compExp` has the same cover, projection, and fiber as `F`, hence the
same monodromy group at every basepoint. -/
@[simp] theorem compExp_monodromyGroup (F : MultivaluedAnalytic n) (x : F.domain) :
    F.compExp.monodromyGroup x = F.monodromyGroup x :=
  rfl

/-- `F.compExp` has solvable monodromy iff `F` does (since they share the
same monodromy group structure). -/
theorem compExp_hasSolvableMonodromy_iff (F : MultivaluedAnalytic n) :
    F.compExp.hasSolvableMonodromy ↔ F.hasSolvableMonodromy := by
  unfold hasSolvableMonodromy hasSolvableMonodromyAt
  simp only [compExp_monodromyGroup]
  rfl

/-- Post-compose a `MultivaluedAnalytic` with negation at the value level.
Cover, projection, and monodromy are unchanged. -/
noncomputable def compNeg (F : MultivaluedAnalytic n) : MultivaluedAnalytic n where
  domain := F.domain
  open_domain := F.open_domain
  cover := F.cover
  topology_cover := F.topology_cover
  proj := F.proj
  proj_isCovering := F.proj_isCovering
  value := fun p => -F.value p
  value_continuous := F.value_continuous.neg
  value_locallyHolo := by
    intro p
    obtain ⟨U, hU_open, hp_in_U, f, hf_analytic, hf_eq⟩ := F.value_locallyHolo p
    refine ⟨U, hU_open, hp_in_U, fun env => -f env, hf_analytic.neg, ?_⟩
    intro q hq
    rw [hf_eq q hq]

@[simp] theorem compNeg_monodromyGroup (F : MultivaluedAnalytic n) (x : F.domain) :
    F.compNeg.monodromyGroup x = F.monodromyGroup x :=
  rfl

theorem compNeg_hasSolvableMonodromy_iff (F : MultivaluedAnalytic n) :
    F.compNeg.hasSolvableMonodromy ↔ F.hasSolvableMonodromy := by
  unfold hasSolvableMonodromy hasSolvableMonodromyAt
  simp only [compNeg_monodromyGroup]
  rfl

/-! ## A.2 step — fiber-product cover for binary operations

`compAdd F G` constructs the multivalued sum `F + G` by:
- Restricting the domain to `F.domain ∩ G.domain`.
- Taking the fiber product cover: pairs `(p, q) : F.cover × G.cover` whose
  projections agree as base points.
- Adding the per-sheet values.

The fiber product of two covering maps over the same base is a covering map
(standard topology result; mathlib doesn't have a direct lemma, but the proof
uses simultaneous trivializations from F's and G's local triviality).

The monodromy group of `compAdd F G` injects into the direct product
`F.monodromyGroup × G.monodromyGroup`: a loop in the intersection of domains
acts independently on the F-sheet and G-sheet components of `(p, q)`.

Solvability of subgroup of `solvable × solvable` follows from mathlib's
`IsSolvable.prod` (and a subgroup of a solvable group is solvable). -/

/-- The fiber product cover type for two `MultivaluedAnalytic n`'s. Elements
are pairs of sheets whose base-point projections agree as elements of `ℂⁿ`. -/
def FibProdCover (F G : MultivaluedAnalytic n) : Type _ :=
  { pq : F.cover × G.cover // (F.proj pq.1).val = (G.proj pq.2).val }

instance (F G : MultivaluedAnalytic n) : TopologicalSpace (FibProdCover F G) :=
  instTopologicalSpaceSubtype

/-- The fiber product projection into the intersection of domains.

For `pq = ⟨(p, q), h_eq⟩` where `h_eq : (F.proj p).val = (G.proj q).val`,
the projection lands at `(F.proj p).val` viewed as an element of
`F.domain ∩ G.domain` (membership in both via the equality). -/
noncomputable def fibProdProj (F G : MultivaluedAnalytic n) :
    FibProdCover F G → ↥(F.domain ∩ G.domain) := fun pq =>
  ⟨(F.proj pq.val.1).val,
   ⟨(F.proj pq.val.1).property,
    pq.property ▸ (G.proj pq.val.2).property⟩⟩

/-- The fiber-product cover is a covering map onto the intersection of domains.

**Proof obligation (Path A.2 multi-week — sorry'd):** local triviality follows
from F's and G's local trivializations restricted to a common neighborhood.
Fiber discreteness follows from discreteness of F's and G's fibers individually.
~150-200 ln when discharged; deferred to A.2 grind. -/
theorem fibProdProj_isCoveringMap (F G : MultivaluedAnalytic n) :
    IsCoveringMap (fibProdProj F G) := by
  sorry

/-- Pointwise addition of two `MultivaluedAnalytic`'s via fiber-product cover.
Cover = pairs of agreeing-base-point sheets; value = sum of per-sheet values. -/
noncomputable def compAdd (F G : MultivaluedAnalytic n) :
    MultivaluedAnalytic n where
  domain := F.domain ∩ G.domain
  open_domain := F.open_domain.inter G.open_domain
  cover := FibProdCover F G
  topology_cover := instTopologicalSpaceSubtype
  proj := fibProdProj F G
  proj_isCovering := fibProdProj_isCoveringMap F G
  value := fun pq => F.value pq.val.1 + G.value pq.val.2
  value_continuous := by
    -- F.value ∘ Prod.fst ∘ Subtype.val + G.value ∘ Prod.snd ∘ Subtype.val
    have h1 : @Continuous (FibProdCover F G) ℂ _ _
        (fun pq => F.value pq.val.1) :=
      F.value_continuous.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : @Continuous (FibProdCover F G) ℂ _ _
        (fun pq => G.value pq.val.2) :=
      G.value_continuous.comp (continuous_snd.comp continuous_subtype_val)
    exact h1.add h2
  value_locallyHolo := by
    -- Local holomorphicity: sum of local-analytic functions is local-analytic.
    -- Deferred to A.2 grind alongside fibProdProj covering proof.
    sorry

/-- Pointwise subtraction `F - G := F + (-G)`. Reuses `compNeg` + `compAdd`. -/
noncomputable def compSub (F G : MultivaluedAnalytic n) : MultivaluedAnalytic n :=
  F.compAdd G.compNeg

/-- Monodromy group of `compAdd F G` injects into the product
`F.monodromyGroup × G.monodromyGroup`. Solvability of the result follows from
solvability of both components.

**Proof obligation (A.2 grind):** the injection follows from the fiber-product
structure of the cover — a loop in the base lifts uniquely on each component.
~50-80 ln when discharged. -/
theorem compAdd_hasSolvableMonodromy
    (F G : MultivaluedAnalytic n)
    (hF : F.hasSolvableMonodromy) (hG : G.hasSolvableMonodromy) :
    (F.compAdd G).hasSolvableMonodromy := by
  sorry

/-- Monodromy of `compSub F G = compAdd F (compNeg G)` is solvable when both
F and G have solvable monodromy. Uses `compNeg_hasSolvableMonodromy_iff` to
chain solvability of G through to compNeg G, then `compAdd_hasSolvableMonodromy`. -/
theorem compSub_hasSolvableMonodromy
    (F G : MultivaluedAnalytic n)
    (hF : F.hasSolvableMonodromy) (hG : G.hasSolvableMonodromy) :
    (F.compSub G).hasSolvableMonodromy := by
  unfold compSub
  exact compAdd_hasSolvableMonodromy F G.compNeg hF
    ((G.compNeg_hasSolvableMonodromy_iff).mpr hG)

end MultivaluedAnalytic

end Path_A
