/-
# Sheffer.Examples.Eml — EML instantiation of the framework

The continuous-math, negative-obstruction example. Single binary operator
`eml(x, y) = exp(x) − log(y)` over ℝ, with `inClass` = "has solvable monodromy."
4 axioms encode the Path-B analytic-continuation gap.

Headline: `no_eml_term_represents_quintic`.

References to the original `Eml.lean` (which contains `EmlTree`-based work and
the T4 Khovanskii placeholder) are intentional — `EML.eml` is defined there. -/

import MatrixFoundations.Sheffer.Core
import MatrixFoundations.Eml
import MatrixFoundations.Sheffer.Foundations.SolvableMonodromy
import Mathlib.Analysis.Complex.ExponentialBounds

namespace MinimalBasis.EML

/-- The EML operator-symbol. One element. -/
inductive EmlOp : Type where
  | eml : EmlOp
  deriving Inhabited, DecidableEq

/-- The EML operator-basis: single 2-ary operator interpreted as `EML.eml`. -/
noncomputable def EmlBasis : MinimalBasis.OperatorBasis ℝ where
  Op := EmlOp
  arity _ := 2
  eval _ args := EML.eml (args 0) (args 1)

/-- Sanity: an `eml(x, 1)` term over `EmlBasis` represents `Real.exp ∘ (·)`. -/
example :
    MinimalBasis.Term.representsGlobally (B := EmlBasis) (n := 1)
      (MinimalBasis.Term.app EmlOp.eml
        (fun i => match i with
          | ⟨0, _⟩ => MinimalBasis.Term.var 0
          | ⟨1, _⟩ => MinimalBasis.Term.const 1))
      (fun env => Real.exp (env 0)) := by
  intro env
  simp [MinimalBasis.Term.eval, EmlBasis, EML.eml, Real.log_one]

/-! ## EML obstruction theory + quintic non-expressibility (Path B, axiomatized)

The EML instantiation of `ObstructionTheory`. The `inClass` predicate is "the
function lifts to a multivalued analytic function with solvable monodromy."
We do NOT formalize this analytic content; it's an opaque predicate plus three
axioms (constants/variables trivially in the class, eml preserves the class).
-/

open MinimalBasis

/-- **Concrete `hasSolvableMonodromy`** (was opaque pre-2026-05-10).

Defined via `Path_A.hasSolvableMonodromy`: a real function has solvable
monodromy iff it admits a `MultivaluedAnalytic` complex extension with
solvable monodromy group at every basepoint. See
`MatrixFoundations.Sheffer.Foundations.SolvableMonodromy`. -/
def hasSolvableMonodromy {n : ℕ} : ((Fin n → ℝ) → ℝ) → Prop :=
  Path_A.hasSolvableMonodromy

/-- **Theorem (Path A.1, was axiom).** Constants have trivial (hence solvable)
monodromy. Discharged via `Path_A.const_solvableMonodromy` and a single-sheet
trivial covering. -/
theorem const_solvableMonodromy {n : ℕ} (c : ℝ) :
    hasSolvableMonodromy (n := n) (fun _ => c) :=
  Path_A.const_solvableMonodromy c

/-- **Theorem (Path A.1, was axiom).** Variable projections have trivial
monodromy. Discharged via `Path_A.var_solvableMonodromy`. -/
theorem var_solvableMonodromy {n : ℕ} (i : Fin n) :
    hasSolvableMonodromy (fun env : Fin n → ℝ => env i) :=
  Path_A.var_solvableMonodromy i

/-- **Axiom (Path B gap, Khovanskii's lemma — pending discharge via A.2).**
The `eml` operator preserves solvable monodromy. This requires Khovanskii's
structure theorem (closure of solvable-monodromy under exp/log composition);
multi-week work in `SolvableMonodromy.lean`'s `eml_preserves_solvableMonodromy`. -/
axiom eml_preserves_solvableMonodromy {n : ℕ} (f g : (Fin n → ℝ) → ℝ) :
    hasSolvableMonodromy f → hasSolvableMonodromy g →
    hasSolvableMonodromy (fun env : Fin n → ℝ => EML.eml (f env) (g env))

/-- The EML obstruction theory. -/
noncomputable def EmlObstruction : ObstructionTheory EmlBasis where
  inClass _ f := hasSolvableMonodromy f
  const_in_class c := const_solvableMonodromy c
  var_in_class i := var_solvableMonodromy i
  app_in_class op subs ih := by
    cases op
    dsimp only [EmlBasis] at subs ih
    change hasSolvableMonodromy (fun env => EML.eml (subs 0 env) (subs 1 env))
    exact eml_preserves_solvableMonodromy _ _ (ih 0) (ih 1)

/-! ### Application — the generic quintic root is not EML-expressible -/

/-- Placeholder for "the generic quintic root function." -/
opaque quinticRoot : (Fin 5 → ℝ) → ℝ

/-- **Axiom (Path A.3 residual, Galois-analytic content).** Every
`MultivaluedAnalytic` real-extension of the generic quintic root has
`Equiv.Perm (Fin 5) = S₅` injecting into its monodromy group at some
basepoint. This is the analytic content connecting the quintic's Galois
group `S₅` to its multivalued-function monodromy.

Discharging this axiom requires (a) a concrete definition of `quinticRoot`
(e.g., as the analytic continuation of `f(z) = root of z⁵ - z₁z⁴ - ... - z₅`
on its discriminant complement) and (b) the Galois-monodromy correspondence
for irreducible polynomials. Both are substantial classical results not yet
in mathlib. -/
axiom quinticRoot_has_S5_monodromy_universal :
    ∀ F : Path_A.MultivaluedAnalytic.{0} 5, Path_A.IsRealExtension F quinticRoot →
      ∃ x : F.domain, ∃ φ : Equiv.Perm (Fin 5) →* (F.monodromyGroup x),
                        Function.Injective φ

/-- **Theorem (Path A.3, was axiom).** The generic quintic root does not
have solvable monodromy. Discharged via the group-theoretic
`not_hasSolvableMonodromy_of_S5_universal` lemma + the
`quinticRoot_has_S5_monodromy_universal` axiom (analytic content). -/
theorem quinticRoot_not_solvableMonodromy : ¬ hasSolvableMonodromy quinticRoot :=
  Path_A.not_hasSolvableMonodromy_of_S5_universal _
    quinticRoot_has_S5_monodromy_universal

/-- **Headline theorem.** No EML-term globally represents the generic
quintic root. -/
theorem no_eml_term_represents_quintic :
    ¬ ∃ T : MinimalBasis.Term EmlBasis 5, T.representsGlobally quinticRoot :=
  Term.no_representation_of_not_in_class EmlObstruction quinticRoot
    quinticRoot_not_solvableMonodromy

/-! ### Bridge to the original `EmlTree` from `MatrixFoundations.Eml`

The original `Eml.lean` defined `EmlTree n` directly without going through
the framework. The embedding below shows that every `EmlTree n` corresponds
to a `Term EmlBasis n` with the same evaluation — i.e., the framework
instantiation faithfully recovers the original syntactic object. This is
paper-coherence material, not load-bearing for the framework's contribution.

Earlier attempts hit `Fin 2` match-elaboration friction; this version uses
`Fin.cases` instead of explicit pattern matching, which unfolds more
cleanly under tactics. -/

/-- Embed an `EmlTree` as a `Term EmlBasis n`. The two `Fin 2`-indexed
children of an `eml` node are assembled with a decidable `if i = 0` rather
than `Fin.cases` — the `if` form reduces by `decide` and avoids the
eliminator-motive inference that trips up tactics like `change` downstream. -/
noncomputable def emlTreeToTerm {n : ℕ} :
    EML.EmlTree n → MinimalBasis.Term EmlBasis n
  | .one     => MinimalBasis.Term.const 1
  | .var i   => MinimalBasis.Term.var i
  | .eml a b =>
    MinimalBasis.Term.app EmlOp.eml
      (fun i : Fin 2 => if i = 0 then emlTreeToTerm a else emlTreeToTerm b)

/-- Evaluation is preserved by the embedding. -/
theorem emlTreeToTerm_eval {n : ℕ} (T : EML.EmlTree n) (env : Fin n → ℝ) :
    (emlTreeToTerm T).eval env = T.eval env := by
  induction T with
  | one =>
      simp [emlTreeToTerm, MinimalBasis.Term.eval, EML.EmlTree.eval]
  | var i =>
      simp [emlTreeToTerm, MinimalBasis.Term.eval, EML.EmlTree.eval]
  | eml a b iha ihb =>
      -- `simp` unfolds `emlTreeToTerm`, `Term.eval`, `EmlBasis.eval`, and
      -- reduces the two `if`s on `Fin 2` literals; the residue is a
      -- `congrArg₂ EML.eml` of the children's IHs.
      simp only [emlTreeToTerm, MinimalBasis.Term.eval, EmlBasis,
                 EML.EmlTree.eval,
                 show ((1 : Fin 2) = 0) = False from by decide,
                 if_true, if_false]
      exact congrArg₂ EML.eml iha ihb

/-- The embedding preserves `representsGlobally`. -/
theorem emlTreeToTerm_representsGlobally {n : ℕ}
    (T : EML.EmlTree n) (f : (Fin n → ℝ) → ℝ) :
    (emlTreeToTerm T).representsGlobally f ↔ T.representsGlobally f := by
  constructor
  · intro h env; rw [← emlTreeToTerm_eval]; exact h env
  · intro h env; rw [emlTreeToTerm_eval]; exact h env

/-! ## H1 — depth lower bound for `x + y` over EML

Math-researcher's 21:00 dispatch. **Novel small concrete result**: no
EML-tree of depth ≤ 2 globally represents the addition function
`(x, y) ↦ x + y`. Proof by case enumeration on the term's shape.

Proof structure (per dispatch):
- Depth 0: leaves are `const c`, `var 0`, `var 1`. None equals `x + y`.
- Depth 1: outer `eml(α, β)` with leaves α, β. Form is `exp α - log β`.
  Never equals `x + y`.
- Depth 2: outer `eml(α, β)` with α, β of depth ≤ 1. Form has nested
  exp/log. Never equals `x + y`.

Each step's "never equals" is verified by exhibiting test points where
the term's eval and `x + y` differ. -/

/-- **Helper for cross-variable hard sub-cases of H1.** When T(env) at three
test points (env₀, env₁, env₋₁) along a single var-axis gives values 0, 1, -1,
the algebra forces `exp(exp 1) + exp(exp(-1)) = 2 * exp 1`, which contradicts
`exp(exp 1) > 2 * exp 1` (provable from `Real.exp_one_gt_two`). -/
private lemma case9_cross_variable_hard (Cf K : ℝ)
    (h00 : Real.exp (1 - Cf) - K = 0)
    (h10 : Real.exp (Real.exp 1 - Cf) - K = 1)
    (h_neg : Real.exp (Real.exp (-1) - Cf) - K = -1) :
    False := by
  -- Step 1: subtract h00 from h10 and h_neg.
  have h1 : Real.exp (Real.exp 1 - Cf) - Real.exp (1 - Cf) = 1 := by linarith
  have h2 : Real.exp (Real.exp (-1) - Cf) - Real.exp (1 - Cf) = -1 := by linarith
  -- Step 2: factor exp(-Cf) using exp_add.
  have hxform : ∀ x : ℝ, Real.exp (x - Cf) = Real.exp x * Real.exp (-Cf) := fun x => by
    rw [show x - Cf = x + (-Cf) from by ring, Real.exp_add]
  rw [hxform, hxform] at h1
  rw [hxform, hxform] at h2
  -- h1: exp(exp 1) * exp(-Cf) - exp 1 * exp(-Cf) = 1
  -- h2: exp(exp(-1)) * exp(-Cf) - exp 1 * exp(-Cf) = -1
  -- Sum (h1 + h2): factor (exp(exp 1) + exp(exp(-1)) - 2 * exp 1) * exp(-Cf) = 0
  have hsum : (Real.exp (Real.exp 1) + Real.exp (Real.exp (-1)) - 2 * Real.exp 1) *
              Real.exp (-Cf) = 0 := by linear_combination h1 + h2
  -- Step 3: cancel exp(-Cf) (positive).
  have h_exp_neg_Cf_pos : (0 : ℝ) < Real.exp (-Cf) := Real.exp_pos _
  have heq : Real.exp (Real.exp 1) + Real.exp (Real.exp (-1)) - 2 * Real.exp 1 = 0 := by
    by_contra h_ne
    exact (mul_ne_zero h_ne h_exp_neg_Cf_pos.ne') hsum
  -- Step 4: derive contradiction. exp(exp 1) > 2 * exp 1; exp(exp(-1)) > 0.
  have h_e_gt_2 : Real.exp 1 > 2 := Real.exp_one_gt_two
  have h_e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have h_e2_gt_2e : Real.exp 2 > 2 * Real.exp 1 := by
    rw [h_e2]; nlinarith [h_e_gt_2]
  have h_ee_gt_e2 : Real.exp (Real.exp 1) > Real.exp 2 := Real.exp_lt_exp.mpr h_e_gt_2
  have h_ee_gt_2e : Real.exp (Real.exp 1) > 2 * Real.exp 1 := lt_trans h_e2_gt_2e h_ee_gt_e2
  have h_e_neg_pos : (0 : ℝ) < Real.exp (Real.exp (-1)) := Real.exp_pos _
  linarith

/-- Headline H1 result: `(x, y) ↦ x + y` requires EML depth ≥ 3. -/
theorem depth_global_xy_ge_three :
    ¬ ∃ (T : MinimalBasis.Term EmlBasis 2), T.depth ≤ 2 ∧
        T.representsGlobally (fun v : Fin 2 → ℝ => v 0 + v 1) := by
  rintro ⟨T, hd, hr⟩
  -- T's eval at (0, 0) must be 0; at (1, 0) must be 1; at (0, 1) must be 1.
  -- Suffices: pick three test points where the eval-equation forces three
  -- numerical equations on T's eval.
  have h00 : T.eval (fun _ : Fin 2 => (0 : ℝ)) = 0 := by
    have h := hr (fun _ : Fin 2 => (0 : ℝ))
    suffices (0 : ℝ) + 0 = 0 by linarith [h]
    norm_num
  have h10 : T.eval (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) = 1 := by
    have h := hr (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
    suffices (1 : ℝ) + 0 = 1 by
      rw [h]
      simp
    norm_num
  have h01 : T.eval (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) = 1 := by
    have h := hr (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1)
    suffices (0 : ℝ) + 1 = 1 by
      rw [h]
      simp
    norm_num
  -- 4th test point at (-1, 0): used by cross-variable hard sub-case in case 9.
  have h_neg10 : T.eval (fun i : Fin 2 => if i = 0 then (-1 : ℝ) else 0) = -1 := by
    have h := hr (fun i : Fin 2 => if i = 0 then (-1 : ℝ) else 0)
    suffices ((-1) : ℝ) + 0 = -1 by
      rw [h]
      simp
    norm_num
  -- 5th test point at (0, -1): symmetric for the other cross-variable pattern.
  have h_neg01 : T.eval (fun i : Fin 2 => if i = 0 then 0 else (-1 : ℝ)) = -1 := by
    have h := hr (fun i : Fin 2 => if i = 0 then 0 else (-1 : ℝ))
    suffices ((0 : ℝ)) + (-1) = -1 by
      rw [h]
      simp
    norm_num
  -- Case-split on T.
  match T, hd, h00, h10, h01, h_neg10, h_neg01 with
  | .const c, _, h00, h10, _, _, _ =>
    -- T.eval _ = c at every env. So c = 0 (from h00) and c = 1 (from h10). Contra.
    simp [MinimalBasis.Term.eval] at h00 h10
    linarith
  | .var ⟨0, _⟩, _, _, _, h01, _, _ =>
    -- T.eval env = env 0; at (0, 1), eval = 0, but RHS = 1
    simp [MinimalBasis.Term.eval] at h01
  | .var ⟨1, _⟩, _, _, h10, _, _, _ =>
    -- T.eval env = env 1; at (1, 0), eval = 0, but RHS = 1
    simp [MinimalBasis.Term.eval] at h10
  | .app .eml kids, hd, h00, h10, h01, h_neg10, h_neg01 =>
    -- T = app .eml kids; kids : Fin (EmlBasis.arity .eml) → Term EmlBasis 2.
    -- Use ⟨_, _⟩ indexing form throughout to avoid OfNat synthesis issues.
    have hk0_lt : (0 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
    have hk1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
    -- Coerce h00, h10, h01 into the explicit kids ⟨_, _⟩ form via `change`
    -- (def-equality: T.eval reduces through EmlBasis.eval to Real.exp - Real.log).
    change Real.exp ((kids ⟨0, hk0_lt⟩).eval (fun _ : Fin 2 => 0)) -
           Real.log ((kids ⟨1, hk1_lt⟩).eval (fun _ : Fin 2 => 0)) = 0 at h00
    change Real.exp ((kids ⟨0, hk0_lt⟩).eval
             (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)) -
           Real.log ((kids ⟨1, hk1_lt⟩).eval
             (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)) = 1 at h10
    change Real.exp ((kids ⟨0, hk0_lt⟩).eval
             (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1)) -
           Real.log ((kids ⟨1, hk1_lt⟩).eval
             (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1)) = 1 at h01
    change Real.exp ((kids ⟨0, hk0_lt⟩).eval
             (fun i : Fin 2 => if i = 0 then (-1 : ℝ) else 0)) -
           Real.log ((kids ⟨1, hk1_lt⟩).eval
             (fun i : Fin 2 => if i = 0 then (-1 : ℝ) else 0)) = -1 at h_neg10
    change Real.exp ((kids ⟨0, hk0_lt⟩).eval
             (fun i : Fin 2 => if i = 0 then 0 else (-1 : ℝ))) -
           Real.log ((kids ⟨1, hk1_lt⟩).eval
             (fun i : Fin 2 => if i = 0 then 0 else (-1 : ℝ))) = -1 at h_neg01
    -- Now case-split with consistent indexing.
    cases h_k0 : (kids ⟨0, hk0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
    | const a =>
      cases h_k1 : (kids ⟨1, hk1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
      | const b =>
        rw [h_k0, h_k1] at h00 h10
        simp only [MinimalBasis.Term.eval] at h00 h10
        linarith
      | var i =>
        rw [h_k0, h_k1] at h00
        simp only [MinimalBasis.Term.eval, Real.log_zero, sub_zero] at h00
        linarith [Real.exp_pos a]
      | app _ kids1' =>
        -- kids 1 = .app .eml kids1'; kids1' has depth ≤ 0 (leaves).
        -- T.eval env = exp(a) - log(exp((kids1' 0).eval env) - log((kids1' 1).eval env)).
        rw [h_k0, h_k1] at h00 h10 h01
        have hk1'0_lt : (0 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
        have hk1'1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
        change Real.exp a -
               Real.log (Real.exp ((kids1' ⟨0, hk1'0_lt⟩).eval (fun _ : Fin 2 => 0)) -
                         Real.log ((kids1' ⟨1, hk1'1_lt⟩).eval (fun _ : Fin 2 => 0))) = 0 at h00
        change Real.exp a -
               Real.log (Real.exp ((kids1' ⟨0, hk1'0_lt⟩).eval
                           (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)) -
                         Real.log ((kids1' ⟨1, hk1'1_lt⟩).eval
                           (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0))) = 1 at h10
        change Real.exp a -
               Real.log (Real.exp ((kids1' ⟨0, hk1'0_lt⟩).eval
                           (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1)) -
                         Real.log ((kids1' ⟨1, hk1'1_lt⟩).eval
                           (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1))) = 1 at h01
        cases h_k1'0 : (kids1' ⟨0, hk1'0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
        | const c0 =>
          cases h_k1'1 : (kids1' ⟨1, hk1'1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
          | const c1 =>
            -- T = exp(a) - log(exp(c0) - log(c1)). Constant. h00 = 0, h10 = 1. Contra.
            rw [h_k1'0, h_k1'1] at h00 h10
            simp only [MinimalBasis.Term.eval] at h00 h10
            linarith
          | var i =>
            -- log of (exp c0 - log (env i)). At env = (0,0): log 0 = 0.
            -- At (1, 0): if i=0, env i=1, log 1=0; if i=1, env i=0, log 0=0.
            -- Either way: T = exp(a) - log(exp c0 - 0) = exp(a) - c0. Constant. Contra.
            rw [h_k1'0, h_k1'1] at h00 h10
            simp only [MinimalBasis.Term.eval, Real.log_zero, sub_zero,
                       Real.log_exp] at h00 h10
            rcases i with ⟨_ | _ | _, hi⟩
            · simp at h10; linarith
            · simp at h10; linarith
            · exact absurd hi (by omega)
          | app op'' kids1'' =>
            -- Impossible: 3-level depth chain ≥ 3 contradicts hd ≤ 2.
            -- Use `change` (def-equal expansion) to expose `Term.depth` structure.
            -- Then beta-reduce `Finset.le_sup` redexes manually so omega sees them
            -- as the same term as the goal.
            exfalso
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids i).depth) ≤ 2 at hd
            have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 1 := by
              have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids i).depth) :=
                Finset.le_sup (f := fun i => (kids i).depth)
                  (Finset.mem_univ (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1] at h1
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids1' i).depth) ≤ 1 at h1
            have h2 : (kids1' ⟨1, hk1'1_lt⟩).depth ≤ 0 := by
              have hle : (kids1' ⟨1, hk1'1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids1' i).depth) :=
                Finset.le_sup (f := fun i => (kids1' i).depth)
                  (Finset.mem_univ (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1'1] at h2
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity op''))).sup
                       (fun i => (kids1'' i).depth) ≤ 0 at h2
            omega
        | var i =>
          cases h_k1'1 : (kids1' ⟨1, hk1'1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
          | const c1 =>
            -- (kids1' 0, kids1' 1) = (var i, const c1).
            -- (kids 1).eval env = exp(env i) - log c1.
            -- T.eval env = exp(a) - log(exp(env i) - log c1). Function of env i only.
            -- For i = 0: T(0, 0) = T(0, 1) but RHS 0 ≠ 1.
            -- For i = 1: T(0, 0) = T(1, 0) but RHS 0 ≠ 1.
            rw [h_k1'0, h_k1'1] at h00 h10 h01
            simp only [MinimalBasis.Term.eval] at h00 h10 h01
            rcases i with ⟨_ | _ | _, hi⟩
            · -- i = 0: env i at h00 = 0, at h10 = 1. T depends on env 0; h00 vs h01 give same since env 0 same.
              simp at h00 h01
              linarith
            · -- i = 1: env i at h00 = 0, at h01 = 1. T depends on env 1; h00 vs h10 give same.
              simp at h00 h10
              linarith
            · exact absurd hi (by omega)
          | var j =>
            -- (var i, var j). (kids 1).eval (0, 0) = exp(0) - log(0) = 1 - 0 = 1.
            -- T(0, 0) = exp(a) - log 1 = exp(a). RHS = 0. exp_pos contra.
            rw [h_k1'0, h_k1'1] at h00
            simp only [MinimalBasis.Term.eval, Real.exp_zero, Real.log_zero,
                       sub_zero, Real.log_one] at h00
            linarith [Real.exp_pos a]
          | app op'' kids1'' =>
            -- 3-level depth chain: T → kids 1 → kids1' 1.
            exfalso
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids i).depth) ≤ 2 at hd
            have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 1 := by
              have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids i).depth) :=
                Finset.le_sup (f := fun i => (kids i).depth)
                  (Finset.mem_univ (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1] at h1
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids1' i).depth) ≤ 1 at h1
            have h2 : (kids1' ⟨1, hk1'1_lt⟩).depth ≤ 0 := by
              have hle : (kids1' ⟨1, hk1'1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids1' i).depth) :=
                Finset.le_sup (f := fun i => (kids1' i).depth)
                  (Finset.mem_univ (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1'1] at h2
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity op''))).sup
                       (fun i => (kids1'' i).depth) ≤ 0 at h2
            omega
        | app op'' kids1'' =>
          -- 3-level depth chain: T → kids 1 → kids1' 0.
          exfalso
          change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                     (fun i => (kids i).depth) ≤ 2 at hd
          have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 1 := by
            have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                  (fun i => (kids i).depth) :=
              Finset.le_sup (f := fun i => (kids i).depth)
                (Finset.mem_univ (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
            omega
          rw [h_k1] at h1
          change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                     (fun i => (kids1' i).depth) ≤ 1 at h1
          have h2 : (kids1' ⟨0, hk1'0_lt⟩).depth ≤ 0 := by
            have hle : (kids1' ⟨0, hk1'0_lt⟩).depth ≤
                (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                  (fun i => (kids1' i).depth) :=
              Finset.le_sup (f := fun i => (kids1' i).depth)
                (Finset.mem_univ (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
            omega
          rw [h_k1'0] at h2
          change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity op''))).sup
                     (fun i => (kids1'' i).depth) ≤ 0 at h2
          omega
    | var i =>
      cases h_k1 : (kids ⟨1, hk1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
      | const b =>
        rw [h_k0, h_k1] at h00 h10 h01
        simp only [MinimalBasis.Term.eval] at h00 h10 h01
        rcases i with ⟨_ | _ | _, hi⟩
        · simp at h00 h10
          have h_log_b : Real.log b = 1 := by linarith
          rw [h_log_b] at h10
          linarith [Real.exp_one_gt_two]
        · simp at h00 h01
          have h_log_b : Real.log b = 1 := by linarith
          rw [h_log_b] at h01
          linarith [Real.exp_one_gt_two]
        · exact absurd hi (by omega)
      | var j =>
        rw [h_k0, h_k1] at h00
        simp only [MinimalBasis.Term.eval, Real.exp_zero, Real.log_zero,
                   sub_zero] at h00
        linarith
      | app _ kids1' =>
        -- (var i, app .eml kids1'): kids1' children must be leaves (depth bound).
        have hk1'0_lt : (0 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
        have hk1'1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
        rw [h_k0, h_k1] at h00 h10 h01
        change Real.exp ((fun _ : Fin 2 => (0 : ℝ)) i) -
               Real.log (Real.exp ((kids1' ⟨0, hk1'0_lt⟩).eval
                           (fun _ : Fin 2 => 0)) -
                         Real.log ((kids1' ⟨1, hk1'1_lt⟩).eval
                           (fun _ : Fin 2 => 0))) = 0 at h00
        change Real.exp ((fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0) i) -
               Real.log (Real.exp ((kids1' ⟨0, hk1'0_lt⟩).eval
                           (fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0)) -
                         Real.log ((kids1' ⟨1, hk1'1_lt⟩).eval
                           (fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0))) = 1
                 at h10
        change Real.exp ((fun a : Fin 2 => if a = 0 then (0 : ℝ) else 1) i) -
               Real.log (Real.exp ((kids1' ⟨0, hk1'0_lt⟩).eval
                           (fun a : Fin 2 => if a = 0 then (0 : ℝ) else 1)) -
                         Real.log ((kids1' ⟨1, hk1'1_lt⟩).eval
                           (fun a : Fin 2 => if a = 0 then (0 : ℝ) else 1))) = 1
                 at h01
        cases h_k1'0 : (kids1' ⟨0, hk1'0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
        | const c0 =>
          cases h_k1'1 : (kids1' ⟨1, hk1'1_lt⟩ : MinimalBasis.Term EmlBasis 2)
              with
          | const c1 =>
            -- T = exp(env i) - log(exp c0 - log c1). Let K = log(exp c0 - log c1).
            rw [h_k1'0, h_k1'1] at h00 h10 h01
            simp only [MinimalBasis.Term.eval] at h00 h10 h01
            rcases i with ⟨_ | _ | _, hi⟩
            · simp at h00 h10
              have h_log : Real.log (Real.exp c0 - Real.log c1) = 1 := by
                linarith
              rw [h_log] at h10
              linarith [Real.exp_one_gt_two]
            · simp at h00 h01
              have h_log : Real.log (Real.exp c0 - Real.log c1) = 1 := by
                linarith
              rw [h_log] at h01
              linarith [Real.exp_one_gt_two]
            · exact absurd hi (by omega)
          | var k =>
            -- (kids 1).eval env = exp c0 - log(env k). env k ∈ {0,1}, log = 0.
            -- Inner reduces to exp c0 always. Outer log = c0.
            rw [h_k1'0, h_k1'1] at h00 h10 h01
            simp only [MinimalBasis.Term.eval] at h00 h10 h01
            rcases i with ⟨_ | _ | _, hi⟩
            · rcases k with ⟨_ | _ | _, hk⟩
              · simp at h00 h01; linarith
              · simp at h00 h10
                have h_c0 : c0 = 1 := by
                  have hle := Real.log_exp c0
                  linarith
                rw [h_c0] at h10
                linarith [Real.exp_one_gt_two]
              · exact absurd hk (by omega)
            · rcases k with ⟨_ | _ | _, hk⟩
              · simp at h00 h01
                have h_c0 : c0 = 1 := by
                  have hle := Real.log_exp c0
                  linarith
                rw [h_c0] at h01
                linarith [Real.exp_one_gt_two]
              · simp at h00 h10; linarith
              · exact absurd hk (by omega)
            · exact absurd hi (by omega)
          | app op'' kids1'' =>
            -- 3-level depth contradiction.
            exfalso
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids i).depth) ≤ 2 at hd
            have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 1 := by
              have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids i).depth) :=
                Finset.le_sup (f := fun i => (kids i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1] at h1
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids1' i).depth) ≤ 1 at h1
            have h2 : (kids1' ⟨1, hk1'1_lt⟩).depth ≤ 0 := by
              have hle : (kids1' ⟨1, hk1'1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids1' i).depth) :=
                Finset.le_sup (f := fun i => (kids1' i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1'1] at h2
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity op''))).sup
                       (fun i => (kids1'' i).depth) ≤ 0 at h2
            omega
        | var j =>
          cases h_k1'1 : (kids1' ⟨1, hk1'1_lt⟩ : MinimalBasis.Term EmlBasis 2)
              with
          | const c1 =>
            -- (kids 1).eval env = exp(env j) - log c1.
            rw [h_k1'0, h_k1'1] at h00 h10 h01
            simp only [MinimalBasis.Term.eval] at h00 h10 h01
            rcases i with ⟨_ | _ | _, hi⟩
            · rcases j with ⟨_ | _ | _, hj⟩
              · -- i=0, j=0: env i = env j = 0 in env₀ and env₀₁. Same LHS.
                rw [show (if (⟨0, hi⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 0
                      from if_pos rfl] at h01
                linarith
              · -- i=0, j=1
                simp at h00 h10
                have h_log : Real.log (1 - Real.log c1) = 1 := by linarith
                rw [h_log] at h10
                linarith [Real.exp_one_gt_two]
              · exact absurd hj (by omega)
            · rcases j with ⟨_ | _ | _, hj⟩
              · -- i=1, j=0
                simp at h00 h01
                have h_log : Real.log (1 - Real.log c1) = 1 := by linarith
                rw [h_log] at h01
                linarith [Real.exp_one_gt_two]
              · -- i=1, j=1: env₁₀ at index 1 = 0; same LHS as h00.
                have h_one_ne_zero : (⟨0 + 1, hi⟩ : Fin 2) ≠ 0 := by
                  intro h; exact Nat.succ_ne_zero 0 (congrArg Fin.val h)
                rw [show (if (⟨0 + 1, hi⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 0
                      from if_neg h_one_ne_zero] at h10
                linarith
              · exact absurd hj (by omega)
            · exact absurd hi (by omega)
          | var k =>
            -- (kids 1).eval (0,0) = exp 0 - log 0 = 1 - 0 = 1. log 1 = 0.
            -- T(0,0) = exp 0 - 0 = 1 ≠ 0.
            rw [h_k1'0, h_k1'1] at h00
            simp only [MinimalBasis.Term.eval, Real.exp_zero, Real.log_zero,
                       sub_zero, Real.log_one] at h00
            linarith
          | app op'' kids1'' =>
            -- 3-level depth contradiction.
            exfalso
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids i).depth) ≤ 2 at hd
            have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 1 := by
              have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids i).depth) :=
                Finset.le_sup (f := fun i => (kids i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1] at h1
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids1' i).depth) ≤ 1 at h1
            have h2 : (kids1' ⟨1, hk1'1_lt⟩).depth ≤ 0 := by
              have hle : (kids1' ⟨1, hk1'1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids1' i).depth) :=
                Finset.le_sup (f := fun i => (kids1' i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1'1] at h2
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity op''))).sup
                       (fun i => (kids1'' i).depth) ≤ 0 at h2
            omega
        | app op'' kids1'' =>
          -- 3-level depth contradiction (kids1' 0 = .app).
          exfalso
          change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                     (fun i => (kids i).depth) ≤ 2 at hd
          have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 1 := by
            have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                  (fun i => (kids i).depth) :=
              Finset.le_sup (f := fun i => (kids i).depth)
                (Finset.mem_univ (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
            omega
          rw [h_k1] at h1
          change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                     (fun i => (kids1' i).depth) ≤ 1 at h1
          have h2 : (kids1' ⟨0, hk1'0_lt⟩).depth ≤ 0 := by
            have hle : (kids1' ⟨0, hk1'0_lt⟩).depth ≤
                (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                  (fun i => (kids1' i).depth) :=
              Finset.le_sup (f := fun i => (kids1' i).depth)
                (Finset.mem_univ
                  (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
            omega
          rw [h_k1'0] at h2
          change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity op''))).sup
                     (fun i => (kids1'' i).depth) ≤ 0 at h2
          omega
    | app _ kids0' =>
      -- kids 0 = .app .eml kids0'. By depth bound, kids0' children are leaves.
      have hk0'0_lt : (0 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
      have hk0'1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
      rw [h_k0] at h00 h10 h01 h_neg10 h_neg01
      change Real.exp (Real.exp ((kids0' ⟨0, hk0'0_lt⟩).eval
                           (fun _ : Fin 2 => 0)) -
                       Real.log ((kids0' ⟨1, hk0'1_lt⟩).eval
                           (fun _ : Fin 2 => 0))) -
             Real.log ((kids ⟨1, hk1_lt⟩).eval (fun _ : Fin 2 => 0)) = 0 at h00
      change Real.exp (Real.exp ((kids0' ⟨0, hk0'0_lt⟩).eval
                           (fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0)) -
                       Real.log ((kids0' ⟨1, hk0'1_lt⟩).eval
                           (fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0))) -
             Real.log ((kids ⟨1, hk1_lt⟩).eval
                 (fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0)) = 1 at h10
      change Real.exp (Real.exp ((kids0' ⟨0, hk0'0_lt⟩).eval
                           (fun a : Fin 2 => if a = 0 then (0 : ℝ) else 1)) -
                       Real.log ((kids0' ⟨1, hk0'1_lt⟩).eval
                           (fun a : Fin 2 => if a = 0 then (0 : ℝ) else 1))) -
             Real.log ((kids ⟨1, hk1_lt⟩).eval
                 (fun a : Fin 2 => if a = 0 then (0 : ℝ) else 1)) = 1 at h01
      change Real.exp (Real.exp ((kids0' ⟨0, hk0'0_lt⟩).eval
                           (fun a : Fin 2 => if a = 0 then (-1 : ℝ) else 0)) -
                       Real.log ((kids0' ⟨1, hk0'1_lt⟩).eval
                           (fun a : Fin 2 => if a = 0 then (-1 : ℝ) else 0))) -
             Real.log ((kids ⟨1, hk1_lt⟩).eval
                 (fun a : Fin 2 => if a = 0 then (-1 : ℝ) else 0)) = -1 at h_neg10
      change Real.exp (Real.exp ((kids0' ⟨0, hk0'0_lt⟩).eval
                           (fun a : Fin 2 => if a = 0 then 0 else (-1 : ℝ))) -
                       Real.log ((kids0' ⟨1, hk0'1_lt⟩).eval
                           (fun a : Fin 2 => if a = 0 then 0 else (-1 : ℝ)))) -
             Real.log ((kids ⟨1, hk1_lt⟩).eval
                 (fun a : Fin 2 => if a = 0 then 0 else (-1 : ℝ))) = -1 at h_neg01
      cases h_k1 : (kids ⟨1, hk1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
      | const b =>
        -- T(env) = exp(F(env)) - log b. Same kids0'-form gives same F.
        rw [h_k1] at h00 h10 h01
        simp only [MinimalBasis.Term.eval] at h00 h10 h01
        cases h_k0'0 : (kids0' ⟨0, hk0'0_lt⟩ :
            MinimalBasis.Term EmlBasis 2) with
        | const a =>
          cases h_k0'1 : (kids0' ⟨1, hk0'1_lt⟩ :
              MinimalBasis.Term EmlBasis 2) with
          | const b' =>
            -- F = exp a - log b'. Constant. h00 LHS = h10 LHS, RHS differ.
            rw [h_k0'0, h_k0'1] at h00 h10
            simp only [MinimalBasis.Term.eval] at h00 h10
            linarith
          | var k =>
            -- F = exp a - log(env k). env k ∈ {0,1} → log = 0. F = exp a const.
            rw [h_k0'0, h_k0'1] at h00 h10 h01
            simp only [MinimalBasis.Term.eval] at h00 h10 h01
            rcases k with ⟨_ | _ | _, hk⟩
            · simp at h00 h10; linarith
            · simp at h00 h10; linarith
            · exact absurd hk (by omega)
          | app op'' kids0'' =>
            -- 3-level depth contradiction (T → kids 0 → kids0' 1).
            exfalso
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids i).depth) ≤ 2 at hd
            have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
              have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids i).depth) :=
                Finset.le_sup (f := fun i => (kids i).depth)
                  (Finset.mem_univ
                    (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k0] at h1
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids0' i).depth) ≤ 1 at h1
            have h2 : (kids0' ⟨1, hk0'1_lt⟩).depth ≤ 0 := by
              have hle : (kids0' ⟨1, hk0'1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids0' i).depth) :=
                Finset.le_sup (f := fun i => (kids0' i).depth)
                  (Finset.mem_univ
                    (⟨1, hk0'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k0'1] at h2
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity op''))).sup
                       (fun i => (kids0'' i).depth) ≤ 0 at h2
            omega
        | var i =>
          cases h_k0'1 : (kids0' ⟨1, hk0'1_lt⟩ :
              MinimalBasis.Term EmlBasis 2) with
          | const b' =>
            -- F = exp(env i) - log b'.
            rw [h_k0'0, h_k0'1] at h00 h10 h01
            simp only [MinimalBasis.Term.eval] at h00 h10 h01
            rcases i with ⟨_ | _ | _, hi⟩
            · -- i=0: F(env₀) = F(env₀₁) (both have env i = 0).
              rw [show (if (⟨0, hi⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 0
                    from if_pos rfl] at h01
              linarith
            · -- i=1: F(env₀) = F(env₁₀) (both have env i = 0).
              have h_one_ne_zero : (⟨0 + 1, hi⟩ : Fin 2) ≠ 0 := by
                intro h; exact Nat.succ_ne_zero 0 (congrArg Fin.val h)
              rw [show (if (⟨0 + 1, hi⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 0
                    from if_neg h_one_ne_zero] at h10
              linarith
            · exact absurd hi (by omega)
          | var k =>
            -- F = exp(env i) - log(env k). log(env k) = 0 always.
            rw [h_k0'0, h_k0'1] at h00 h10 h01
            simp only [MinimalBasis.Term.eval] at h00 h10 h01
            rcases i with ⟨_ | _ | _, hi⟩
            · -- i=0: F(env₀) = exp 0 = 1 = F(env₀₁).
              rcases k with ⟨_ | _ | _, hk⟩
              · simp at h00 h01; linarith
              · simp at h00 h01; linarith
              · exact absurd hk (by omega)
            · -- i=1: F(env₀) = 1 = F(env₁₀).
              rcases k with ⟨_ | _ | _, hk⟩
              · simp at h00 h10; linarith
              · simp at h00 h10; linarith
              · exact absurd hk (by omega)
            · exact absurd hi (by omega)
          | app op'' kids0'' =>
            -- 3-level depth contradiction.
            exfalso
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids i).depth) ≤ 2 at hd
            have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
              have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids i).depth) :=
                Finset.le_sup (f := fun i => (kids i).depth)
                  (Finset.mem_univ
                    (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k0] at h1
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids0' i).depth) ≤ 1 at h1
            have h2 : (kids0' ⟨1, hk0'1_lt⟩).depth ≤ 0 := by
              have hle : (kids0' ⟨1, hk0'1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids0' i).depth) :=
                Finset.le_sup (f := fun i => (kids0' i).depth)
                  (Finset.mem_univ
                    (⟨1, hk0'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k0'1] at h2
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity op''))).sup
                       (fun i => (kids0'' i).depth) ≤ 0 at h2
            omega
        | app op'' kids0'' =>
          -- 3-level depth contradiction (kids0' 0 = .app).
          exfalso
          change 1 + (Finset.univ :
              Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                     (fun i => (kids i).depth) ≤ 2 at hd
          have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
            have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                  (fun i => (kids i).depth) :=
              Finset.le_sup (f := fun i => (kids i).depth)
                (Finset.mem_univ
                  (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
            omega
          rw [h_k0] at h1
          change 1 + (Finset.univ :
              Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                     (fun i => (kids0' i).depth) ≤ 1 at h1
          have h2 : (kids0' ⟨0, hk0'0_lt⟩).depth ≤ 0 := by
            have hle : (kids0' ⟨0, hk0'0_lt⟩).depth ≤
                (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                  (fun i => (kids0' i).depth) :=
              Finset.le_sup (f := fun i => (kids0' i).depth)
                (Finset.mem_univ
                  (⟨0, hk0'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
            omega
          rw [h_k0'0] at h2
          change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity op''))).sup
                     (fun i => (kids0'' i).depth) ≤ 0 at h2
          omega
      | var j =>
        -- T(env₀) = exp(F(env₀)) - log 0 = exp(F(env₀)) > 0. h00 = 0 → contra.
        rw [h_k1] at h00
        simp only [MinimalBasis.Term.eval, Real.log_zero, sub_zero] at h00
        linarith [Real.exp_pos
            (Real.exp ((kids0' ⟨0, hk0'0_lt⟩).eval (fun _ : Fin 2 => 0)) -
             Real.log ((kids0' ⟨1, hk0'1_lt⟩).eval (fun _ : Fin 2 => 0)))]
      | app _ kids1' =>
        -- 4-level: T = exp(F) - log(G). F, G each depth-1 over leaves.
        have hk1'0_lt : (0 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
        have hk1'1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
        rw [h_k1] at h00 h10 h01 h_neg10 h_neg01
        change Real.exp (Real.exp ((kids0' ⟨0, hk0'0_lt⟩).eval
                             (fun _ : Fin 2 => 0)) -
                         Real.log ((kids0' ⟨1, hk0'1_lt⟩).eval
                             (fun _ : Fin 2 => 0))) -
               Real.log (Real.exp ((kids1' ⟨0, hk1'0_lt⟩).eval
                             (fun _ : Fin 2 => 0)) -
                         Real.log ((kids1' ⟨1, hk1'1_lt⟩).eval
                             (fun _ : Fin 2 => 0))) = 0 at h00
        change Real.exp (Real.exp ((kids0' ⟨0, hk0'0_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0)) -
                         Real.log ((kids0' ⟨1, hk0'1_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0))) -
               Real.log (Real.exp ((kids1' ⟨0, hk1'0_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0)) -
                         Real.log ((kids1' ⟨1, hk1'1_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0))) =
                 1 at h10
        change Real.exp (Real.exp ((kids0' ⟨0, hk0'0_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then (0 : ℝ) else 1)) -
                         Real.log ((kids0' ⟨1, hk0'1_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then (0 : ℝ) else 1))) -
               Real.log (Real.exp ((kids1' ⟨0, hk1'0_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then (0 : ℝ) else 1)) -
                         Real.log ((kids1' ⟨1, hk1'1_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then (0 : ℝ) else 1))) =
                 1 at h01
        change Real.exp (Real.exp ((kids0' ⟨0, hk0'0_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then (-1 : ℝ) else 0)) -
                         Real.log ((kids0' ⟨1, hk0'1_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then (-1 : ℝ) else 0))) -
               Real.log (Real.exp ((kids1' ⟨0, hk1'0_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then (-1 : ℝ) else 0)) -
                         Real.log ((kids1' ⟨1, hk1'1_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then (-1 : ℝ) else 0))) =
                 -1 at h_neg10
        change Real.exp (Real.exp ((kids0' ⟨0, hk0'0_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then 0 else (-1 : ℝ))) -
                         Real.log ((kids0' ⟨1, hk0'1_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then 0 else (-1 : ℝ)))) -
               Real.log (Real.exp ((kids1' ⟨0, hk1'0_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then 0 else (-1 : ℝ))) -
                         Real.log ((kids1' ⟨1, hk1'1_lt⟩).eval
                             (fun a : Fin 2 => if a = 0 then 0 else (-1 : ℝ)))) =
                 -1 at h_neg01
        cases h_k1'0 : (kids1' ⟨0, hk1'0_lt⟩ :
            MinimalBasis.Term EmlBasis 2) with
        | const c =>
          cases h_k1'1 : (kids1' ⟨1, hk1'1_lt⟩ :
              MinimalBasis.Term EmlBasis 2) with
          | const b'' =>
            -- G(env) = exp c - log b''. CONSTANT (both kids1' children constants).
            -- T = exp(F) - log(exp c - log b''). Same as case 7 with K = log(exp c - log b'').
            -- F's variability gives contradiction.
            rw [h_k1'0, h_k1'1] at h00 h10 h01
            simp only [MinimalBasis.Term.eval] at h00 h10 h01
            cases h_k0'0 : (kids0' ⟨0, hk0'0_lt⟩ :
                MinimalBasis.Term EmlBasis 2) with
            | const a =>
              cases h_k0'1 : (kids0' ⟨1, hk0'1_lt⟩ :
                  MinimalBasis.Term EmlBasis 2) with
              | const b' =>
                rw [h_k0'0, h_k0'1] at h00 h10
                simp only [MinimalBasis.Term.eval] at h00 h10
                linarith
              | var k =>
                rw [h_k0'0, h_k0'1] at h00 h10 h01
                simp only [MinimalBasis.Term.eval] at h00 h10 h01
                rcases k with ⟨_ | _ | _, hk⟩
                · simp at h00 h10; linarith
                · simp at h00 h10; linarith
                · exact absurd hk (by omega)
              | app op'' kids0'' =>
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 2 at hd
                have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
                  have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k0] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids0' i).depth) ≤ 1 at h1
                have h2 : (kids0' ⟨1, hk0'1_lt⟩).depth ≤ 0 := by
                  have hle : (kids0' ⟨1, hk0'1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids0' i).depth) :=
                    Finset.le_sup (f := fun i => (kids0' i).depth)
                      (Finset.mem_univ
                        (⟨1, hk0'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k0'1] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op''))).sup
                           (fun i => (kids0'' i).depth) ≤ 0 at h2
                omega
            | var i =>
              cases h_k0'1 : (kids0' ⟨1, hk0'1_lt⟩ :
                  MinimalBasis.Term EmlBasis 2) with
              | const b' =>
                rw [h_k0'0, h_k0'1] at h00 h10 h01
                simp only [MinimalBasis.Term.eval] at h00 h10 h01
                rcases i with ⟨_ | _ | _, hi⟩
                · rw [show (if (⟨0, hi⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 0
                        from if_pos rfl] at h01
                  linarith
                · have hne : (⟨0 + 1, hi⟩ : Fin 2) ≠ 0 := fun h =>
                    Nat.succ_ne_zero 0 (congrArg Fin.val h)
                  rw [show (if (⟨0 + 1, hi⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 0
                        from if_neg hne] at h10
                  linarith
                · exact absurd hi (by omega)
              | var k =>
                rw [h_k0'0, h_k0'1] at h00 h10 h01
                simp only [MinimalBasis.Term.eval] at h00 h10 h01
                rcases i with ⟨_ | _ | _, hi⟩
                · rcases k with ⟨_ | _ | _, hk⟩
                  · simp at h00 h01; linarith
                  · simp at h00 h01; linarith
                  · exact absurd hk (by omega)
                · rcases k with ⟨_ | _ | _, hk⟩
                  · simp at h00 h10; linarith
                  · simp at h00 h10; linarith
                  · exact absurd hk (by omega)
                · exact absurd hi (by omega)
              | app op'' kids0'' =>
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 2 at hd
                have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
                  have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k0] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids0' i).depth) ≤ 1 at h1
                have h2 : (kids0' ⟨1, hk0'1_lt⟩).depth ≤ 0 := by
                  have hle : (kids0' ⟨1, hk0'1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids0' i).depth) :=
                    Finset.le_sup (f := fun i => (kids0' i).depth)
                      (Finset.mem_univ
                        (⟨1, hk0'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k0'1] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op''))).sup
                           (fun i => (kids0'' i).depth) ≤ 0 at h2
                omega
            | app op'' kids0'' =>
              exfalso
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids i).depth) ≤ 2 at hd
              have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
                have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids i).depth) :=
                  Finset.le_sup (f := fun i => (kids i).depth)
                    (Finset.mem_univ
                      (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k0] at h1
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids0' i).depth) ≤ 1 at h1
              have h2 : (kids0' ⟨0, hk0'0_lt⟩).depth ≤ 0 := by
                have hle : (kids0' ⟨0, hk0'0_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids0' i).depth) :=
                  Finset.le_sup (f := fun i => (kids0' i).depth)
                    (Finset.mem_univ
                      (⟨0, hk0'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k0'0] at h2
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity op''))).sup
                         (fun i => (kids0'' i).depth) ≤ 0 at h2
              omega
          | var l =>
            -- T(env) = exp(F(env)) - log(exp c - log(env l)).
            -- env l ∈ {0, 1} → log = 0 always. So T(env) = exp(F(env)) - c.
            rw [h_k1'0, h_k1'1] at h00 h10 h01
            simp only [MinimalBasis.Term.eval] at h00 h10 h01
            rcases l with ⟨_ | _ | _, hl⟩
            -- l = 0: env₀ ⟨0,_⟩ = 0; env₁₀ ⟨0,_⟩ = 1; env₀₁ ⟨0,_⟩ = 0.
            · simp only [Real.exp_zero, Real.log_zero,
                         Real.log_one, sub_zero, Real.log_exp] at h00
              -- h00: Real.exp F(env₀) - c = 0
              rw [show (if (⟨0, hl⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 1
                    from if_pos rfl] at h10
              rw [show (if (⟨0, hl⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 0
                    from if_pos rfl] at h01
              simp only [Real.exp_zero, Real.log_zero,
                         Real.log_one, sub_zero, Real.log_exp] at h10 h01
              -- All three: Real.exp F(env) - c = 0/1/1
              -- F shape determines which env-pair gives same F.
              cases h_k0'0 : (kids0' ⟨0, hk0'0_lt⟩ :
                  MinimalBasis.Term EmlBasis 2) with
              | const a =>
                cases h_k0'1 : (kids0' ⟨1, hk0'1_lt⟩ :
                    MinimalBasis.Term EmlBasis 2) with
                | const b' =>
                  rw [h_k0'0, h_k0'1] at h00 h10
                  simp only [MinimalBasis.Term.eval] at h00 h10
                  linarith
                | var k =>
                  rw [h_k0'0, h_k0'1] at h00 h10 h01
                  simp only [MinimalBasis.Term.eval] at h00 h10 h01
                  rcases k with ⟨_ | _ | _, hk⟩
                  · simp at h00 h10; linarith
                  · simp at h00 h10; linarith
                  · exact absurd hk (by omega)
                | app op'' kids0'' =>
                  -- 4-level depth contradiction
                  exfalso
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids i).depth) ≤ 2 at hd
                  have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
                    have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids i).depth) :=
                      Finset.le_sup (f := fun i => (kids i).depth)
                        (Finset.mem_univ
                          (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k0] at h1
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids0' i).depth) ≤ 1 at h1
                  have h2 : (kids0' ⟨1, hk0'1_lt⟩).depth ≤ 0 := by
                    have hle : (kids0' ⟨1, hk0'1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids0' i).depth) :=
                      Finset.le_sup (f := fun i => (kids0' i).depth)
                        (Finset.mem_univ
                          (⟨1, hk0'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k0'1] at h2
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity op''))).sup
                             (fun i => (kids0'' i).depth) ≤ 0 at h2
                  omega
              | var i =>
                cases h_k0'1 : (kids0' ⟨1, hk0'1_lt⟩ :
                    MinimalBasis.Term EmlBasis 2) with
                | const b' =>
                  rw [h_k0'0, h_k0'1] at h00 h10 h01
                  simp only [MinimalBasis.Term.eval] at h00 h10 h01
                  rcases i with ⟨_ | _ | _, hi⟩
                  · -- i=0: F(env₀) = F(env₀₁) (both env i = 0)
                    rw [show (if (⟨0, hi⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 0
                          from if_pos rfl] at h01
                    linarith
                  · -- i=1: F(env₀) = F(env₁₀)
                    have hne : (⟨0 + 1, hi⟩ : Fin 2) ≠ 0 := fun h =>
                      Nat.succ_ne_zero 0 (congrArg Fin.val h)
                    rw [show (if (⟨0 + 1, hi⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 0
                          from if_neg hne] at h10
                    linarith
                  · exact absurd hi (by omega)
                | var k =>
                  rw [h_k0'0, h_k0'1] at h00 h10 h01
                  simp only [MinimalBasis.Term.eval] at h00 h10 h01
                  rcases i with ⟨_ | _ | _, hi⟩
                  · rcases k with ⟨_ | _ | _, hk⟩
                    · simp at h00 h01; linarith
                    · simp at h00 h01; linarith
                    · exact absurd hk (by omega)
                  · rcases k with ⟨_ | _ | _, hk⟩
                    · simp at h00 h10; linarith
                    · simp at h00 h10; linarith
                    · exact absurd hk (by omega)
                  · exact absurd hi (by omega)
                | app op'' kids0'' =>
                  -- 4-level depth contradiction
                  exfalso
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids i).depth) ≤ 2 at hd
                  have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
                    have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids i).depth) :=
                      Finset.le_sup (f := fun i => (kids i).depth)
                        (Finset.mem_univ
                          (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k0] at h1
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids0' i).depth) ≤ 1 at h1
                  have h2 : (kids0' ⟨1, hk0'1_lt⟩).depth ≤ 0 := by
                    have hle : (kids0' ⟨1, hk0'1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids0' i).depth) :=
                      Finset.le_sup (f := fun i => (kids0' i).depth)
                        (Finset.mem_univ
                          (⟨1, hk0'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k0'1] at h2
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity op''))).sup
                             (fun i => (kids0'' i).depth) ≤ 0 at h2
                  omega
              | app op'' kids0'' =>
                -- 4-level depth contradiction (kids0' 0 = .app)
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 2 at hd
                have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
                  have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k0] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids0' i).depth) ≤ 1 at h1
                have h2 : (kids0' ⟨0, hk0'0_lt⟩).depth ≤ 0 := by
                  have hle : (kids0' ⟨0, hk0'0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids0' i).depth) :=
                    Finset.le_sup (f := fun i => (kids0' i).depth)
                      (Finset.mem_univ
                        (⟨0, hk0'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k0'0] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op''))).sup
                           (fun i => (kids0'' i).depth) ≤ 0 at h2
                omega
            -- l = 1: env₀ ⟨1,_⟩ = 0; env₁₀ ⟨1,_⟩ = 0; env₀₁ ⟨1,_⟩ = 1.
            · simp only [Real.exp_zero, Real.log_zero,
                         Real.log_one, sub_zero, Real.log_exp] at h00
              have hne : (⟨0 + 1, hl⟩ : Fin 2) ≠ 0 := fun h =>
                Nat.succ_ne_zero 0 (congrArg Fin.val h)
              rw [show (if (⟨0 + 1, hl⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 0
                    from if_neg hne] at h10
              rw [show (if (⟨0 + 1, hl⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 1
                    from if_neg hne] at h01
              simp only [Real.exp_zero, Real.log_zero,
                         Real.log_one, sub_zero, Real.log_exp] at h10 h01
              -- Same dispatch as l = 0 branch
              cases h_k0'0 : (kids0' ⟨0, hk0'0_lt⟩ :
                  MinimalBasis.Term EmlBasis 2) with
              | const a =>
                cases h_k0'1 : (kids0' ⟨1, hk0'1_lt⟩ :
                    MinimalBasis.Term EmlBasis 2) with
                | const b' =>
                  rw [h_k0'0, h_k0'1] at h00 h10
                  simp only [MinimalBasis.Term.eval] at h00 h10
                  linarith
                | var k =>
                  rw [h_k0'0, h_k0'1] at h00 h10 h01
                  simp only [MinimalBasis.Term.eval] at h00 h10 h01
                  rcases k with ⟨_ | _ | _, hk⟩
                  · simp at h00 h10; linarith
                  · simp at h00 h10; linarith
                  · exact absurd hk (by omega)
                | app op'' kids0'' =>
                  exfalso
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids i).depth) ≤ 2 at hd
                  have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
                    have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids i).depth) :=
                      Finset.le_sup (f := fun i => (kids i).depth)
                        (Finset.mem_univ
                          (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k0] at h1
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids0' i).depth) ≤ 1 at h1
                  have h2 : (kids0' ⟨1, hk0'1_lt⟩).depth ≤ 0 := by
                    have hle : (kids0' ⟨1, hk0'1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids0' i).depth) :=
                      Finset.le_sup (f := fun i => (kids0' i).depth)
                        (Finset.mem_univ
                          (⟨1, hk0'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k0'1] at h2
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity op''))).sup
                             (fun i => (kids0'' i).depth) ≤ 0 at h2
                  omega
              | var i =>
                cases h_k0'1 : (kids0' ⟨1, hk0'1_lt⟩ :
                    MinimalBasis.Term EmlBasis 2) with
                | const b' =>
                  rw [h_k0'0, h_k0'1] at h00 h10 h01
                  simp only [MinimalBasis.Term.eval] at h00 h10 h01
                  rcases i with ⟨_ | _ | _, hi⟩
                  · rw [show (if (⟨0, hi⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 0
                          from if_pos rfl] at h01
                    linarith
                  · have hne' : (⟨0 + 1, hi⟩ : Fin 2) ≠ 0 := fun h =>
                      Nat.succ_ne_zero 0 (congrArg Fin.val h)
                    rw [show (if (⟨0 + 1, hi⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 0
                          from if_neg hne'] at h10
                    linarith
                  · exact absurd hi (by omega)
                | var k =>
                  rw [h_k0'0, h_k0'1] at h00 h10 h01
                  simp only [MinimalBasis.Term.eval] at h00 h10 h01
                  rcases i with ⟨_ | _ | _, hi⟩
                  · rcases k with ⟨_ | _ | _, hk⟩
                    · simp at h00 h01; linarith
                    · simp at h00 h01; linarith
                    · exact absurd hk (by omega)
                  · rcases k with ⟨_ | _ | _, hk⟩
                    · simp at h00 h10; linarith
                    · simp at h00 h10; linarith
                    · exact absurd hk (by omega)
                  · exact absurd hi (by omega)
                | app op'' kids0'' =>
                  exfalso
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids i).depth) ≤ 2 at hd
                  have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
                    have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids i).depth) :=
                      Finset.le_sup (f := fun i => (kids i).depth)
                        (Finset.mem_univ
                          (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k0] at h1
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids0' i).depth) ≤ 1 at h1
                  have h2 : (kids0' ⟨1, hk0'1_lt⟩).depth ≤ 0 := by
                    have hle : (kids0' ⟨1, hk0'1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids0' i).depth) :=
                      Finset.le_sup (f := fun i => (kids0' i).depth)
                        (Finset.mem_univ
                          (⟨1, hk0'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k0'1] at h2
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity op''))).sup
                             (fun i => (kids0'' i).depth) ≤ 0 at h2
                  omega
              | app op'' kids0'' =>
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 2 at hd
                have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
                  have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k0] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids0' i).depth) ≤ 1 at h1
                have h2 : (kids0' ⟨0, hk0'0_lt⟩).depth ≤ 0 := by
                  have hle : (kids0' ⟨0, hk0'0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids0' i).depth) :=
                    Finset.le_sup (f := fun i => (kids0' i).depth)
                      (Finset.mem_univ
                        (⟨0, hk0'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k0'0] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op''))).sup
                           (fun i => (kids0'' i).depth) ≤ 0 at h2
                omega
            · exact absurd hl (by omega)
          | app op'' kids1'' =>
            -- 3-level depth contradiction (kids1' 1 = .app).
            exfalso
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids i).depth) ≤ 2 at hd
            have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 1 := by
              have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids i).depth) :=
                Finset.le_sup (f := fun i => (kids i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1] at h1
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids1' i).depth) ≤ 1 at h1
            have h2 : (kids1' ⟨1, hk1'1_lt⟩).depth ≤ 0 := by
              have hle : (kids1' ⟨1, hk1'1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids1' i).depth) :=
                Finset.le_sup (f := fun i => (kids1' i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1'1] at h2
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity op''))).sup
                       (fun i => (kids1'' i).depth) ≤ 0 at h2
            omega
        | var j =>
          cases h_k1'1 : (kids1' ⟨1, hk1'1_lt⟩ :
              MinimalBasis.Term EmlBasis 2) with
          | const b'' =>
            -- The genuine cross-variable hard case. T = exp(F) - log(exp(env j) - log b'').
            -- Discharge: same-var sub-cases via duplicate-env LHS; cross-var via helper.
            rw [h_k1'0, h_k1'1] at h00 h10 h01 h_neg10 h_neg01
            simp only [MinimalBasis.Term.eval] at h00 h10 h01 h_neg10 h_neg01
            cases h_k0'0 : (kids0' ⟨0, hk0'0_lt⟩ :
                MinimalBasis.Term EmlBasis 2) with
            | const a =>
              -- F constant. T varies only with G's env j.
              cases h_k0'1 : (kids0' ⟨1, hk0'1_lt⟩ :
                  MinimalBasis.Term EmlBasis 2) with
              | const b' =>
                rw [h_k0'0, h_k0'1] at h00 h10 h01
                simp only [MinimalBasis.Term.eval] at h00 h10 h01
                rcases j with ⟨_ | _ | _, hj⟩
                · rw [show (if (⟨0, hj⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 0
                        from if_pos rfl] at h01
                  linarith
                · have hne : (⟨0 + 1, hj⟩ : Fin 2) ≠ 0 := fun h =>
                    Nat.succ_ne_zero 0 (congrArg Fin.val h)
                  rw [show (if (⟨0 + 1, hj⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 0
                        from if_neg hne] at h10
                  linarith
                · exact absurd hj (by omega)
              | var k =>
                rw [h_k0'0, h_k0'1] at h00 h10 h01
                simp only [MinimalBasis.Term.eval] at h00 h10 h01
                rcases j with ⟨_ | _ | _, hj⟩
                · rcases k with ⟨_ | _ | _, hk⟩
                  · simp at h00 h01; linarith
                  · simp at h00 h01; linarith
                  · exact absurd hk (by omega)
                · rcases k with ⟨_ | _ | _, hk⟩
                  · simp at h00 h10; linarith
                  · simp at h00 h10; linarith
                  · exact absurd hk (by omega)
                · exact absurd hj (by omega)
              | app op'' kids0'' =>
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 2 at hd
                have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
                  have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k0] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids0' i).depth) ≤ 1 at h1
                have h2 : (kids0' ⟨1, hk0'1_lt⟩).depth ≤ 0 := by
                  have hle : (kids0' ⟨1, hk0'1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids0' i).depth) :=
                    Finset.le_sup (f := fun i => (kids0' i).depth)
                      (Finset.mem_univ
                        (⟨1, hk0'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k0'1] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op''))).sup
                           (fun i => (kids0'' i).depth) ≤ 0 at h2
                omega
            | var i =>
              -- F = exp(env i) - Cf. G = exp(env j) - log b''.
              cases h_k0'1 : (kids0' ⟨1, hk0'1_lt⟩ :
                  MinimalBasis.Term EmlBasis 2) with
              | const b' =>
                -- Cf = log b'.
                rw [h_k0'0, h_k0'1] at h00 h10 h01 h_neg10 h_neg01
                simp only [MinimalBasis.Term.eval] at h00 h10 h01 h_neg10 h_neg01
                rcases i with ⟨_ | _ | _, hi⟩
                · -- i = 0
                  rcases j with ⟨_ | _ | _, hj⟩
                  · -- i = 0, j = 0: same var. h00 LHS = h01 LHS after if-reduction.
                    rw [show (if (⟨0, hi⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 0
                          from if_pos rfl] at h01
                    linarith
                  · -- i = 0, j = 1: CROSS-VARIABLE HARD. Use helper.
                    have hne : (⟨0 + 1, hj⟩ : Fin 2) ≠ 0 := fun h =>
                      Nat.succ_ne_zero 0 (congrArg Fin.val h)
                    -- Reduce h00 (already canonical: exp 0 - log b' in F, exp 0 - log b'' in G).
                    -- Reduce h10: F has env_pos 0 = 1, G has env_pos 1 = 0 → 1 - log b''.
                    rw [show (if (⟨0, hi⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 1
                          from if_pos rfl,
                        show (if (⟨0 + 1, hj⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 0
                          from if_neg hne] at h10
                    -- Reduce h_neg10: F has env_neg10 0 = -1, G has env_neg10 1 = 0.
                    rw [show (if (⟨0, hi⟩ : Fin 2) = 0 then (-1 : ℝ) else 0) = -1
                          from if_pos rfl,
                        show (if (⟨0 + 1, hj⟩ : Fin 2) = 0 then (-1 : ℝ) else 0) = 0
                          from if_neg hne] at h_neg10
                    simp only [Real.exp_zero] at h00 h10 h_neg10
                    -- h00: exp(1 - log b') - log(1 - log b'') = 0
                    -- h10: exp(exp 1 - log b') - log(1 - log b'') = 1
                    -- h_neg10: exp(exp(-1) - log b') - log(1 - log b'') = -1
                    exact case9_cross_variable_hard (Real.log b')
                      (Real.log (1 - Real.log b'')) h00 h10 h_neg10
                  · exact absurd hj (by omega)
                · -- i = 1
                  rcases j with ⟨_ | _ | _, hj⟩
                  · -- i = 1, j = 0: CROSS-VARIABLE HARD (symmetric). Use h_neg01.
                    have hne : (⟨0 + 1, hi⟩ : Fin 2) ≠ 0 := fun h =>
                      Nat.succ_ne_zero 0 (congrArg Fin.val h)
                    rw [show (if (⟨0 + 1, hi⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 1
                          from if_neg hne,
                        show (if (⟨0, hj⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 0
                          from if_pos rfl] at h01
                    rw [show (if (⟨0 + 1, hi⟩ : Fin 2) = 0 then 0 else (-1 : ℝ)) = -1
                          from if_neg hne,
                        show (if (⟨0, hj⟩ : Fin 2) = 0 then 0 else (-1 : ℝ)) = 0
                          from if_pos rfl] at h_neg01
                    simp only [Real.exp_zero] at h00 h01 h_neg01
                    exact case9_cross_variable_hard (Real.log b')
                      (Real.log (1 - Real.log b'')) h00 h01 h_neg01
                  · -- i = 1, j = 1: same var. h00 LHS = h10 LHS.
                    have hne_i : (⟨0 + 1, hi⟩ : Fin 2) ≠ 0 := fun h =>
                      Nat.succ_ne_zero 0 (congrArg Fin.val h)
                    rw [show (if (⟨0 + 1, hi⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 0
                          from if_neg hne_i] at h10
                    linarith
                  · exact absurd hj (by omega)
                · exact absurd hi (by omega)
              | var k =>
                -- F = exp(env i) (Cf = 0 since kids0' 1 = var, log(env k) = 0).
                rw [h_k0'0, h_k0'1] at h00 h10 h01 h_neg10 h_neg01
                simp only [MinimalBasis.Term.eval] at h00 h10 h01 h_neg10 h_neg01
                have h_log_neg_one : Real.log (-1 : ℝ) = 0 := by
                  rw [show (-1 : ℝ) = -(1 : ℝ) by ring, Real.log_neg_eq_log,
                      Real.log_one]
                rcases i with ⟨_ | _ | _, hi⟩
                · rcases j with ⟨_ | _ | _, hj⟩
                  · -- i=0, j=0: same var. h00 LHS = h01 LHS.
                    rw [show (if (⟨0, hi⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 0
                          from if_pos rfl] at h01
                    rcases k with ⟨_ | _ | _, hk⟩
                    · simp at h00 h01; linarith
                    · simp at h00 h01; linarith
                    · exact absurd hk (by omega)
                  · -- i=0, j=1: CROSS-VAR. Cf=0. Use helper with h_neg10.
                    have hne : (⟨0 + 1, hj⟩ : Fin 2) ≠ 0 := fun h =>
                      Nat.succ_ne_zero 0 (congrArg Fin.val h)
                    rw [show (if (⟨0, hi⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 1
                          from if_pos rfl,
                        show (if (⟨0 + 1, hj⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 0
                          from if_neg hne] at h10
                    rw [show (if (⟨0, hi⟩ : Fin 2) = 0 then (-1 : ℝ) else 0) = -1
                          from if_pos rfl,
                        show (if (⟨0 + 1, hj⟩ : Fin 2) = 0 then (-1 : ℝ) else 0) = 0
                          from if_neg hne] at h_neg10
                    rcases k with ⟨_ | _ | _, hk⟩
                    · -- k = 0
                      rw [show (if (⟨0, hk⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 1
                            from if_pos rfl] at h10
                      rw [show (if (⟨0, hk⟩ : Fin 2) = 0 then (-1 : ℝ) else 0) = -1
                            from if_pos rfl] at h_neg10
                      simp only [Real.exp_zero, Real.log_one, Real.log_zero,
                                 sub_zero, h_log_neg_one] at h00 h10 h_neg10
                      have h00' : Real.exp (1 - (0 : ℝ)) -
                          Real.log (1 - Real.log b'') = 0 := by
                        simp only [sub_zero]; exact h00
                      have h10' : Real.exp (Real.exp 1 - (0 : ℝ)) -
                          Real.log (1 - Real.log b'') = 1 := by
                        simp only [sub_zero]; exact h10
                      have h_neg10' : Real.exp (Real.exp (-1) - (0 : ℝ)) -
                          Real.log (1 - Real.log b'') = -1 := by
                        simp only [sub_zero]; exact h_neg10
                      exact case9_cross_variable_hard 0
                        (Real.log (1 - Real.log b'')) h00' h10' h_neg10'
                    · -- k = 1
                      have hne_k : (⟨0 + 1, hk⟩ : Fin 2) ≠ 0 := fun h =>
                        Nat.succ_ne_zero 0 (congrArg Fin.val h)
                      rw [show (if (⟨0 + 1, hk⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 0
                            from if_neg hne_k] at h10
                      rw [show (if (⟨0 + 1, hk⟩ : Fin 2) = 0 then (-1 : ℝ) else 0) = 0
                            from if_neg hne_k] at h_neg10
                      simp only [Real.exp_zero, Real.log_one, Real.log_zero,
                                 sub_zero] at h00 h10 h_neg10
                      have h00' : Real.exp (1 - (0 : ℝ)) -
                          Real.log (1 - Real.log b'') = 0 := by
                        simp only [sub_zero]; exact h00
                      have h10' : Real.exp (Real.exp 1 - (0 : ℝ)) -
                          Real.log (1 - Real.log b'') = 1 := by
                        simp only [sub_zero]; exact h10
                      have h_neg10' : Real.exp (Real.exp (-1) - (0 : ℝ)) -
                          Real.log (1 - Real.log b'') = -1 := by
                        simp only [sub_zero]; exact h_neg10
                      exact case9_cross_variable_hard 0
                        (Real.log (1 - Real.log b'')) h00' h10' h_neg10'
                    · exact absurd hk (by omega)
                  · exact absurd hj (by omega)
                · rcases j with ⟨_ | _ | _, hj⟩
                  · -- i=1, j=0: CROSS-VAR. Cf=0. Use h_neg01.
                    have hne : (⟨0 + 1, hi⟩ : Fin 2) ≠ 0 := fun h =>
                      Nat.succ_ne_zero 0 (congrArg Fin.val h)
                    rw [show (if (⟨0 + 1, hi⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 1
                          from if_neg hne,
                        show (if (⟨0, hj⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 0
                          from if_pos rfl] at h01
                    rw [show (if (⟨0 + 1, hi⟩ : Fin 2) = 0 then 0 else (-1 : ℝ)) = -1
                          from if_neg hne,
                        show (if (⟨0, hj⟩ : Fin 2) = 0 then 0 else (-1 : ℝ)) = 0
                          from if_pos rfl] at h_neg01
                    rcases k with ⟨_ | _ | _, hk⟩
                    · -- k = 0
                      rw [show (if (⟨0, hk⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 0
                            from if_pos rfl] at h01
                      rw [show (if (⟨0, hk⟩ : Fin 2) = 0 then 0 else (-1 : ℝ)) = 0
                            from if_pos rfl] at h_neg01
                      simp only [Real.exp_zero, Real.log_one, Real.log_zero,
                                 sub_zero] at h00 h01 h_neg01
                      have h00' : Real.exp (1 - (0 : ℝ)) -
                          Real.log (1 - Real.log b'') = 0 := by
                        simp only [sub_zero]; exact h00
                      have h01' : Real.exp (Real.exp 1 - (0 : ℝ)) -
                          Real.log (1 - Real.log b'') = 1 := by
                        simp only [sub_zero]; exact h01
                      have h_neg01' : Real.exp (Real.exp (-1) - (0 : ℝ)) -
                          Real.log (1 - Real.log b'') = -1 := by
                        simp only [sub_zero]; exact h_neg01
                      exact case9_cross_variable_hard 0
                        (Real.log (1 - Real.log b'')) h00' h01' h_neg01'
                    · -- k = 1
                      have hne_k : (⟨0 + 1, hk⟩ : Fin 2) ≠ 0 := fun h =>
                        Nat.succ_ne_zero 0 (congrArg Fin.val h)
                      rw [show (if (⟨0 + 1, hk⟩ : Fin 2) = 0 then (0 : ℝ) else 1) = 1
                            from if_neg hne_k] at h01
                      rw [show (if (⟨0 + 1, hk⟩ : Fin 2) = 0 then 0 else (-1 : ℝ)) = -1
                            from if_neg hne_k] at h_neg01
                      simp only [Real.exp_zero, Real.log_one, Real.log_zero,
                                 sub_zero, h_log_neg_one] at h00 h01 h_neg01
                      have h00' : Real.exp (1 - (0 : ℝ)) -
                          Real.log (1 - Real.log b'') = 0 := by
                        simp only [sub_zero]; exact h00
                      have h01' : Real.exp (Real.exp 1 - (0 : ℝ)) -
                          Real.log (1 - Real.log b'') = 1 := by
                        simp only [sub_zero]; exact h01
                      have h_neg01' : Real.exp (Real.exp (-1) - (0 : ℝ)) -
                          Real.log (1 - Real.log b'') = -1 := by
                        simp only [sub_zero]; exact h_neg01
                      exact case9_cross_variable_hard 0
                        (Real.log (1 - Real.log b'')) h00' h01' h_neg01'
                    · exact absurd hk (by omega)
                  · -- i=1, j=1: same var. h00 LHS = h10 LHS.
                    have hne_i : (⟨0 + 1, hi⟩ : Fin 2) ≠ 0 := fun h =>
                      Nat.succ_ne_zero 0 (congrArg Fin.val h)
                    rw [show (if (⟨0 + 1, hi⟩ : Fin 2) = 0 then (1 : ℝ) else 0) = 0
                          from if_neg hne_i] at h10
                    rcases k with ⟨_ | _ | _, hk⟩
                    · simp at h00 h10; linarith
                    · simp at h00 h10; linarith
                    · exact absurd hk (by omega)
                  · exact absurd hj (by omega)
                · exact absurd hi (by omega)
              | app op'' kids0'' =>
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 2 at hd
                have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
                  have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k0] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids0' i).depth) ≤ 1 at h1
                have h2 : (kids0' ⟨1, hk0'1_lt⟩).depth ≤ 0 := by
                  have hle : (kids0' ⟨1, hk0'1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids0' i).depth) :=
                    Finset.le_sup (f := fun i => (kids0' i).depth)
                      (Finset.mem_univ
                        (⟨1, hk0'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k0'1] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op''))).sup
                           (fun i => (kids0'' i).depth) ≤ 0 at h2
                omega
            | app op'' kids0'' =>
              exfalso
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids i).depth) ≤ 2 at hd
              have h1 : (kids ⟨0, hk0_lt⟩).depth ≤ 1 := by
                have hle : (kids ⟨0, hk0_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids i).depth) :=
                  Finset.le_sup (f := fun i => (kids i).depth)
                    (Finset.mem_univ
                      (⟨0, hk0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k0] at h1
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids0' i).depth) ≤ 1 at h1
              have h2 : (kids0' ⟨0, hk0'0_lt⟩).depth ≤ 0 := by
                have hle : (kids0' ⟨0, hk0'0_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids0' i).depth) :=
                  Finset.le_sup (f := fun i => (kids0' i).depth)
                    (Finset.mem_univ
                      (⟨0, hk0'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k0'0] at h2
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity op''))).sup
                         (fun i => (kids0'' i).depth) ≤ 0 at h2
              omega
          | var l =>
            -- (kids 1).eval env₀ = exp 0 - log 0 = 1 - 0 = 1. log 1 = 0.
            -- T(env₀) = exp(F(env₀)) - 0 = exp(F(env₀)). h00 = 0 → contra exp_pos.
            rw [h_k1'0, h_k1'1] at h00
            simp only [MinimalBasis.Term.eval, Real.exp_zero, Real.log_zero,
                       sub_zero, Real.log_one] at h00
            linarith [Real.exp_pos
                (Real.exp ((kids0' ⟨0, hk0'0_lt⟩).eval (fun _ : Fin 2 => 0)) -
                 Real.log ((kids0' ⟨1, hk0'1_lt⟩).eval (fun _ : Fin 2 => 0)))]
          | app op'' kids1'' =>
            exfalso
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids i).depth) ≤ 2 at hd
            have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 1 := by
              have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids i).depth) :=
                Finset.le_sup (f := fun i => (kids i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1] at h1
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids1' i).depth) ≤ 1 at h1
            have h2 : (kids1' ⟨1, hk1'1_lt⟩).depth ≤ 0 := by
              have hle : (kids1' ⟨1, hk1'1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids1' i).depth) :=
                Finset.le_sup (f := fun i => (kids1' i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1'1] at h2
            change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity op''))).sup
                       (fun i => (kids1'' i).depth) ≤ 0 at h2
            omega
        | app op'' kids1'' =>
          -- depth contradiction (kids1' 0 = .app)
          exfalso
          change 1 + (Finset.univ :
              Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                     (fun i => (kids i).depth) ≤ 2 at hd
          have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 1 := by
            have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                  (fun i => (kids i).depth) :=
              Finset.le_sup (f := fun i => (kids i).depth)
                (Finset.mem_univ
                  (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
            omega
          rw [h_k1] at h1
          change 1 + (Finset.univ :
              Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                     (fun i => (kids1' i).depth) ≤ 1 at h1
          have h2 : (kids1' ⟨0, hk1'0_lt⟩).depth ≤ 0 := by
            have hle : (kids1' ⟨0, hk1'0_lt⟩).depth ≤
                (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                  (fun i => (kids1' i).depth) :=
              Finset.le_sup (f := fun i => (kids1' i).depth)
                (Finset.mem_univ
                  (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
            omega
          rw [h_k1'0] at h2
          change 1 + (Finset.univ : Finset (Fin (EmlBasis.arity op''))).sup
                     (fun i => (kids1'' i).depth) ≤ 0 at h2
          omega

/-! ## H1.EML.depth_ge_four — depth lower bound for `x + y` ≥ 4

Sharpening H1 from "depth ≥ 3" to "depth ≥ 4" via the **exp-growth lemma**:
any depth-3 `eml(A, B)` globally representing `x + y` forces
`B(v) ≥ exp(-(v 0 + v 1))` on the half-plane `{v 0 + v 1 < 0}`, but no
depth-≤2 EML expression `B` satisfies this exponential growth bound (case
enumeration of depth-≤2 globals on the slice `v = (-t, 0)`).

Math-prose proof: `shared/eml/notes-depth-lower-bound.md` (depth ≥ 4 section,
self-verified 2026-05-12 02:00).

This section builds the proof incrementally. The exp-growth lemma is
discharged; the full theorem awaits the case enumeration. -/

/-! ### H1.4 analytic helpers -/

/-- **Helper.** `(e - 1) * exp a ≥ a + 1` for all real `a`. Used to derive
`log(exp a + a + 1) ≤ a + 1` in the depth-≥-4 enumeration sub-cases.

Proof: case split on sign of `a + 1`. For `a + 1 ≥ 0`: use `Real.add_one_le_exp`
plus `Real.exp_one_gt_two` (giving `e - 1 > 1`). For `a + 1 < 0`: direct
since `(e - 1) * exp a > 0 ≥ a + 1`. -/
private theorem e_minus_one_mul_exp_ge_add_one (a : ℝ) :
    (Real.exp 1 - 1) * Real.exp a ≥ a + 1 := by
  by_cases h_nonneg : 0 ≤ a + 1
  · -- a + 1 ≥ 0
    have h_exp_a : a + 1 ≤ Real.exp a := Real.add_one_le_exp a
    have h_e_gt_2 : Real.exp 1 > 2 := Real.exp_one_gt_two
    have h_exp_a_pos : Real.exp a > 0 := Real.exp_pos a
    nlinarith
  · -- a + 1 < 0
    push_neg at h_nonneg
    have h_e_pos : Real.exp 1 - 1 > 0 := by linarith [Real.exp_one_gt_two]
    have h_exp_a_pos : Real.exp a > 0 := Real.exp_pos a
    have : (Real.exp 1 - 1) * Real.exp a > 0 := mul_pos h_e_pos h_exp_a_pos
    linarith

/-- **Helper.** `Real.exp a + |a| + 2 ≤ Real.exp (|a| + 2)` for all real `a`.
Used for cross-variable sub-cases of `depth_global_xy_ge_four` where the test
point `v 0 = -(|a| + 2)` is needed (uniform across all `a` regardless of sign). -/
private theorem exp_a_plus_abs_a_plus_two_le_exp (a : ℝ) :
    Real.exp a + |a| + 2 ≤ Real.exp (|a| + 2) := by
  have h_e_gt_2 : Real.exp 1 > 2 := Real.exp_one_gt_two
  have h_exp2_gt_4 : Real.exp 2 > 4 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  by_cases h_pos : 0 ≤ a
  · -- a ≥ 0: |a| = a. exp(a + 2) = exp a · exp 2. Need exp a + a + 2 ≤ exp a · exp 2.
    rw [abs_of_nonneg h_pos]
    rw [show a + 2 = a + 2 from rfl, Real.exp_add]
    have h_exp_a_pos : Real.exp a > 0 := Real.exp_pos a
    have h_add_one : a + 1 ≤ Real.exp a := Real.add_one_le_exp a
    nlinarith
  · -- a < 0: |a| = -a. exp(-a + 2) = exp(-a) · exp 2. Need exp a + (-a) + 2 ≤ exp(-a) · exp 2.
    push_neg at h_pos
    rw [abs_of_neg h_pos]
    rw [show -a + 2 = -a + 2 from rfl, Real.exp_add]
    have h_exp_a_lt_one : Real.exp a < 1 := Real.exp_lt_one_iff.mpr h_pos
    have h_neg_a_pos : -a > 0 := by linarith
    have h_exp_neg_a_ge_one : Real.exp (-a) ≥ 1 := by
      have := Real.add_one_le_exp (-a)
      linarith
    have h_addone_neg_a : -a + 1 ≤ Real.exp (-a) := Real.add_one_le_exp (-a)
    nlinarith

/-- **Helper corollary (cross-variable).** `Real.log (Real.exp a + |a| + 2) ≤ |a| + 2`
for all real `a`. Follows from `exp_a_plus_abs_a_plus_two_le_exp` plus log
monotonicity (sum is always positive since exp > 0). -/
private theorem log_exp_a_plus_abs_a_plus_two_le (a : ℝ) :
    Real.log (Real.exp a + |a| + 2) ≤ |a| + 2 := by
  have h_sum_pos : Real.exp a + |a| + 2 > 0 := by
    have := Real.exp_pos a
    have := abs_nonneg a
    linarith
  have h_bound := exp_a_plus_abs_a_plus_two_le_exp a
  have h_log_le := Real.log_le_log h_sum_pos h_bound
  rw [Real.log_exp] at h_log_le
  exact h_log_le

/-- **Helper corollary.** `Real.log (Real.exp a + a + 1) ≤ a + 1` when
`Real.exp a + a + 1 > 0`. Follows from `e_minus_one_mul_exp_ge_add_one`
plus log monotonicity. -/
private theorem log_exp_a_plus_a_plus_one_le (a : ℝ)
    (h : Real.exp a + a + 1 > 0) :
    Real.log (Real.exp a + a + 1) ≤ a + 1 := by
  -- a + 1 ≤ (e-1) exp a (by helper), so exp a + a + 1 ≤ exp a + (e-1) exp a
  --   = e * exp a = exp(a + 1).
  -- log monotonic: log(exp a + a + 1) ≤ log(exp(a+1)) = a + 1.
  have h_bound : (Real.exp 1 - 1) * Real.exp a ≥ a + 1 :=
    e_minus_one_mul_exp_ge_add_one a
  have h_sum_le : Real.exp a + a + 1 ≤ Real.exp (a + 1) := by
    rw [Real.exp_add]
    have : Real.exp a * Real.exp 1 = Real.exp 1 * Real.exp a := mul_comm _ _
    nlinarith
  have h_log_le : Real.log (Real.exp a + a + 1) ≤ Real.log (Real.exp (a + 1)) :=
    Real.log_le_log h h_sum_le
  rw [Real.log_exp] at h_log_le
  exact h_log_le

/-- **Helper.** For `a ≤ 0` and any real `c`, `Real.log (Real.exp a - c) ≤ |c|`.
Used for cross-variable sub-sub-cases of `depth_global_xy_ge_four` where the
inner argument is `Real.exp(v_i) - log_c` and we choose `v_i = -(|log_c| + 1)`. -/
private theorem log_exp_sub_le_abs (a c : ℝ) (ha : a ≤ 0) :
    Real.log (Real.exp a - c) ≤ |c| := by
  have h_exp_pos : Real.exp a > 0 := Real.exp_pos a
  have h_exp_le_one : Real.exp a ≤ 1 := Real.exp_le_one_iff.mpr ha
  -- Triangle inequality: |exp a - c| ≤ |exp a| + |c| = exp a + |c| ≤ 1 + |c|.
  have h_abs : |Real.exp a - c| ≤ 1 + |c| := by
    calc |Real.exp a - c|
        ≤ |Real.exp a| + |c| := abs_sub _ _
      _ = Real.exp a + |c| := by rw [abs_of_pos h_exp_pos]
      _ ≤ 1 + |c| := by linarith
  by_cases h_zero : Real.exp a - c = 0
  · rw [h_zero, Real.log_zero]
    exact abs_nonneg _
  · have h_abs_pos : 0 < |Real.exp a - c| := abs_pos.mpr h_zero
    have h_log_eq : Real.log (Real.exp a - c) = Real.log |Real.exp a - c| := by
      rcases lt_or_gt_of_ne h_zero with h | h
      · rw [abs_of_neg h, Real.log_neg_eq_log]
      · rw [abs_of_pos h]
    rw [h_log_eq]
    have h_one_plus_pos : (0 : ℝ) < 1 + |c| := by
      have := abs_nonneg c; linarith
    have h_log_le := Real.log_le_log h_abs_pos h_abs
    have h_log_one_plus : Real.log (1 + |c|) ≤ |c| := by
      have h := Real.log_le_sub_one_of_pos h_one_plus_pos
      linarith
    linarith

/-- **Helper (deeper).** For `v ≤ 0` and any real `c`,
`Real.log (Real.exp (Real.exp v) - c) ≤ 1 + |c|`.
Used for line 3239's cross-variable sub-sub-cases where `kids' 0 = .app .eml kids_a`
introduces an extra `Real.exp` layer over the inner `Real.exp(v_j)`. -/
private theorem log_exp_exp_v_sub_const_le (v c : ℝ) (hv : v ≤ 0) :
    Real.log (Real.exp (Real.exp v) - c) ≤ 1 + |c| := by
  have hev_pos : Real.exp v > 0 := Real.exp_pos v
  have hev_le_one : Real.exp v ≤ 1 := Real.exp_le_one_iff.mpr hv
  have heev_pos : Real.exp (Real.exp v) > 0 := Real.exp_pos _
  have heev_le_e : Real.exp (Real.exp v) ≤ Real.exp 1 := Real.exp_le_exp.mpr hev_le_one
  -- Bound: |exp(exp v) - c| ≤ exp 1 + |c|.
  have h_abs : |Real.exp (Real.exp v) - c| ≤ Real.exp 1 + |c| := by
    calc |Real.exp (Real.exp v) - c|
        ≤ |Real.exp (Real.exp v)| + |c| := abs_sub _ _
      _ = Real.exp (Real.exp v) + |c| := by rw [abs_of_pos heev_pos]
      _ ≤ Real.exp 1 + |c| := by linarith
  -- exp 1 + |c| ≤ exp(1 + |c|): since exp 1 · exp |c| ≥ exp 1 · (1 + |c|).
  have h_e_plus : Real.exp 1 + |c| ≤ Real.exp (1 + |c|) := by
    rw [Real.exp_add]
    have h_e_pos : Real.exp 1 > 0 := Real.exp_pos 1
    have h_e_ge_one : Real.exp 1 ≥ 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h_add_one_le_exp_abs : 1 + |c| ≤ Real.exp |c| := by
      have := Real.add_one_le_exp |c|; linarith
    have h_abs_nonneg : 0 ≤ |c| := abs_nonneg c
    nlinarith [Real.exp_pos (1 : ℝ)]
  by_cases h_zero : Real.exp (Real.exp v) - c = 0
  · rw [h_zero, Real.log_zero]
    have := abs_nonneg c; linarith
  · have h_abs_pos : 0 < |Real.exp (Real.exp v) - c| := abs_pos.mpr h_zero
    have h_log_eq : Real.log (Real.exp (Real.exp v) - c) =
                    Real.log |Real.exp (Real.exp v) - c| := by
      rcases lt_or_gt_of_ne h_zero with h | h
      · rw [abs_of_neg h, Real.log_neg_eq_log]
      · rw [abs_of_pos h]
    rw [h_log_eq]
    have h_log_le := Real.log_le_log h_abs_pos h_abs
    have h_e_plus_pos : (0 : ℝ) < Real.exp 1 + |c| := by
      have := Real.exp_pos (1 : ℝ); have := abs_nonneg c; linarith
    have h_log_e_plus : Real.log (Real.exp 1 + |c|) ≤ 1 + |c| := by
      have := Real.log_le_log h_e_plus_pos h_e_plus
      rwa [Real.log_exp] at this
    linarith

/-- **Helper (triple-log witness).** For any `K r : ℝ`, there exists a witness
`t ≤ 0` such that `log(exp K − log(exp r − log t)) + t ≤ −1`. This is the
deep-nest helper needed for the kids' 0 = .app, kids' 1 = .app cross-var
sub-cases of `depth_global_xy_ge_four`. Witness: `t = -exp(exp(exp K + exp r + 100))`. -/
private theorem log_triple_nest_witness (K r : ℝ) :
    Real.log (Real.exp K - Real.log (Real.exp r -
      Real.log (-Real.exp (Real.exp (Real.exp K + Real.exp r + 100))))) +
      (-Real.exp (Real.exp (Real.exp K + Real.exp r + 100))) ≤ -1 := by
  -- Layer 1: log t = exp M, where M = exp K + exp r + 100.
  set M : ℝ := Real.exp K + Real.exp r + 100 with hM_def
  set t : ℝ := -Real.exp (Real.exp M) with ht_def
  have hM_pos : M > 0 := by
    have := Real.exp_pos K
    have := Real.exp_pos r
    simp [hM_def]; linarith
  have h_logt : Real.log t = Real.exp M := by
    show Real.log (-Real.exp (Real.exp M)) = Real.exp M
    rw [Real.log_neg_eq_log, Real.log_exp]
  -- Layer 2: exp r - log t = exp r - exp M < 0.
  have h_exp_r_lt_M : Real.exp r < Real.exp M := by
    apply Real.exp_lt_exp.mpr
    have h_exp_r_pos : Real.exp r > 0 := Real.exp_pos r
    have h_exp_K_pos : Real.exp K > 0 := Real.exp_pos K
    have h_r_lt_exp_r : r < Real.exp r + 1 := by
      have := Real.add_one_le_exp r; linarith
    simp [hM_def]; linarith
  have h_inner_neg : Real.exp r - Real.log t < 0 := by
    rw [h_logt]; linarith
  -- |exp r - exp M| = exp M - exp r.
  have h_log_inner : Real.log (Real.exp r - Real.log t) =
                     Real.log (Real.exp M - Real.exp r) := by
    rw [h_logt]
    have : Real.exp r - Real.exp M = -(Real.exp M - Real.exp r) := by ring
    rw [this, Real.log_neg_eq_log]
  -- exp M - exp r > 0 (from h_exp_r_lt_M).
  have h_M_minus_r_pos : Real.exp M - Real.exp r > 0 := by linarith
  -- log(exp M - exp r) ≤ M.
  have h_log_diff_le_M : Real.log (Real.exp M - Real.exp r) ≤ M := by
    have h_le : Real.exp M - Real.exp r ≤ Real.exp M := by
      have := Real.exp_pos r; linarith
    have := Real.log_le_log h_M_minus_r_pos h_le
    rwa [Real.log_exp] at this
  -- log(exp M - exp r) ≥ M - log 2 (when exp r ≤ exp M / 2, i.e., r + log 2 ≤ M).
  have h_r_plus_log2_le_M : r + Real.log 2 ≤ M := by
    have h_exp_K_ge : Real.exp K ≥ K + 1 := Real.add_one_le_exp K
    have h_exp_r_ge : Real.exp r ≥ r + 1 := Real.add_one_le_exp r
    -- M = exp K + exp r + 100 ≥ (K+1) + (r+1) + 100 ≥ r + 102 + K.
    -- r + log 2 ≤ M iff log 2 ≤ M - r.
    -- M - r ≥ (K + 1) + (r + 1) + 100 - r = K + 102 ≥ 102 - |K| (if K ≥ -102).
    -- Hmm, K could be very negative. Use exp K ≥ 0 instead.
    have h_exp_K_pos : Real.exp K > 0 := Real.exp_pos K
    have h_log2_lt_one : Real.log 2 < 1 := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
      exact Real.log_lt_log (by norm_num) Real.exp_one_gt_two
    simp [hM_def]
    linarith
  have h_log_diff_ge : Real.log (Real.exp M - Real.exp r) ≥ M - Real.log 2 := by
    have h_diff_ge_half : Real.exp M - Real.exp r ≥ Real.exp M / 2 := by
      have h_exp_r_le_half : Real.exp r ≤ Real.exp M / 2 := by
        have h_exp_log2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num : (0:ℝ) < 2)
        have h_exp_le := Real.exp_le_exp.mpr h_r_plus_log2_le_M
        rw [Real.exp_add, h_exp_log2] at h_exp_le
        linarith
      linarith
    have h_half_pos : Real.exp M / 2 > 0 := by
      have := Real.exp_pos M; linarith
    have h := Real.log_le_log h_half_pos h_diff_ge_half
    have h_log_half : Real.log (Real.exp M / 2) = M - Real.log 2 := by
      rw [Real.log_div (by have := Real.exp_pos M; linarith) (by norm_num : (2:ℝ) ≠ 0),
          Real.log_exp]
    linarith [h, h_log_half.le]
  -- exp K - log(exp r - log t) = exp K - log(exp M - exp r) ≤ exp K - (M - log 2)
  --   = exp K - exp K - exp r - 100 + log 2 = -exp r - 100 + log 2 < 0.
  have h_outer_neg : Real.exp K - Real.log (Real.exp r - Real.log t) < 0 := by
    rw [h_log_inner]
    have h_exp_r_pos : Real.exp r > 0 := Real.exp_pos r
    have h_log2_lt_one : Real.log 2 < 1 := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
      exact Real.log_lt_log (by norm_num) Real.exp_one_gt_two
    -- exp K - log(exp M - exp r) ≤ exp K - (M - log 2) = -exp r - 100 + log 2 < 0.
    have : Real.exp K - Real.log (Real.exp M - Real.exp r) ≤
           Real.exp K - (M - Real.log 2) := by linarith
    have h_simplification : Real.exp K - (M - Real.log 2) = -Real.exp r - 100 + Real.log 2 := by
      simp [hM_def]; ring
    linarith
  -- log of negative: log(exp K - log(exp r - log t)) = log|...|.
  have h_outer_log_eq : Real.log (Real.exp K - Real.log (Real.exp r - Real.log t)) =
                       Real.log (Real.log (Real.exp M - Real.exp r) - Real.exp K) := by
    rw [h_log_inner]
    have h_neg : Real.exp K - Real.log (Real.exp M - Real.exp r) =
                 -(Real.log (Real.exp M - Real.exp r) - Real.exp K) := by ring
    rw [h_neg, Real.log_neg_eq_log]
  -- log(exp M - exp r) - exp K ≤ M - exp K = exp r + 100.
  have h_outer_arg_le : Real.log (Real.exp M - Real.exp r) - Real.exp K ≤
                        Real.exp r + 100 := by
    have h_M_minus_K : M - Real.exp K = Real.exp r + 100 := by
      simp [hM_def]; ring
    linarith [h_log_diff_le_M, h_M_minus_K.ge]
  -- log(exp M - exp r) - exp K > 0.
  have h_outer_arg_pos : Real.log (Real.exp M - Real.exp r) - Real.exp K > 0 := by
    rw [h_log_inner] at h_outer_neg
    linarith
  -- log of arg ≤ log(exp r + 100).
  have h_exp_r_plus_100_pos : (0 : ℝ) < Real.exp r + 100 := by
    have := Real.exp_pos r; linarith
  have h_outer_log_le : Real.log (Real.log (Real.exp M - Real.exp r) - Real.exp K) ≤
                       Real.log (Real.exp r + 100) := by
    exact Real.log_le_log h_outer_arg_pos h_outer_arg_le
  -- log(exp r + 100) ≤ exp r + 99 (using log y ≤ y - 1).
  have h_log_exp_r_plus_100 : Real.log (Real.exp r + 100) ≤ Real.exp r + 99 := by
    have h := Real.log_le_sub_one_of_pos h_exp_r_plus_100_pos
    linarith
  -- Combine: log(...) ≤ exp r + 99.
  have h_outer_log_total : Real.log (Real.exp K - Real.log (Real.exp r - Real.log t)) ≤
                          Real.exp r + 99 := by
    rw [h_outer_log_eq]
    linarith
  -- t = -exp(exp M). Need exp(exp M) ≥ exp r + 100.
  -- exp M ≥ exp(exp r + 100) (since M ≥ exp r + 100).
  -- exp(exp r + 100) ≥ exp 100 > 22000.
  -- Hmm we want exp(exp M) ≥ exp r + 100.
  -- exp(exp M) ≥ exp M (since exp M ≥ 1 for M ≥ 0).
  -- exp M ≥ exp(exp r + 100) ≥ exp 100 > 22000 > exp r + 100 (for r ≤ ~10).
  -- For r > 10, exp r grows; need tighter.
  -- exp(exp M) ≥ exp(exp(exp r + 100)). exp(exp r + 100) > exp r + 100 (since exp y > y).
  -- So exp(exp M) > exp(exp r + 100) > exp r + 100. ✓
  have h_M_ge : M ≥ Real.exp r + 100 := by
    have := Real.exp_pos K; simp [hM_def]; linarith
  have h_expM_ge : Real.exp M ≥ Real.exp (Real.exp r + 100) :=
    Real.exp_le_exp.mpr h_M_ge
  have h_exp_y_gt_y : Real.exp (Real.exp r + 100) > Real.exp r + 100 := by
    have h := Real.add_one_lt_exp (x := Real.exp r + 100)
      (by have := Real.exp_pos r; intro hk; linarith)
    linarith
  have h_expM_gt : Real.exp M > Real.exp r + 100 := by linarith
  have h_exp_expM_ge : Real.exp (Real.exp M) ≥ Real.exp M :=
    Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp M])
  have h_exp_expM_gt : Real.exp (Real.exp M) > Real.exp r + 100 := by linarith
  -- Final: log(...) + t ≤ (exp r + 99) - exp(exp M) ≤ -1.
  show Real.log (Real.exp K - Real.log (Real.exp r - Real.log t)) + t ≤ -1
  linarith

/-- **Helper (Alt-2 same-var triple-log bound).** Parameterized over `t` with an
explicit hypothesis on its magnitude. The proof uses case-split on the sign of
`exp K − log(exp t − log t)` to avoid `set`/`rcases` friction.

Math content: with `t` so negative that `-t ≥ exp(exp(exp(|K|+100)))`:
- Positive case: `log(arg) ≤ K`, and `t ≤ -K - 1`, so LHS ≤ -1.
- Non-positive case: junk-extend; `log|arg| ≤ log(-t) - 2`, and `log(-t) + t ≤ -1`,
  so LHS ≤ -3 ≤ -1.
-/
private theorem log_triple_nest_same_var_bound (K t : ℝ)
    (h_t_bound : t ≤ -Real.exp (Real.exp (Real.exp (|K| + 100)))) :
    Real.log (Real.exp K - Real.log (Real.exp t - Real.log t)) + t ≤ -1 := by
  have h_exp_K_pos : Real.exp K > 0 := Real.exp_pos K
  have h_M_pos : Real.exp (|K| + 100) > 0 := Real.exp_pos _
  have h_eM_pos : Real.exp (Real.exp (|K| + 100)) > 0 := Real.exp_pos _
  have h_eeM_pos : Real.exp (Real.exp (Real.exp (|K| + 100))) > 0 := Real.exp_pos _
  have h_t_lt_0 : t < 0 := by linarith
  have h_neg_t_pos : -t > 0 := by linarith
  have h_M_ge_K_101 : Real.exp (|K| + 100) ≥ |K| + 101 := by
    have := Real.add_one_le_exp (|K| + 100); linarith
  have h_eM_ge_K_102 : Real.exp (Real.exp (|K| + 100)) ≥ |K| + 102 := by
    have := Real.add_one_le_exp (Real.exp (|K| + 100)); linarith
  have h_eeM_ge_K_103 : Real.exp (Real.exp (Real.exp (|K| + 100))) ≥ |K| + 103 := by
    have := Real.add_one_le_exp (Real.exp (Real.exp (|K| + 100))); linarith
  have h_neg_t_ge : -t ≥ |K| + 103 := by linarith
  have h_t_le_neg_K_minus_1 : t ≤ -K - 1 := by
    have h_K_le_absK : K ≤ |K| := le_abs_self K; linarith
  have h_logt_eq : Real.log t = Real.log (-t) := (Real.log_neg_eq_log t).symm
  have h_logt_le : Real.log (-t) ≤ -t - 1 := Real.log_le_sub_one_of_pos h_neg_t_pos
  have h_logt_huge : Real.log (-t) ≥ |K| + 102 := by
    have h := Real.log_le_log h_eeM_pos
      (show Real.exp (Real.exp (Real.exp (|K| + 100))) ≤ -t by linarith)
    rw [Real.log_exp] at h
    linarith
  have h_logt_pos : Real.log (-t) > 0 := by have := abs_nonneg K; linarith
  have h_logt_ge_2 : Real.log (-t) ≥ 2 := by have := abs_nonneg K; linarith
  have h_eeM_ge_1 : Real.exp (Real.exp (Real.exp (|K| + 100))) ≥ 1 := by
    have := abs_nonneg K; linarith
  have h_t_le_neg_1 : t ≤ -1 := by linarith
  have h_exp_t_le_neg_1 : Real.exp t ≤ Real.exp (-1 : ℝ) :=
    Real.exp_le_exp.mpr h_t_le_neg_1
  have h_exp_neg_1_lt_1 : Real.exp (-1 : ℝ) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  have h_exp_t_lt_1 : Real.exp t < 1 := by linarith
  have h_exp_t_pos : Real.exp t > 0 := Real.exp_pos t
  have h_inner_neg : Real.exp t - Real.log t < 0 := by rw [h_logt_eq]; linarith
  have h_log_inner_eq : Real.log (Real.exp t - Real.log t) =
                       Real.log (Real.log (-t) - Real.exp t) := by
    rw [h_logt_eq]
    have h_neg : Real.exp t - Real.log (-t) = -(Real.log (-t) - Real.exp t) := by ring
    rw [h_neg, Real.log_neg_eq_log]
  have h_diff_ge_1 : Real.log (-t) - Real.exp t ≥ 1 := by linarith
  have h_log_inner_nonneg : Real.log (Real.exp t - Real.log t) ≥ 0 := by
    rw [h_log_inner_eq]; exact Real.log_nonneg h_diff_ge_1
  have h_log_inner_le : Real.log (Real.exp t - Real.log t) ≤ Real.log (-t) - 1 := by
    rw [h_log_inner_eq]
    have h_le_log_logt :
        Real.log (Real.log (-t) - Real.exp t) ≤ Real.log (Real.log (-t)) :=
      Real.log_le_log (by linarith) (by linarith)
    have h_log_logt_le : Real.log (Real.log (-t)) ≤ Real.log (-t) - 1 :=
      Real.log_le_sub_one_of_pos h_logt_pos
    linarith
  -- Case-split on sign of outer arg.
  by_cases h_arg_pos : Real.exp K - Real.log (Real.exp t - Real.log t) > 0
  · -- Positive: log(...) ≤ log(exp K) = K, LHS ≤ K + t ≤ -1.
    have h_arg_le_exp_K :
        Real.exp K - Real.log (Real.exp t - Real.log t) ≤ Real.exp K := by linarith
    have h_log_le := Real.log_le_log h_arg_pos h_arg_le_exp_K
    rw [Real.log_exp] at h_log_le
    linarith
  · push_neg at h_arg_pos
    by_cases h_arg_zero : Real.exp K - Real.log (Real.exp t - Real.log t) = 0
    · rw [h_arg_zero, Real.log_zero]; linarith
    · have h_arg_neg : Real.exp K - Real.log (Real.exp t - Real.log t) < 0 :=
        lt_of_le_of_ne h_arg_pos h_arg_zero
      have h_log_arg_eq :
          Real.log (Real.exp K - Real.log (Real.exp t - Real.log t)) =
          Real.log (Real.log (Real.exp t - Real.log t) - Real.exp K) := by
        have h_neg : Real.exp K - Real.log (Real.exp t - Real.log t) =
                     -(Real.log (Real.exp t - Real.log t) - Real.exp K) := by ring
        rw [h_neg, Real.log_neg_eq_log]
      rw [h_log_arg_eq]
      have h_inner_pos :
          Real.log (Real.exp t - Real.log t) - Real.exp K > 0 := by linarith
      have h_inner_le_log_neg_t :
          Real.log (Real.exp t - Real.log t) - Real.exp K ≤ Real.log (-t) - 1 := by linarith
      have h_log_le := Real.log_le_log h_inner_pos h_inner_le_log_neg_t
      have h_log_logt_minus_1_le :
          Real.log (Real.log (-t) - 1) ≤ Real.log (-t) - 2 := by
        have h_pos : Real.log (-t) - 1 > 0 := by linarith
        have := Real.log_le_sub_one_of_pos h_pos
        linarith
      linarith

/-- **Witness wrapper.** Provides the explicit existential form. -/
private theorem log_triple_nest_same_var_witness (K : ℝ) :
    Real.log (Real.exp K - Real.log (Real.exp
      (-Real.exp (Real.exp (Real.exp (|K| + 100)))) - Real.log
      (-Real.exp (Real.exp (Real.exp (|K| + 100)))))) +
      (-Real.exp (Real.exp (Real.exp (|K| + 100)))) ≤ -1 :=
  log_triple_nest_same_var_bound K (-Real.exp (Real.exp (Real.exp (|K| + 100))))
    (le_refl _)

/-- **Helper #11 (swap-form triple-log bound).** Cross-form analog of
`log_triple_nest_same_var_bound`. For the H1.4 sub-case where `kids_r 0 = var
(active)` and `kids_r 1 = const r1`: the inner sub-tree evaluates to
`exp t - R` where `R = Real.log r1`.

Statement: For K, R ∈ ℝ and t sufficiently negative,
  `log(exp K - log(exp t - R)) + t ≤ -1`.

Math content: with `t ≤ -exp(exp(exp(|K| + |R| + |Real.log R| + 100)))`,
- Upper bound on inner: `Real.log(exp t - R) ≤ |R|` (uniform).
- Lower bound on inner: `Real.log(exp t - R) ≥ t - |Real.log R| - 1`.
- Hence `|exp K - Real.log(exp t - R)| ≤ exp K + (-t) + |Real.log R| + 1 ≤ 2(-t)`.
- `log(2(-t)) ≤ 2 log 2 - 1 + (-t)/2` via `log y ≤ y/2 + log 2 - 1`.
- Adding t: `log + t ≤ 2 log 2 - 1 - (-t)/2 ≤ -1` for `-t ≥ 4 log 2`. -/
private theorem log_triple_nest_swap_bound (K R t : ℝ)
    (h_t_bound : t ≤ -Real.exp (Real.exp (Real.exp
        (|K| + |R| + |Real.log R| + 100)))) :
    Real.log (Real.exp K - Real.log (Real.exp t - R)) + t ≤ -1 := by
  -- Step 1: Setup size constants.
  set M : ℝ := |K| + |R| + |Real.log R| + 100 with hM_def
  have hK_nn : (0 : ℝ) ≤ |K| := abs_nonneg K
  have hR_nn : (0 : ℝ) ≤ |R| := abs_nonneg R
  have hLR_nn : (0 : ℝ) ≤ |Real.log R| := abs_nonneg _
  have hM_ge_100 : M ≥ 100 := by simp [hM_def]; linarith
  have hM_pos : M > 0 := by linarith
  have h_eM_pos : Real.exp M > 0 := Real.exp_pos _
  have h_eeM_pos : Real.exp (Real.exp M) > 0 := Real.exp_pos _
  have h_eM_ge : Real.exp M ≥ M + 1 := Real.add_one_le_exp M
  have h_eeM_ge : Real.exp (Real.exp M) ≥ Real.exp M + 1 := Real.add_one_le_exp _
  have h_eeeM_ge_eeM : Real.exp (Real.exp (Real.exp M)) ≥ Real.exp (Real.exp M) + 1 :=
    Real.add_one_le_exp _
  have h_eeeM_ge_M : Real.exp (Real.exp (Real.exp M)) ≥ M + 3 := by linarith
  -- -t bounds.
  have h_neg_t_ge : -t ≥ Real.exp (Real.exp (Real.exp M)) := by linarith
  have h_neg_t_ge_M : -t ≥ M + 3 := by linarith
  have h_neg_t_pos : -t > 0 := by linarith
  have h_t_lt_0 : t < 0 := by linarith
  have h_t_le_0 : t ≤ 0 := le_of_lt h_t_lt_0
  have h_neg_t_ge_K : -t ≥ |K| + |R| + |Real.log R| + 103 := by
    have h : M + 3 = |K| + |R| + |Real.log R| + 103 := by simp [hM_def]; ring
    linarith
  -- exp t bounds.
  have h_exp_t_le_1 : Real.exp t ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr h_t_le_0
  have h_exp_t_pos : Real.exp t > 0 := Real.exp_pos t
  have h_log_2_lt_1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have h_log_2_nn : Real.log 2 ≥ 0 := Real.log_nonneg (by norm_num)
  -- log y ≤ y/2 - 1 + log 2 for y > 0 (via log_le_sub_one_of_pos on y/2).
  have h_log_le_half : ∀ y : ℝ, y > 0 → Real.log y ≤ y/2 - 1 + Real.log 2 := by
    intro y hy_pos
    have h_half_pos : y/2 > 0 := by linarith
    have h := Real.log_le_sub_one_of_pos h_half_pos
    have h_y_eq : y = y/2 * 2 := by ring
    have h_split : Real.log y = Real.log (y/2) + Real.log 2 := by
      conv_lhs => rw [h_y_eq]
      exact Real.log_mul (ne_of_gt h_half_pos) (by norm_num : (2:ℝ) ≠ 0)
    linarith
  -- Step 2: bound the inner log.
  -- Upper: Real.log(exp t - R) ≤ |R| (uniform).
  -- Lower: Real.log(exp t - R) ≥ t - |Real.log R| - 1 (uniform).
  have h_inner_log_le_R : Real.log (Real.exp t - R) ≤ |R| := by
    by_cases hR : R = 0
    · subst hR
      rw [sub_zero, Real.log_exp]
      simp only [abs_zero]
      linarith
    · have hR_abs_pos : |R| > 0 := abs_pos.mpr hR
      have h_log_eq_abs : Real.log (Real.exp t - R) = Real.log |Real.exp t - R| :=
        (Real.log_abs _).symm
      have h_inner_abs_le : |Real.exp t - R| ≤ 1 + |R| := by
        calc |Real.exp t - R| ≤ |Real.exp t| + |R| := abs_sub _ _
          _ = Real.exp t + |R| := by rw [abs_of_pos h_exp_t_pos]
          _ ≤ 1 + |R| := by linarith
      have h_1_plus_R_pos : (1 : ℝ) + |R| > 0 := by linarith
      by_cases h_inner_eq_zero : Real.exp t - R = 0
      · rw [h_inner_eq_zero, Real.log_zero]; exact abs_nonneg R
      · have h_inner_abs_pos : |Real.exp t - R| > 0 := abs_pos.mpr h_inner_eq_zero
        rw [h_log_eq_abs]
        calc Real.log |Real.exp t - R|
            ≤ Real.log (1 + |R|) := Real.log_le_log h_inner_abs_pos h_inner_abs_le
          _ ≤ |R| := by
              have h := Real.log_le_sub_one_of_pos h_1_plus_R_pos; linarith
  have h_inner_log_ge : Real.log (Real.exp t - R) ≥ t - |Real.log R| - 1 := by
    by_cases hR : R = 0
    · subst hR
      rw [sub_zero, Real.log_exp]
      simp only [Real.log_zero, abs_zero]
      linarith
    · -- R ≠ 0. exp t ≤ |R|/2 from t-bound, so |exp t - R| ≥ |R|/2.
      have hR_abs_pos : |R| > 0 := abs_pos.mpr hR
      have h_log_R_abs : Real.log R = Real.log |R| := (Real.log_abs R).symm
      have h_exp_t_le_R_half : Real.exp t ≤ |R| / 2 := by
        have h_t_le : t ≤ -|Real.log R| - 1 := by linarith
        have h_t_le_log : t ≤ Real.log |R| - 1 := by
          rw [h_log_R_abs] at h_t_le
          have h_neg_abs : -(abs (Real.log |R|)) ≤ Real.log |R| := by
            have := neg_le_abs (Real.log |R|); linarith
          linarith
        have h_exp_le : Real.exp t ≤ Real.exp (Real.log |R| - 1) :=
          Real.exp_le_exp.mpr h_t_le_log
        rw [Real.exp_sub, Real.exp_log hR_abs_pos] at h_exp_le
        have h_exp1_ge_2 : Real.exp (1 : ℝ) ≥ 2 := by
          have := Real.add_one_le_exp (1:ℝ); linarith
        have h_exp1_pos : Real.exp 1 > 0 := Real.exp_pos 1
        have h_div_le : |R| / Real.exp 1 ≤ |R| / 2 :=
          div_le_div_of_nonneg_left (le_of_lt hR_abs_pos) (by norm_num : (0:ℝ) < 2) h_exp1_ge_2
        linarith
      have h_inner_abs_ge : |Real.exp t - R| ≥ |R| / 2 := by
        have h_swap : |Real.exp t - R| = |R - Real.exp t| := abs_sub_comm _ _
        rw [h_swap]
        calc |R - Real.exp t| ≥ |R| - |Real.exp t| := by
              have := abs_sub_abs_le_abs_sub R (Real.exp t); linarith
          _ = |R| - Real.exp t := by rw [abs_of_pos h_exp_t_pos]
          _ ≥ |R| - |R|/2 := by linarith
          _ = |R|/2 := by ring
      have h_R_half_pos : |R| / 2 > 0 := by linarith
      have h_inner_abs_pos : |Real.exp t - R| > 0 := by linarith
      have h_log_eq_abs : Real.log (Real.exp t - R) = Real.log |Real.exp t - R| :=
        (Real.log_abs _).symm
      rw [h_log_eq_abs]
      calc Real.log |Real.exp t - R|
          ≥ Real.log (|R| / 2) := Real.log_le_log h_R_half_pos h_inner_abs_ge
        _ = Real.log |R| - Real.log 2 := by
            rw [Real.log_div (ne_of_gt hR_abs_pos) (by norm_num : (2:ℝ) ≠ 0)]
        _ ≥ -|Real.log R| - 1 := by
            have h_neg_log_R_abs_le : -Real.log |R| ≤ |Real.log R| := by
              rw [h_log_R_abs]; exact neg_le_abs _
            linarith
        _ ≥ t - |Real.log R| - 1 := by linarith
  -- Step 3: Bound |outer arg| = |exp K - Real.log(exp t - R)| ≤ 2(-t).
  -- Chain: exp K + |Real.log R| + 1 ≤ exp M + M + 1 ≤ 2 exp M ≤ exp(exp M) ≤ -t.
  have h_K_le_M : K ≤ M := by
    have hK_le : K ≤ |K| := le_abs_self K
    simp [hM_def]; linarith
  have h_LR_le_M : |Real.log R| ≤ M := by simp [hM_def]; linarith
  have h_exp_K_le_eM : Real.exp K ≤ Real.exp M := Real.exp_le_exp.mpr h_K_le_M
  -- exp(M+1) ≥ 2 exp M.
  have h_exp_1_ge_2 : Real.exp 1 ≥ 2 := by
    have := Real.add_one_le_exp (1:ℝ); linarith
  have h_exp_M_plus_1_eq : Real.exp (M + 1) = Real.exp M * Real.exp 1 := by
    rw [Real.exp_add]
  have h_exp_M_plus_1_ge_2eM : Real.exp (M + 1) ≥ 2 * Real.exp M := by
    rw [h_exp_M_plus_1_eq]
    have := Real.exp_pos M; nlinarith [h_exp_1_ge_2]
  -- exp(exp M) ≥ exp(M+1) since exp M ≥ M + 1.
  have h_eeM_ge_exp_M_plus_1 : Real.exp (Real.exp M) ≥ Real.exp (M + 1) :=
    Real.exp_le_exp.mpr (by linarith)
  have h_eeM_ge_2_eM : Real.exp (Real.exp M) ≥ 2 * Real.exp M := by linarith
  -- exp(exp(exp M)) ≥ exp(exp M) since exp M ≥ 0.
  have h_eeeM_ge_eeM : Real.exp (Real.exp (Real.exp M)) ≥ Real.exp (Real.exp M) :=
    Real.exp_le_exp.mpr (by linarith)
  -- Combine: -t ≥ 2 exp M.
  have h_neg_t_ge_2eM : -t ≥ 2 * Real.exp M := by linarith
  -- exp M + M + 1 ≤ 2 exp M (using exp M ≥ M + 1).
  have h_2eM_ge_eM_plus_M_plus_1 : 2 * Real.exp M ≥ Real.exp M + (M + 1) := by linarith
  -- Conclude: exp K + |Real.log R| + 1 ≤ 2 exp M ≤ -t.
  have h_exp_K_LR_le_neg_t : Real.exp K + |Real.log R| + 1 ≤ -t := by
    calc Real.exp K + |Real.log R| + 1
        ≤ Real.exp M + M + 1 := by linarith
      _ ≤ 2 * Real.exp M := by linarith
      _ ≤ -t := h_neg_t_ge_2eM
  have h_outer_le_2neg_t : Real.exp K - Real.log (Real.exp t - R) ≤ 2 * (-t) := by
    have h_neg_inner_le : -Real.log (Real.exp t - R) ≤ -t + |Real.log R| + 1 := by
      linarith [h_inner_log_ge]
    linarith
  -- Lower bound on outer arg: exp K - |R| ≥ -|R| ≥ -(-t).
  have h_R_le_M : |R| ≤ M := by simp [hM_def]; linarith
  have h_R_le_neg_t : |R| ≤ -t := by linarith
  have h_outer_ge_neg_2neg_t : Real.exp K - Real.log (Real.exp t - R) ≥ -2 * (-t) := by
    have h_inner_le : Real.log (Real.exp t - R) ≤ |R| := h_inner_log_le_R
    linarith [Real.exp_pos K]
  -- |outer arg| ≤ 2(-t).
  have h_outer_abs_le : |Real.exp K - Real.log (Real.exp t - R)| ≤ 2 * (-t) := by
    rw [abs_le]; exact ⟨by linarith, h_outer_le_2neg_t⟩
  -- Step 4: Real.log(outer arg) ≤ Real.log|outer arg| ≤ log(2(-t)).
  have h_2neg_t_pos : 2 * (-t) > 0 := by linarith
  have h_outer_log_le : Real.log (Real.exp K - Real.log (Real.exp t - R)) ≤
                       Real.log (2 * (-t)) := by
    by_cases h_outer_zero : Real.exp K - Real.log (Real.exp t - R) = 0
    · rw [h_outer_zero, Real.log_zero]; exact Real.log_nonneg (by linarith)
    · have h_outer_abs_pos : |Real.exp K - Real.log (Real.exp t - R)| > 0 :=
        abs_pos.mpr h_outer_zero
      have h_log_eq_abs :
          Real.log (Real.exp K - Real.log (Real.exp t - R)) =
          Real.log |Real.exp K - Real.log (Real.exp t - R)| :=
        (Real.log_abs _).symm
      rw [h_log_eq_abs]
      exact Real.log_le_log h_outer_abs_pos h_outer_abs_le
  -- log(2(-t)) = log 2 + log(-t) ≤ log 2 + (-t)/2 - 1 + log 2 = 2 log 2 - 1 + (-t)/2.
  have h_log_2neg_t : Real.log (2 * (-t)) ≤ 2 * Real.log 2 - 1 + (-t)/2 := by
    have h_split : Real.log (2 * (-t)) = Real.log 2 + Real.log (-t) := by
      rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt h_neg_t_pos)]
    have h_log_neg_t : Real.log (-t) ≤ (-t)/2 - 1 + Real.log 2 :=
      h_log_le_half (-t) h_neg_t_pos
    linarith
  -- Step 5: Conclude.
  have h_neg_t_huge : -t ≥ 4 * Real.log 2 + 4 := by
    have : (4 : ℝ) * Real.log 2 + 4 ≤ 8 := by linarith
    linarith
  linarith

/-- **Helper #12 (cross-var diagonal asymptotic-gap contradiction).** For the H1.4
cross-var sub-cases under diagonal witness `(v_0, v_1) = (t, t)` with t very negative:
the H1.4 hypothesis `K - Real.log Y = 2*t` becomes structurally impossible when
`K > 0`, `Real.log Y` is bounded asymptotically below `-t`, and `t < 0`.

Statement: For K, Y, t ∈ ℝ with `0 < K`, `Real.log Y ≤ -t`, and `t < 0`,
  `K - Real.log Y ≠ 2 * t`.

Math: If `K - Real.log Y = 2*t`, then `K = 2*t + Real.log Y ≤ 2*t + (-t) = t < 0`,
contradicting `K > 0`. The shape-specific work (deriving `Real.log Y ≤ -t` per
`(kids 0)` / `(kids_r)` enumeration) lives at the call site. -/
private theorem cross_var_diagonal_contra (K Y t : ℝ)
    (h_K_pos : 0 < K)
    (h_Y_upper : Real.log Y ≤ -t)
    (h_t_neg : t < 0) :
    K - Real.log Y ≠ 2 * t := by
  intro h_eq
  -- From h_eq: K = 2t + log Y ≤ 2t + (-t) = t. But K > 0 and t < 0.
  have h_K_le : K ≤ t := by linarith
  linarith

/-- **Helper #12 refined (cross-var diagonal uniform bound).** For the H1.4 cross-var
sub-cases under diagonal witness `(v_0, v_1) = (t, t)`: under the loose hypothesis
that `|Real.log (S t)|` is bounded by `|t|` (junk-aware), the outer log expression
plus `2t` collapses to ≤ -1.

Statement: For `S : ℝ → ℝ` and `t ≤ -3` with `|Real.log (S t)| ≤ |t|`,
  `log(exp(exp t - log t) - log(S t)) + 2*t ≤ -1`.

This is the uniform helper for direction β diagonal witness across all 4 cross-var
shapes (const/var × const/var). Per-shape work at call site is just discharging the
`h_S_logbound` hypothesis. -/
private theorem log_diagonal_cross_bound (S : ℝ → ℝ) (t : ℝ)
    (h_S_logbound : |Real.log (S t)| ≤ |t|)
    (h_t_bound : t ≤ -3) :
    Real.log (Real.exp (Real.exp t - Real.log t) - Real.log (S t)) + 2 * t ≤ -1 := by
  -- Setup.
  have h_t_lt_0 : t < 0 := by linarith
  have h_neg_t_pos : -t > 0 := by linarith
  have h_neg_t_ge_3 : -t ≥ 3 := by linarith
  have h_abs_t : |t| = -t := abs_of_neg h_t_lt_0
  -- exp t ≤ 1 (t ≤ 0).
  have h_exp_t_le_1 : Real.exp t ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have h_exp_t_pos : Real.exp t > 0 := Real.exp_pos t
  -- log t = log(-t) ≥ log 3 ≥ 1 (since 3 ≥ exp 1).
  have h_log_t_eq : Real.log t = Real.log (-t) := by
    conv_lhs => rw [show t = -(-t) from by ring]
    rw [Real.log_neg_eq_log]
  have h_exp_1_lt_3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9; linarith
  have h_log_3_ge_1 : Real.log 3 ≥ 1 := by
    have h : Real.log (Real.exp 1) ≤ Real.log 3 :=
      Real.log_le_log (Real.exp_pos 1) (le_of_lt h_exp_1_lt_3)
    rw [Real.log_exp] at h; exact h
  have h_log_neg_t_ge_1 : Real.log (-t) ≥ 1 := by
    have h : Real.log 3 ≤ Real.log (-t) :=
      Real.log_le_log (by norm_num : (0:ℝ) < 3) h_neg_t_ge_3
    linarith
  have h_log_t_ge_1 : Real.log t ≥ 1 := by rw [h_log_t_eq]; exact h_log_neg_t_ge_1
  -- Q = exp t - log t ≤ 1 - 1 = 0.
  have h_Q_le_0 : Real.exp t - Real.log t ≤ 0 := by linarith
  -- exp Q ≤ 1.
  have h_exp_Q_le_1 : Real.exp (Real.exp t - Real.log t) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr h_Q_le_0
  have h_exp_Q_pos : Real.exp (Real.exp t - Real.log t) > 0 := Real.exp_pos _
  -- |inner_arg| ≤ 1 + |t|.
  have h_inner_abs_le :
      |Real.exp (Real.exp t - Real.log t) - Real.log (S t)| ≤ 1 + |t| := by
    calc |Real.exp (Real.exp t - Real.log t) - Real.log (S t)|
        ≤ |Real.exp (Real.exp t - Real.log t)| + |Real.log (S t)| := abs_sub _ _
      _ = Real.exp (Real.exp t - Real.log t) + |Real.log (S t)| := by
          rw [abs_of_pos h_exp_Q_pos]
      _ ≤ 1 + |t| := by linarith
  -- log(1 + |t|) ≤ |t| (via log y ≤ y - 1).
  have h_sum_pos : (0 : ℝ) < 1 + |t| := by have := abs_nonneg t; linarith
  have h_log_sum_le : Real.log (1 + |t|) ≤ |t| := by
    have := Real.log_le_sub_one_of_pos h_sum_pos; linarith
  -- Real.log(inner_arg) ≤ Real.log|inner_arg| ≤ log(1+|t|) ≤ |t|.
  have h_log_inner_le :
      Real.log (Real.exp (Real.exp t - Real.log t) - Real.log (S t)) ≤ |t| := by
    have h_log_eq_abs :
        Real.log (Real.exp (Real.exp t - Real.log t) - Real.log (S t)) =
        Real.log |Real.exp (Real.exp t - Real.log t) - Real.log (S t)| :=
      (Real.log_abs _).symm
    rw [h_log_eq_abs]
    by_cases h_inner_zero :
        Real.exp (Real.exp t - Real.log t) - Real.log (S t) = 0
    · rw [h_inner_zero, abs_zero, Real.log_zero]
      have := abs_nonneg t; linarith
    · have h_abs_pos :
          |Real.exp (Real.exp t - Real.log t) - Real.log (S t)| > 0 :=
        abs_pos.mpr h_inner_zero
      have h_log_le := Real.log_le_log h_abs_pos h_inner_abs_le
      linarith
  -- Conclude: log(inner) + 2t ≤ |t| + 2t = -t + 2t = t ≤ -3 ≤ -1.
  linarith

-- **Helper (same-var triple-log witness, parked block below).** See researcher
-- dispatch 2026-05-12T19:30 and 20:25 derivations. Live bound theorem above;
-- block-comment below preserves the earlier (failed) inline-cascade attempt.
/-
private theorem log_triple_nest_same_var_witness (K : ℝ) :
    Real.log (Real.exp K - Real.log (Real.exp
      (-Real.exp (Real.exp (Real.exp (|K| + 100)))) - Real.log
      (-Real.exp (Real.exp (Real.exp (|K| + 100)))))) +
      (-Real.exp (Real.exp (Real.exp (|K| + 100)))) ≤ -1 := by
  -- (proof attempt - reverted due to rcases/log_neg_eq_log friction)
  -- M := exp(|K| + 100), T := exp M, t := -exp T.
  have h_absK_nn : (0 : ℝ) ≤ |K| := abs_nonneg K
  have h_M_pos : Real.exp (|K| + 100) > 0 := Real.exp_pos _
  have h_T_pos : Real.exp (Real.exp (|K| + 100)) > 0 := Real.exp_pos _
  have h_t_neg : -Real.exp (Real.exp (Real.exp (|K| + 100))) < 0 := by
    have := Real.exp_pos (Real.exp (Real.exp (|K| + 100))); linarith
  -- Layer 1: log t = exp(exp(|K|+100)).
  have h_logt :
      Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))) =
      Real.exp (Real.exp (|K| + 100)) := by
    rw [Real.log_neg_eq_log, Real.log_exp]
  -- Layer 2: exp t ≤ 1. exp t - log t = exp(-T) - T < -T + 1 ≤ 0 for T ≥ 1.
  have h_exp_t_le_one :
      Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr; linarith
  have h_exp_t_pos :
      Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) > 0 := Real.exp_pos _
  have h_M_ge_100 : Real.exp (|K| + 100) ≥ Real.exp 100 :=
    Real.exp_le_exp.mpr (by linarith)
  have h_exp_100_ge_2 : Real.exp 100 ≥ 2 := by
    have h := Real.add_one_le_exp (100 : ℝ); linarith
  have h_M_ge_2 : Real.exp (|K| + 100) ≥ 2 := by linarith
  have h_T_ge_M_plus_1 :
      Real.exp (Real.exp (|K| + 100)) ≥ Real.exp (|K| + 100) + 1 :=
    Real.add_one_le_exp _
  have h_T_ge_3 : Real.exp (Real.exp (|K| + 100)) ≥ 3 := by linarith
  -- Layer 2 continued: exp t - log t ≤ 1 - T < -2 (since T ≥ 3). So < 0.
  have h_inner_neg :
      Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
      Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))) < 0 := by
    rw [h_logt]; linarith
  -- |inner| ≤ T (since exp t ∈ (0, 1] and log t = T).
  -- exp t - T ∈ (-T, 1 - T] ⊂ (-T, 0). |exp t - T| ∈ [T - 1, T).
  have h_inner_abs_le :
      Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
      Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) ≤
      Real.exp (Real.exp (|K| + 100)) := by
    rw [h_logt]; linarith
  have h_inner_abs_ge :
      Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
      Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) ≥
      Real.exp (Real.exp (|K| + 100)) - 1 := by
    rw [h_logt]; linarith
  -- log of the absolute value:
  have h_abs_eq :
      |Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
       Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100))))| =
      Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
      Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) := by
    rw [abs_of_neg h_inner_neg]; ring
  have h_log_inner_le :
      Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100))))) ≤
      Real.exp (Real.exp (|K| + 100)) := by
    have h_log_eq :
        Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                  Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100))))) =
        Real.log (Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                  Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100))))) := by
      have h : Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
               Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))) =
               -(Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                 Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100))))) := by ring
      rw [h, Real.log_neg_eq_log]
    rw [h_log_eq]
    have h_pos :
        Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
        Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) > 0 := by
      rw [h_logt]; linarith
    have h_le := Real.log_le_log h_pos h_inner_abs_le
    have h_log_T_le_T :
        Real.log (Real.exp (Real.exp (|K| + 100))) ≤ Real.exp (Real.exp (|K| + 100)) := by
      rw [Real.log_exp]; linarith
    linarith
  -- Bound on |exp K - log(exp t - log t)|.
  have h_exp_K_le_T : Real.exp K ≤ Real.exp (Real.exp (|K| + 100)) := by
    have h_K_le_absK : K ≤ |K| := le_abs_self K
    have h_K_le_M : K ≤ Real.exp (|K| + 100) := by
      have h := Real.add_one_le_exp (|K| + 100); linarith
    exact Real.exp_le_exp.mpr h_K_le_M
  have h_log_inner_ge :
      Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100))))) ≥ 0 := by
    have h_log_eq :
        Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                  Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100))))) =
        Real.log (Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                  Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100))))) := by
      have h : Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
               Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))) =
               -(Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                 Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100))))) := by ring
      rw [h, Real.log_neg_eq_log]
    rw [h_log_eq]
    apply Real.log_nonneg
    rw [h_logt]; linarith
  -- exp K - log|...| ≤ exp K ≤ T. log_inner ≥ 0, so |exp K - log_inner| ≤ exp K + log_inner.
  have h_outer_arg_le :
      Real.exp K - Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                             Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100))))) ≤
      Real.exp K := by linarith
  have h_outer_arg_ge :
      Real.exp K - Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                             Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100))))) ≥
      Real.exp K - Real.exp (Real.exp (|K| + 100)) := by linarith
  -- The outer arg may be negative. Bound |outer arg| ≤ exp K + log_inner ≤ T + T = 2T.
  have h_outer_arg_abs :
      |Real.exp K - Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                              Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))))| ≤
      2 * Real.exp (Real.exp (|K| + 100)) := by
    calc |Real.exp K - Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                                 Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))))|
        ≤ |Real.exp K| + |Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                                    Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))))| :=
          abs_sub _ _
      _ = Real.exp K +
          Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                    Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100))))) := by
          rw [abs_of_pos (Real.exp_pos K), abs_of_nonneg h_log_inner_ge]
      _ ≤ Real.exp (Real.exp (|K| + 100)) + Real.exp (Real.exp (|K| + 100)) := by linarith
      _ = 2 * Real.exp (Real.exp (|K| + 100)) := by ring
  -- log of outer arg.
  have h_outer_log_le :
      Real.log (Real.exp K -
                Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                          Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))))) ≤
      Real.log (2 * Real.exp (Real.exp (|K| + 100))) := by
    by_cases h_zero : Real.exp K -
                      Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                                Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100))))) = 0
    · rw [h_zero, Real.log_zero]
      have h_pos : (0 : ℝ) < 2 * Real.exp (Real.exp (|K| + 100)) := by linarith
      exact Real.log_nonneg (by linarith)
    · have h_abs_pos :
          0 < |Real.exp K -
              Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                        Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))))| :=
        abs_pos.mpr h_zero
      have h_log_le_log_abs :
          Real.log (Real.exp K -
                    Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                              Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))))) ≤
          Real.log |Real.exp K -
                    Real.log (Real.exp (-Real.exp (Real.exp (Real.exp (|K| + 100)))) -
                              Real.log (-Real.exp (Real.exp (Real.exp (|K| + 100)))))| := by
        rcases lt_or_gt_of_ne h_zero with h | h
        · rw [abs_of_neg h, Real.log_neg_eq_log]
        · rw [abs_of_pos h]
      have h_log_abs_le := Real.log_le_log h_abs_pos h_outer_arg_abs
      linarith
  -- log(2T) = log 2 + M.
  have h_log_2T :
      Real.log (2 * Real.exp (Real.exp (|K| + 100))) =
      Real.log 2 + Real.exp (|K| + 100) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt h_T_pos)]
    rw [Real.log_exp]
  -- Final: LHS ≤ log 2 + M - T. Want ≤ -1.
  -- T ≥ exp(M) ≥ M + 1 (add_one_le_exp). So M - T ≤ -1. LHS ≤ log 2 - 1 ≈ -0.31. Not enough.
  -- Need T ≥ M + log 2 + 2. Use: T = exp M ≥ exp 100 ≥ 2 + M + log 2 for M ≥ 100... wait M = exp(|K|+100), can be small if... no M ≥ exp 100 ≈ 10^43 always (since |K|+100 ≥ 100). So T - M ≥ ... a lot.
  -- Specifically: T = exp M. For M ≥ 1: T ≥ exp 1 · exp(M-1) = e · exp(M-1) ≥ e · (M-1+1) = e·M ≥ 2.7 M. So T ≥ 2.7 M, hence T - M ≥ 1.7 M ≥ 1.7 (for M ≥ 1).
  -- Even simpler: T = exp M ≥ exp 100 (since M ≥ 100... wait |K|+100 ≥ 100 so M = exp(|K|+100) ≥ exp 100, but T = exp M ≥ exp(exp 100) astronomical).
  have h_T_huge :
      Real.exp (Real.exp (|K| + 100)) ≥ Real.exp (|K| + 100) + Real.log 2 + 2 := by
    -- T ≥ M + 1 (add_one_le_exp). But we need T ≥ M + log 2 + 2 ≈ M + 2.69.
    -- For M ≥ 2: exp M ≥ exp 2 · exp(M-2) ≥ exp 2 · (M - 2 + 1) = exp 2 · (M - 1).
    -- We have exp 2 > 4 (from h_exp_100_ge_2 indirectly... actually need separate fact).
    have h_exp_2_gt_4 : Real.exp 2 > 4 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      have := Real.exp_one_gt_two; nlinarith
    -- exp M ≥ exp 2 · exp(M-2) ≥ 4 (M-1) = 4M - 4.
    -- 4M - 4 - M = 3M - 4. For M ≥ 2: 3M - 4 ≥ 2. So exp M - M ≥ 2 ≥ log 2 + 2 - 0 → need 2 ≥ log 2 + 2 ⇒ 0 ≥ log 2 ✗ (log 2 ≈ 0.69).
    -- Need 3M - 4 ≥ log 2 + 2 ⇒ 3M ≥ log 2 + 6 ≈ 6.69 ⇒ M ≥ 2.23. We have M ≥ exp 100 huge.
    -- Specifically for M ≥ exp 100 ≥ 2.7: 3 · 2.7 - 4 = 4.1 ≥ 2.69 = log 2 + 2. ✓
    have h_M_minus_2_ge : Real.exp (|K| + 100) - 2 ≥ Real.exp 100 - 2 := by linarith
    have h_exp_M_minus_2_ge_M_minus_1 :
        Real.exp (Real.exp (|K| + 100) - 2) ≥ Real.exp (|K| + 100) - 1 := by
      have := Real.add_one_le_exp (Real.exp (|K| + 100) - 2); linarith
    have h_expand : Real.exp (Real.exp (|K| + 100)) =
                    Real.exp 2 * Real.exp (Real.exp (|K| + 100) - 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h_expand]
    have h_log2_lt_one : Real.log 2 < 1 := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
      exact Real.log_lt_log (by norm_num) Real.exp_one_gt_two
    have : Real.exp 2 * Real.exp (Real.exp (|K| + 100) - 2) ≥
           4 * (Real.exp (|K| + 100) - 1) := by
      have h1 : Real.exp (Real.exp (|K| + 100) - 2) ≥ Real.exp (|K| + 100) - 1 :=
        h_exp_M_minus_2_ge_M_minus_1
      have h2 : Real.exp (Real.exp (|K| + 100) - 2) > 0 := Real.exp_pos _
      have h3 : (0 : ℝ) < 4 := by norm_num
      nlinarith
    linarith
  -- Combine.
  linarith
-/

/-- **Exp-growth lemma.** If `T = .app .eml kids` globally represents
`(v ↦ v 0 + v 1)`, then at every `v` where `(kids 1).eval v > 0`,
`(kids 1).eval v ≥ Real.exp (-(v 0 + v 1))`.

Proof: from the global equation `T.eval v = v 0 + v 1`, expand:
- `Real.exp(A) - Real.log(B) = v 0 + v 1` (where `A = (kids 0).eval v`,
  `B = (kids 1).eval v`).
- For `B > 0`: `Real.log B = Real.exp A - (v 0 + v 1)`.
- So `B = Real.exp(Real.exp A - (v 0 + v 1))`.
- `Real.exp A ≥ 0` (always), so `Real.exp A - (v 0 + v 1) ≥ -(v 0 + v 1)`.
- `Real.exp` is monotonic, giving `B ≥ Real.exp(-(v 0 + v 1))`. ∎ -/
theorem B_exp_growth_lower_bound
    (kids : Fin (EmlBasis.arity EmlOp.eml) → MinimalBasis.Term EmlBasis 2)
    (hr : (MinimalBasis.Term.app (B := EmlBasis) EmlOp.eml kids).representsGlobally
            (fun v : Fin 2 → ℝ => v 0 + v 1))
    (v : Fin 2 → ℝ)
    (hk1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml)
    (h_B_pos : (kids ⟨1, hk1_lt⟩).eval v > 0) :
    (kids ⟨1, hk1_lt⟩).eval v ≥ Real.exp (-(v 0 + v 1)) := by
  have hk0_lt : (0 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
  -- T.eval v = exp(A) - log(B) = v 0 + v 1
  have h_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
              Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 := hr v
  -- log B = exp(A) - (v 0 + v 1)
  have h_logB : Real.log ((kids ⟨1, hk1_lt⟩).eval v) =
                Real.exp ((kids ⟨0, hk0_lt⟩).eval v) - (v 0 + v 1) := by
    linarith
  -- B = exp(log B) (since B > 0)
  have h_B_eq : (kids ⟨1, hk1_lt⟩).eval v =
                Real.exp (Real.exp ((kids ⟨0, hk0_lt⟩).eval v) - (v 0 + v 1)) := by
    rw [← h_logB, Real.exp_log h_B_pos]
  -- exp(A) ≥ 0 ⟹ exp(A) - (v 0 + v 1) ≥ -(v 0 + v 1)
  have h_arg_lb : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) - (v 0 + v 1) ≥
                  -(v 0 + v 1) := by
    have := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
    linarith
  -- exp is monotonic
  rw [h_B_eq]
  exact Real.exp_le_exp.mpr h_arg_lb

/-- **Exp-growth lemma — slice specialization.** Restricting the exp-growth
lemma to `v = (-t, 0)` for `t > 0` gives the cleaner one-parameter statement:
`B(-t, 0) ≥ Real.exp t`. -/
theorem B_exp_growth_at_neg_slice
    (kids : Fin (EmlBasis.arity EmlOp.eml) → MinimalBasis.Term EmlBasis 2)
    (hr : (MinimalBasis.Term.app (B := EmlBasis) EmlOp.eml kids).representsGlobally
            (fun v : Fin 2 → ℝ => v 0 + v 1))
    (t : ℝ) (ht : t > 0)
    (hk1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml)
    (h_B_pos : (kids ⟨1, hk1_lt⟩).eval
                 (fun i : Fin 2 => if i = 0 then -t else 0) > 0) :
    (kids ⟨1, hk1_lt⟩).eval
        (fun i : Fin 2 => if i = 0 then -t else 0) ≥ Real.exp t := by
  have h := B_exp_growth_lower_bound kids hr
    (fun i : Fin 2 => if i = 0 then -t else 0) hk1_lt h_B_pos
  -- The slice has v 0 = -t, v 1 = 0, so -(v 0 + v 1) = -(-t + 0) = t.
  have h_slice : -(((fun i : Fin 2 => if i = 0 then (-t : ℝ) else 0) 0) +
                  ((fun i : Fin 2 => if i = 0 then (-t : ℝ) else 0) 1)) = t := by
    simp
  rw [h_slice] at h
  exact h

set_option maxHeartbeats 2000000 in
/-- **H1.EML.depth_ge_four** (skeleton; full case-enumeration formalization
pending). `(x, y) ↦ x + y` requires EML depth ≥ 4.

Argument structure (math-prose proof in
`shared/eml/notes-depth-lower-bound.md`):
1. By H1, depth ≥ 3.
2. Suppose depth = 3. Then T = `.app .eml kids` with `kids 0`, `kids 1` of
   depth ≤ 2.
3. By the exp-growth lemma (above), `(kids 1).eval (-t, 0) ≥ exp t` for all
   `t > 0` (assuming `kids 1`'s eval stays positive on the slice).
4. **Case enumeration:** no depth-≤2 EML expression `B` satisfies
   `B(-t, 0) ≥ exp t` for all large `t` (asymptotic comparison fails for
   each form).
5. Contradiction with step 3 ⟹ depth ≥ 4.

Step 4 is the substantial analytic content (~250-300 lines of case-by-case
growth-bound proofs). -/
theorem depth_global_xy_ge_four :
    ¬ ∃ (T : MinimalBasis.Term EmlBasis 2), T.depth ≤ 3 ∧
        T.representsGlobally (fun v : Fin 2 → ℝ => v 0 + v 1) := by
  rintro ⟨T, hd, hr⟩
  -- Top-level case split on T.
  match T, hd, hr with
  | .const c, _, hr =>
    have h0 := hr (fun _ : Fin 2 => (0 : ℝ))
    have h1 := hr (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
    simp [MinimalBasis.Term.eval] at h0 h1
    linarith
  | .var ⟨0, _⟩, _, hr =>
    have h := hr (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1)
    simp [MinimalBasis.Term.eval] at h
  | .var ⟨1, _⟩, _, hr =>
    have h := hr (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
    simp [MinimalBasis.Term.eval] at h
  | .var ⟨_ + 2, hi⟩, _, _ => exact absurd hi (by omega)
  | .app .eml kids, hd, hr =>
    -- T = .app .eml kids. Use exp-growth at v = (-t, 0) for large t.
    have hk0_lt : (0 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
    have hk1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
    -- Case-split on kids 1's shape (the "B" in the math-prose).
    cases h_k1 : (kids ⟨1, hk1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
    | const c =>
      -- B = const c. T.eval v = exp((kids 0).eval v) - log c = v 0 + v 1.
      -- Pick v = (-(|log c| + 1), 0). Then v 0 + v 1 = -(|log c| + 1).
      -- exp((kids 0).eval v) = -(|log c| + 1) + log c ≤ -1 < 0. Contra exp_pos.
      let v : Fin 2 → ℝ := fun i => if i = 0 then -(|Real.log c| + 1) else 0
      have h_eq := hr v
      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
      rw [h_k1] at h_eq
      simp only [MinimalBasis.Term.eval] at h_eq
      -- h_eq: exp((kids 0).eval v) - log c = -(|log c| + 1)
      -- Show v 0 + v 1 = -(|log c| + 1).
      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log c| + 1) := by
        simp [v]
      rw [h_sum] at h_eq
      have h_exp_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                      -(|Real.log c| + 1) + Real.log c := by linarith
      -- RHS ≤ -1: -(|x| + 1) + x = x - |x| - 1 ≤ -1 (since x ≤ |x|).
      have h_RHS_le : -(|Real.log c| + 1) + Real.log c ≤ -1 :=
        by linarith [le_abs_self (Real.log c)]
      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
      linarith
    | var i =>
      -- B = .var i. T.eval v = exp((kids 0).eval v) - log(v i) = v 0 + v 1.
      -- At v = (-1, 0): log(v i) = 0 (both i=0 gives log(-1)=0, i=1 gives log(0)=0).
      -- exp = -1 + 0 = -1. Contra exp_pos.
      let v : Fin 2 → ℝ := fun i => if i = 0 then (-1 : ℝ) else 0
      have h_eq := hr v
      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
      rw [h_k1] at h_eq
      simp only [MinimalBasis.Term.eval] at h_eq
      have h_log_zero : Real.log (v i) = 0 := by
        rcases i with ⟨_ | _ | _, hi⟩
        · -- i = 0: v 0 = -1. log(-1) = log 1 = 0.
          show Real.log (v ⟨0, hi⟩) = 0
          have : v ⟨0, hi⟩ = -1 := by simp [v]
          rw [this, show (-1 : ℝ) = -(1 : ℝ) by ring, Real.log_neg_eq_log,
              Real.log_one]
        · -- i = 1: v 1 = 0. log 0 = 0.
          show Real.log (v ⟨0 + 1, hi⟩) = 0
          have : v ⟨0 + 1, hi⟩ = 0 := by simp [v]
          rw [this, Real.log_zero]
        · exact absurd hi (by omega)
      rw [h_log_zero, sub_zero] at h_eq
      have h_sum : (v 0 + v 1 : ℝ) = -1 := by simp [v]
      rw [h_sum] at h_eq
      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
      linarith
    | app _ kids' =>
      -- B = .app op kids' with kids' of depth ≤ 1. (op = .eml since EmlOp
      -- has only one constructor.) Case enumeration over kids' 0, kids' 1.
      have hk1'0_lt : (0 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
      have hk1'1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
      cases h_k1'0 : (kids' ⟨0, hk1'0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
      | const a =>
        cases h_k1'1 : (kids' ⟨1, hk1'1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
        | const c' =>
          -- Case 1: kids 1 = eml(.const a, .const c'). (kids 1).eval v = exp a - log c'
          -- (constant). Pick v 0 + v 1 = -(|log K| + 1) for K = exp a - log c'.
          -- Equation gives exp((kids 0).eval v) ≤ -1. Contradicts exp_pos.
          let K : ℝ := Real.exp a - Real.log c'
          let v : Fin 2 → ℝ := fun i => if i = 0 then -(|Real.log K| + 1) else 0
          have h_eq := hr v
          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                 Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
          rw [h_k1] at h_eq
          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                 Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                           Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                 v 0 + v 1 at h_eq
          rw [h_k1'0, h_k1'1] at h_eq
          simp only [MinimalBasis.Term.eval] at h_eq
          have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
          rw [h_sum] at h_eq
          have h_exp_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                          -(|Real.log K| + 1) + Real.log K := by
            show Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
              -(|Real.log K| + 1) + Real.log (Real.exp a - Real.log c')
            linarith
          have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
            by linarith [le_abs_self (Real.log K)]
          have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
          linarith
        | var k =>
          -- Case 2: kids 1 = eml(.const a, .var k).
          -- Pick v such that v k = 0 (so log(v k) = 0) and v 0 + v 1 = -(|a|+1).
          -- Then (kids 1).eval v = exp a - 0 = exp a. log(exp a) = a.
          -- Equation: exp((kids 0).eval v) - a = -(|a|+1). exp = a - |a| - 1 ≤ -1. Contra.
          rcases k with ⟨_ | _ | _, hk⟩
          · -- k = 0: v = (0, -(|a|+1)). v 0 = 0, log 0 = 0.
            let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else -(|a| + 1)
            have h_eq := hr v
            change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                   Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
            rw [h_k1] at h_eq
            change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                   Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                             Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                   v 0 + v 1 at h_eq
            rw [h_k1'0, h_k1'1] at h_eq
            simp only [MinimalBasis.Term.eval] at h_eq
            -- h_eq: exp((kids 0).eval v) - log(exp a - log(v 0)) = v 0 + v 1
            -- = exp(...) - log(exp a - log 0) = exp(...) - log(exp a) = exp(...) - a
            have h_v0 : v ⟨0, hk⟩ = 0 := by simp [v]
            have h_log_v0 : Real.log (v ⟨0, hk⟩) = 0 := by rw [h_v0, Real.log_zero]
            rw [h_log_v0, sub_zero, Real.log_exp] at h_eq
            have h_sum : (v 0 + v 1 : ℝ) = -(|a| + 1) := by simp [v]
            rw [h_sum] at h_eq
            have h_exp_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) = a - (|a| + 1) :=
              by linarith
            have h_RHS_le : a - (|a| + 1) ≤ -1 := by
              linarith [le_abs_self a]
            have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
            linarith
          · -- k = 1: v = (-(|a|+1), 0). v 1 = 0, log 0 = 0.
            let v : Fin 2 → ℝ := fun i => if i = 0 then -(|a| + 1) else 0
            have h_eq := hr v
            change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                   Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
            rw [h_k1] at h_eq
            change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                   Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                             Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                   v 0 + v 1 at h_eq
            rw [h_k1'0, h_k1'1] at h_eq
            simp only [MinimalBasis.Term.eval] at h_eq
            have h_v1 : v ⟨0 + 1, hk⟩ = 0 := by simp [v]
            have h_log_v1 : Real.log (v ⟨0 + 1, hk⟩) = 0 := by
              rw [h_v1, Real.log_zero]
            rw [h_log_v1, sub_zero, Real.log_exp] at h_eq
            have h_sum : (v 0 + v 1 : ℝ) = -(|a| + 1) := by simp [v]
            rw [h_sum] at h_eq
            have h_exp_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) = a - (|a| + 1) :=
              by linarith
            have h_RHS_le : a - (|a| + 1) ≤ -1 := by
              linarith [le_abs_self a]
            have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
            linarith
          · exact absurd hk (by omega)
        | app _ kids'' =>
          -- kids' 0 = .const a, kids' 1 = .app op'' kids''. kids'' children are leaves.
          have hk1''0_lt : (0 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
          have hk1''1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
          cases h_k1''0 : (kids'' ⟨0, hk1''0_lt⟩ :
              MinimalBasis.Term EmlBasis 2) with
          | const c0 =>
            cases h_k1''1 : (kids'' ⟨1, hk1''1_lt⟩ :
                MinimalBasis.Term EmlBasis 2) with
            | const c1 =>
              -- Sub-case: kids 1 = .app[.const a, .app[.const c0, .const c1]].
              -- (kids 1).eval v = exp a - log(exp c0 - log c1). Constant K.
              -- Pick v 0 + v 1 = -(|log K| + 1). Same as Case 1 with deeper K.
              let K : ℝ := Real.exp a - Real.log (Real.exp c0 - Real.log c1)
              let v : Fin 2 → ℝ := fun i => if i = 0 then -(|Real.log K| + 1) else 0
              have h_eq := hr v
              change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                     Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
              rw [h_k1] at h_eq
              change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                     Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                               Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                     v 0 + v 1 at h_eq
              rw [h_k1'0, h_k1'1] at h_eq
              change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                     Real.log (Real.exp a -
                               Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                         Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                     v 0 + v 1 at h_eq
              rw [h_k1''0, h_k1''1] at h_eq
              simp only [MinimalBasis.Term.eval] at h_eq
              have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
              rw [h_sum] at h_eq
              have h_exp_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                              -(|Real.log K| + 1) + Real.log K := by
                show Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                  -(|Real.log K| + 1) +
                    Real.log (Real.exp a - Real.log (Real.exp c0 - Real.log c1))
                linarith
              have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
                by linarith [le_abs_self (Real.log K)]
              have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
              linarith
            | var l =>
              -- Sub-case: kids 1 = .app[.const a, .app[.const c0, .var l]].
              -- Pick v with v l = 0. (kids' 1).eval = exp c0 - 0 = exp c0.
              -- (kids 1).eval = exp a - log(exp c0) = exp a - c0. K = exp a - c0.
              let K : ℝ := Real.exp a - c0
              rcases l with ⟨_ | _ | _, hl⟩
              · -- l = 0: v = (0, -(|log K| + 1)).
                let v : Fin 2 → ℝ := fun i =>
                  if i = 0 then 0 else -(|Real.log K| + 1)
                have h_eq := hr v
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                rw [h_k1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                 Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                       v 0 + v 1 at h_eq
                rw [h_k1'0, h_k1'1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp a -
                                 Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                           Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                       v 0 + v 1 at h_eq
                rw [h_k1''0, h_k1''1] at h_eq
                simp only [MinimalBasis.Term.eval] at h_eq
                have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                rw [h_vl, Real.log_zero, sub_zero, Real.log_exp] at h_eq
                have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
                rw [h_sum] at h_eq
                have h_exp_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                                -(|Real.log K| + 1) + Real.log K := by
                  show Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                    -(|Real.log K| + 1) + Real.log (Real.exp a - c0)
                  linarith
                have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
                  by linarith [le_abs_self (Real.log K)]
                have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                linarith
              · -- l = 1: v = (-(|log K| + 1), 0).
                let v : Fin 2 → ℝ := fun i =>
                  if i = 0 then -(|Real.log K| + 1) else 0
                have h_eq := hr v
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                rw [h_k1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                 Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                       v 0 + v 1 at h_eq
                rw [h_k1'0, h_k1'1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp a -
                                 Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                           Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                       v 0 + v 1 at h_eq
                rw [h_k1''0, h_k1''1] at h_eq
                simp only [MinimalBasis.Term.eval] at h_eq
                have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                rw [h_vl, Real.log_zero, sub_zero, Real.log_exp] at h_eq
                have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
                rw [h_sum] at h_eq
                have h_exp_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                                -(|Real.log K| + 1) + Real.log K := by
                  show Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                    -(|Real.log K| + 1) + Real.log (Real.exp a - c0)
                  linarith
                have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
                  by linarith [le_abs_self (Real.log K)]
                have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                linarith
              · exact absurd hl (by omega)
            | app op''' kids''' =>
              -- 4-level depth contradiction
              exfalso
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids i).depth) ≤ 3 at hd
              have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids i).depth) :=
                  Finset.le_sup (f := fun i => (kids i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1] at h1
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids' i).depth) ≤ 2 at h1
              have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids' i).depth) :=
                  Finset.le_sup (f := fun i => (kids' i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1'1] at h2
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids'' i).depth) ≤ 1 at h2
              have h3 : (kids'' ⟨1, hk1''1_lt⟩).depth ≤ 0 := by
                have hle : (kids'' ⟨1, hk1''1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids'' i).depth) :=
                  Finset.le_sup (f := fun i => (kids'' i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1''1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1''1] at h3
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity op'''))).sup
                         (fun i => (kids''' i).depth) ≤ 0 at h3
              omega
          | var j =>
            cases h_k1''1 : (kids'' ⟨1, hk1''1_lt⟩ :
                MinimalBasis.Term EmlBasis 2) with
            | const c1 =>
              -- Sub-case: kids 1 = .app[.const a, .app[.var j, .const c1]].
              -- Pick v with v j = 0. (kids'' 0).eval v = 0. (kids' 1).eval = 1 - log c1.
              -- (kids 1).eval = exp a - log(1 - log c1). Constant K.
              let K : ℝ := Real.exp a - Real.log (1 - Real.log c1)
              rcases j with ⟨_ | _ | _, hj⟩
              · -- j = 0: v = (0, -(|log K| + 1)).
                let v : Fin 2 → ℝ := fun i =>
                  if i = 0 then 0 else -(|Real.log K| + 1)
                have h_eq := hr v
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                rw [h_k1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                 Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                       v 0 + v 1 at h_eq
                rw [h_k1'0, h_k1'1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp a -
                                 Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                           Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                       v 0 + v 1 at h_eq
                rw [h_k1''0, h_k1''1] at h_eq
                simp only [MinimalBasis.Term.eval] at h_eq
                have h_v0 : v ⟨0, hj⟩ = 0 := by simp [v]
                rw [h_v0, Real.exp_zero] at h_eq
                have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
                rw [h_sum] at h_eq
                have h_exp_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                                -(|Real.log K| + 1) + Real.log K := by
                  show Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                    -(|Real.log K| + 1) +
                      Real.log (Real.exp a - Real.log (1 - Real.log c1))
                  linarith
                have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
                  by linarith [le_abs_self (Real.log K)]
                have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                linarith
              · -- j = 1: v = (-(|log K| + 1), 0).
                let v : Fin 2 → ℝ := fun i =>
                  if i = 0 then -(|Real.log K| + 1) else 0
                have h_eq := hr v
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                rw [h_k1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                 Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                       v 0 + v 1 at h_eq
                rw [h_k1'0, h_k1'1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp a -
                                 Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                           Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                       v 0 + v 1 at h_eq
                rw [h_k1''0, h_k1''1] at h_eq
                simp only [MinimalBasis.Term.eval] at h_eq
                have h_v1 : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                rw [h_v1, Real.exp_zero] at h_eq
                have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
                rw [h_sum] at h_eq
                have h_exp_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                                -(|Real.log K| + 1) + Real.log K := by
                  show Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                    -(|Real.log K| + 1) +
                      Real.log (Real.exp a - Real.log (1 - Real.log c1))
                  linarith
                have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
                  by linarith [le_abs_self (Real.log K)]
                have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                linarith
              · exact absurd hj (by omega)
            | var l =>
              -- Sub-case: kids 1 = .app[.const a, .app[.var j, .var l]].
              -- 4 sub-sub-cases on (j, l). Same-var (j=l) uses simple K-bound;
              -- cross-variable (j≠l) uses the |a|+2 helper.
              rcases j with ⟨_ | _ | _, hj⟩
              · -- j = 0
                rcases l with ⟨_ | _ | _, hl⟩
                · -- (j=0, l=0): same-var at index 0.
                  -- v = (0, -(|a|+1)). v j = v l = 0. (kids 1).eval = exp a.
                  let v : Fin 2 → ℝ := fun i =>
                    if i = 0 then 0 else -(|a| + 1)
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp a -
                                   Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                             Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_k1''0, h_k1''1] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                  rw [h_vj, Real.exp_zero, Real.log_zero, sub_zero,
                      Real.log_one, sub_zero, Real.log_exp] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|a| + 1) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith [le_abs_self a]
                · -- (j=0, l=1): cross-variable.
                  -- v = (-(|a|+2), 0). v j = v 0 = -(|a|+2). v l = v 1 = 0.
                  let v : Fin 2 → ℝ := fun i =>
                    if i = 0 then -(|a| + 2) else 0
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp a -
                                   Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                             Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_k1''0, h_k1''1] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vj : v ⟨0, hj⟩ = -(|a| + 2) := by simp [v]
                  have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                  rw [h_vj, h_vl, Real.log_zero, sub_zero, Real.log_exp] at h_eq
                  -- h_eq: exp((kids 0).eval v) - log(exp a - (-(|a|+2))) = -(|a|+2)
                  --     = exp(...) - log(exp a + (|a|+2)) = -(|a|+2)
                  have h_sum : (v 0 + v 1 : ℝ) = -(|a| + 2) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_log_bound : Real.log (Real.exp a + |a| + 2) ≤ |a| + 2 :=
                    log_exp_a_plus_abs_a_plus_two_le a
                  have h_exp_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                                  -(|a| + 2) + Real.log (Real.exp a - -(|a| + 2)) := by
                    linarith
                  have h_simplify : Real.exp a - -(|a| + 2) = Real.exp a + |a| + 2 :=
                    by ring
                  rw [h_simplify] at h_exp_eq
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · exact absurd hl (by omega)
              · -- j = 1
                rcases l with ⟨_ | _ | _, hl⟩
                · -- (j=1, l=0): cross-variable, symmetric.
                  -- v = (0, -(|a|+2)). v j = v 1 = -(|a|+2). v l = v 0 = 0.
                  let v : Fin 2 → ℝ := fun i =>
                    if i = 0 then 0 else -(|a| + 2)
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp a -
                                   Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                             Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_k1''0, h_k1''1] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vj : v ⟨0 + 1, hj⟩ = -(|a| + 2) := by simp [v]
                  have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                  rw [h_vj, h_vl, Real.log_zero, sub_zero, Real.log_exp] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|a| + 2) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_log_bound : Real.log (Real.exp a + |a| + 2) ≤ |a| + 2 :=
                    log_exp_a_plus_abs_a_plus_two_le a
                  have h_simplify : Real.exp a - -(|a| + 2) = Real.exp a + |a| + 2 :=
                    by ring
                  rw [h_simplify] at h_eq
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · -- (j=1, l=1): same-var at index 1.
                  -- v = (-(|a|+1), 0). v j = v l = 0. (kids 1).eval = exp a.
                  let v : Fin 2 → ℝ := fun i =>
                    if i = 0 then -(|a| + 1) else 0
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp a -
                                   Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                             Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_k1''0, h_k1''1] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                  rw [h_vj, Real.exp_zero, Real.log_zero, sub_zero,
                      Real.log_one, sub_zero, Real.log_exp] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|a| + 1) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith [le_abs_self a]
                · exact absurd hl (by omega)
              · exact absurd hj (by omega)
            | app op''' kids''' =>
              -- 4-level depth contradiction
              exfalso
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids i).depth) ≤ 3 at hd
              have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids i).depth) :=
                  Finset.le_sup (f := fun i => (kids i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1] at h1
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids' i).depth) ≤ 2 at h1
              have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids' i).depth) :=
                  Finset.le_sup (f := fun i => (kids' i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1'1] at h2
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids'' i).depth) ≤ 1 at h2
              have h3 : (kids'' ⟨1, hk1''1_lt⟩).depth ≤ 0 := by
                have hle : (kids'' ⟨1, hk1''1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids'' i).depth) :=
                  Finset.le_sup (f := fun i => (kids'' i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1''1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1''1] at h3
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity op'''))).sup
                         (fun i => (kids''' i).depth) ≤ 0 at h3
              omega
          | app op''' kids''' =>
            -- 4-level depth contradiction (kids'' 0 = .app)
            exfalso
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids i).depth) ≤ 3 at hd
            have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
              have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids i).depth) :=
                Finset.le_sup (f := fun i => (kids i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1] at h1
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids' i).depth) ≤ 2 at h1
            have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
              have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids' i).depth) :=
                Finset.le_sup (f := fun i => (kids' i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1'1] at h2
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids'' i).depth) ≤ 1 at h2
            have h3 : (kids'' ⟨0, hk1''0_lt⟩).depth ≤ 0 := by
              have hle : (kids'' ⟨0, hk1''0_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids'' i).depth) :=
                Finset.le_sup (f := fun i => (kids'' i).depth)
                  (Finset.mem_univ
                    (⟨0, hk1''0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1''0] at h3
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity op'''))).sup
                       (fun i => (kids''' i).depth) ≤ 0 at h3
            omega
      | var i =>
        cases h_k1'1 : (kids' ⟨1, hk1'1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
        | const c' =>
          -- Case 3: kids 1 = eml(.var i, .const c').
          -- Pick v with v i = 0 (so exp(v i) = 1) and v 0 + v 1 = -(|log K|+1)
          -- where K = 1 - log c'. Then (kids 1).eval v = K. log K consumed
          -- by the bound argument.
          let K : ℝ := 1 - Real.log c'
          rcases i with ⟨_ | _ | _, hi⟩
          · -- i = 0: v = (0, -(|log K|+1)).
            let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else -(|Real.log K| + 1)
            have h_eq := hr v
            change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                   Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
            rw [h_k1] at h_eq
            change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                   Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                             Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                   v 0 + v 1 at h_eq
            rw [h_k1'0, h_k1'1] at h_eq
            simp only [MinimalBasis.Term.eval] at h_eq
            have h_v0 : v ⟨0, hi⟩ = 0 := by simp [v]
            rw [h_v0, Real.exp_zero] at h_eq
            -- h_eq: exp((kids 0).eval v) - log(1 - log c') = v 0 + v 1
            have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
            rw [h_sum] at h_eq
            have h_exp_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                            -(|Real.log K| + 1) + Real.log K := by
              show Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                -(|Real.log K| + 1) + Real.log (1 - Real.log c')
              linarith
            have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
              by linarith [le_abs_self (Real.log K)]
            have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
            linarith
          · -- i = 1: v = (-(|log K|+1), 0).
            let v : Fin 2 → ℝ := fun i => if i = 0 then -(|Real.log K| + 1) else 0
            have h_eq := hr v
            change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                   Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
            rw [h_k1] at h_eq
            change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                   Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                             Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                   v 0 + v 1 at h_eq
            rw [h_k1'0, h_k1'1] at h_eq
            simp only [MinimalBasis.Term.eval] at h_eq
            have h_v1 : v ⟨0 + 1, hi⟩ = 0 := by simp [v]
            rw [h_v1, Real.exp_zero] at h_eq
            have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
            rw [h_sum] at h_eq
            have h_exp_eq : Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                            -(|Real.log K| + 1) + Real.log K := by
              show Real.exp ((kids ⟨0, hk0_lt⟩).eval v) =
                -(|Real.log K| + 1) + Real.log (1 - Real.log c')
              linarith
            have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
              by linarith [le_abs_self (Real.log K)]
            have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
            linarith
          · exact absurd hi (by omega)
        | var k =>
          -- Case 4: kids 1 = eml(.var i, .var k). At v = (0, 0):
          -- v i = 0, v k = 0. (kids 1).eval = exp 0 - log 0 = 1 - 0 = 1.
          -- log 1 = 0. Equation: exp((kids 0).eval (0,0)) = 0. Contra exp_pos.
          let v : Fin 2 → ℝ := fun _ => 0
          have h_eq := hr v
          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                 Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
          rw [h_k1] at h_eq
          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                 Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                           Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                 v 0 + v 1 at h_eq
          rw [h_k1'0, h_k1'1] at h_eq
          simp only [MinimalBasis.Term.eval] at h_eq
          have h_v_eq : ∀ a : Fin 2, v a = 0 := fun _ => rfl
          rw [h_v_eq i, Real.exp_zero, Real.log_zero, sub_zero,
              Real.log_one, sub_zero] at h_eq
          have h_sum : (v 0 + v 1 : ℝ) = 0 := by simp [v]
          rw [h_sum] at h_eq
          have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
          linarith
        | app _ kids'' =>
          -- kids' 0 = .var i, kids' 1 = .app op'' kids''.
          -- kids'' children are leaves (depth ≤ 0 from depth chain).
          have hk1''0_lt : (0 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
          have hk1''1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
          cases h_k1''0 : (kids'' ⟨0, hk1''0_lt⟩ :
              MinimalBasis.Term EmlBasis 2) with
          | const c0 =>
            -- Sub-tree: kids' 0 = var i, kids'' 0 = const c0.
            -- Case on kids'' 1: const, var (with sub-cases on i, l), or app (depth contra).
            cases h_k1''1' : (kids'' ⟨1, hk1''1_lt⟩ :
                MinimalBasis.Term EmlBasis 2) with
            | const c1 =>
              -- (kids' 1).eval v = exp c0 - log c1 = K1 (constant).
              -- (kids 1).eval v = exp(v i) - log K1.
              -- K-bound on K_outer = 1 - log K1.
              let K1 : ℝ := Real.exp c0 - Real.log c1
              let K_outer : ℝ := 1 - Real.log K1
              rcases i with ⟨_ | _ | _, hi⟩
              · -- i = 0: v = (0, -(|log K_outer|+1)).
                let v : Fin 2 → ℝ :=
                  fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                have h_eq := hr v
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                rw [h_k1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                 Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                       v 0 + v 1 at h_eq
                rw [h_k1'0, h_k1'1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp (v ⟨0, hi⟩) -
                                 Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                           Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                       v 0 + v 1 at h_eq
                rw [h_k1''0, h_k1''1'] at h_eq
                simp only [MinimalBasis.Term.eval] at h_eq
                have h_vi : v ⟨0, hi⟩ = 0 := by simp [v]
                rw [h_vi, Real.exp_zero] at h_eq
                have h_K1_unfold : Real.exp c0 - Real.log c1 = K1 := rfl
                rw [h_K1_unfold] at h_eq
                have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                rw [h_sum] at h_eq
                have h_outer_eq : (1 : ℝ) - Real.log K1 = K_outer := rfl
                rw [h_outer_eq] at h_eq
                have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                  by linarith [le_abs_self (Real.log K_outer)]
                have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                linarith
              · -- i = 1: v = (-(|log K_outer|+1), 0).
                let v : Fin 2 → ℝ :=
                  fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                have h_eq := hr v
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                rw [h_k1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                 Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                       v 0 + v 1 at h_eq
                rw [h_k1'0, h_k1'1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp (v ⟨0 + 1, hi⟩) -
                                 Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                           Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                       v 0 + v 1 at h_eq
                rw [h_k1''0, h_k1''1'] at h_eq
                simp only [MinimalBasis.Term.eval] at h_eq
                have h_vi : v ⟨0 + 1, hi⟩ = 0 := by simp [v]
                rw [h_vi, Real.exp_zero] at h_eq
                have h_K1_unfold : Real.exp c0 - Real.log c1 = K1 := rfl
                rw [h_K1_unfold] at h_eq
                have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                rw [h_sum] at h_eq
                have h_outer_eq : (1 : ℝ) - Real.log K1 = K_outer := rfl
                rw [h_outer_eq] at h_eq
                have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                  by linarith [le_abs_self (Real.log K_outer)]
                have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                linarith
              · exact absurd hi (by omega)
            | var l =>
              -- (kids' 1).eval v = exp c0 - log(v l).
              -- (kids 1).eval v = exp(v i) - log(exp c0 - log(v l)).
              -- Strategy: choose v_l = 1 so log(v_l) = 0, then (kids' 1).eval = exp c0.
              -- 4 sub-cases on (i, l).
              rcases i with ⟨_ | _ | _, hi⟩
              · rcases l with ⟨_ | _ | _, hl⟩
                · -- (i=0, l=0): same-var. v 0 = 1, v 1 = -(|log K|+2) where K = e - c0.
                  let K : ℝ := Real.exp 1 - c0
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then 1 else -(|Real.log K| + 2)
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (v ⟨0, hi⟩) -
                                   Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                             Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_k1''0, h_k1''1'] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vi : v ⟨0, hi⟩ = 1 := by simp [v]
                  rw [h_vi, Real.log_one, sub_zero] at h_eq
                  -- h_eq: exp((kids 0).eval v) - log(exp 1 - log(exp c0)) = v 0 + v 1
                  rw [Real.log_exp] at h_eq
                  have h_K_unfold : Real.exp 1 - c0 = K := rfl
                  rw [h_K_unfold] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -|Real.log K| - 1 := by simp [v]; ring
                  rw [h_sum] at h_eq
                  have h_RHS_le : -|Real.log K| - 1 + Real.log K ≤ -1 :=
                    by linarith [le_abs_self (Real.log K)]
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · -- (i=0, l=1): cross-var. v 0 = -(|c0|+2), v 1 = 1.
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then -(|c0| + 2) else 1
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (v ⟨0, hi⟩) -
                                   Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                             Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_k1''0, h_k1''1'] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vi : v ⟨0, hi⟩ = -(|c0| + 2) := by simp [v]
                  have h_vl : v ⟨0 + 1, hl⟩ = 1 := by simp [v]
                  rw [h_vi, h_vl, Real.log_one, sub_zero, Real.log_exp] at h_eq
                  -- h_eq: exp((kids 0).eval v) - log(exp(-(|c0|+2)) - c0) = v 0 + v 1
                  have h_sum : (v 0 + v 1 : ℝ) = -|c0| - 1 := by simp [v]; ring
                  rw [h_sum] at h_eq
                  have h_a_le_zero : -(|c0| + 2) ≤ (0 : ℝ) := by
                    have := abs_nonneg c0; linarith
                  have h_log_bound :
                      Real.log (Real.exp (-(|c0| + 2)) - c0) ≤ |c0| :=
                    log_exp_sub_le_abs _ _ h_a_le_zero
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · exact absurd hl (by omega)
              · rcases l with ⟨_ | _ | _, hl⟩
                · -- (i=1, l=0): cross-var. v 0 = 1, v 1 = -(|c0|+2).
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then 1 else -(|c0| + 2)
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (v ⟨0 + 1, hi⟩) -
                                   Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                             Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_k1''0, h_k1''1'] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vi : v ⟨0 + 1, hi⟩ = -(|c0| + 2) := by simp [v]
                  have h_vl : v ⟨0, hl⟩ = 1 := by simp [v]
                  rw [h_vi, h_vl, Real.log_one, sub_zero, Real.log_exp] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -|c0| - 1 := by simp [v]; ring
                  rw [h_sum] at h_eq
                  have h_a_le_zero : -(|c0| + 2) ≤ (0 : ℝ) := by
                    have := abs_nonneg c0; linarith
                  have h_log_bound :
                      Real.log (Real.exp (-(|c0| + 2)) - c0) ≤ |c0| :=
                    log_exp_sub_le_abs _ _ h_a_le_zero
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · -- (i=1, l=1): same-var at index 1. v 0 = -(|log K|+2), v 1 = 1.
                  let K : ℝ := Real.exp 1 - c0
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then -(|Real.log K| + 2) else 1
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (v ⟨0 + 1, hi⟩) -
                                   Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                             Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_k1''0, h_k1''1'] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vi : v ⟨0 + 1, hi⟩ = 1 := by simp [v]
                  rw [h_vi, Real.log_one, sub_zero, Real.log_exp] at h_eq
                  have h_K_unfold : Real.exp 1 - c0 = K := rfl
                  rw [h_K_unfold] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -|Real.log K| - 1 := by simp [v]; ring
                  rw [h_sum] at h_eq
                  have h_RHS_le : -|Real.log K| - 1 + Real.log K ≤ -1 :=
                    by linarith [le_abs_self (Real.log K)]
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · exact absurd hl (by omega)
              · exact absurd hi (by omega)
            | app op''' kids''' =>
              -- 4-level depth contradiction: kids'' 1 = .app forces depth ≥ 1, but
              -- depth chain gives kids'' i ≤ 0.
              exfalso
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids i).depth) ≤ 3 at hd
              have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids i).depth) :=
                  Finset.le_sup (f := fun i => (kids i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1] at h1
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids' i).depth) ≤ 2 at h1
              have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids' i).depth) :=
                  Finset.le_sup (f := fun i => (kids' i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1'1] at h2
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids'' i).depth) ≤ 1 at h2
              have h3 : (kids'' ⟨1, hk1''1_lt⟩).depth ≤ 0 := by
                have hle : (kids'' ⟨1, hk1''1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids'' i).depth) :=
                  Finset.le_sup (f := fun i => (kids'' i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1''1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1''1'] at h3
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity op'''))).sup
                         (fun i => (kids''' i).depth) ≤ 0 at h3
              omega
          | var j =>
            cases h_k1''1 : (kids'' ⟨1, hk1''1_lt⟩ :
                MinimalBasis.Term EmlBasis 2) with
            | const c1 =>
              -- Sub-sub-case: kids' 0 = var i, kids'' 0 = var j, kids'' 1 = const c1.
              -- (kids' 1).eval v = exp(v j) - log c1.
              -- (kids 1).eval v = exp(v i) - log(exp(v j) - log c1).
              -- Same-var (i=j): K-bound on K_outer = 1 - log(1 - log c1).
              -- Cross-var (i≠j): set v_j = 0, v_i = -(|log K1| + 1), use
              --   log_exp_sub_le_abs to bound log(exp(v_i) - log K1) ≤ |log K1|.
              let K1 : ℝ := 1 - Real.log c1
              let K_outer : ℝ := 1 - Real.log K1
              rcases i with ⟨_ | _ | _, hi⟩
              · -- i = 0
                rcases j with ⟨_ | _ | _, hj⟩
                · -- (i=0, j=0): same-var at index 0.
                  -- v = (0, -(|log K_outer|+1)).
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (v ⟨0, hi⟩) -
                                   Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                             Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_k1''0, h_k1''1] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vi : v ⟨0, hi⟩ = 0 := by simp [v]
                  rw [h_vi, Real.exp_zero] at h_eq
                  -- h_eq: exp((kids 0).eval v) - log(1 - log(1 - log c1)) = v 0 + v 1
                  have h_inner : Real.log (1 - Real.log c1) = Real.log K1 := by
                    show Real.log (1 - Real.log c1) = Real.log (1 - Real.log c1)
                    rfl
                  rw [h_inner] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                  rw [h_sum] at h_eq
                  -- exp((kids 0).eval v) - log K_outer = -(|log K_outer|+1)
                  have h_outer_eq : (1 : ℝ) - Real.log K1 = K_outer := rfl
                  rw [h_outer_eq] at h_eq
                  have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                    by linarith [le_abs_self (Real.log K_outer)]
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · -- (i=0, j=1): cross-variable.
                  -- v = (-(|log K1|+1), 0). v i = v 0 = -(|log K1|+1), v j = v 1 = 0.
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then -(|Real.log K1| + 1) else 0
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (v ⟨0, hi⟩) -
                                   Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                             Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_k1''0, h_k1''1] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vi : v ⟨0, hi⟩ = -(|Real.log K1| + 1) := by simp [v]
                  have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                  rw [h_vi, h_vj, Real.exp_zero] at h_eq
                  -- h_eq: exp((kids 0).eval v) - log(exp(-(|log K1|+1)) - log(1 - log c1))
                  --     = v 0 + v 1
                  have h_K1_unfold : (1 : ℝ) - Real.log c1 = K1 := rfl
                  rw [h_K1_unfold] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K1| + 1) := by simp [v]
                  rw [h_sum] at h_eq
                  -- Apply log_exp_sub_le_abs with a = -(|log K1|+1) ≤ 0, c = log K1.
                  have h_a_le_zero : -(|Real.log K1| + 1) ≤ (0 : ℝ) := by
                    have := abs_nonneg (Real.log K1); linarith
                  have h_log_bound :
                      Real.log (Real.exp (-(|Real.log K1| + 1)) - Real.log K1) ≤
                        |Real.log K1| :=
                    log_exp_sub_le_abs _ _ h_a_le_zero
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · exact absurd hj (by omega)
              · -- i = 1
                rcases j with ⟨_ | _ | _, hj⟩
                · -- (i=1, j=0): cross-variable.
                  -- v = (0, -(|log K1|+1)). v i = v 1 = -(|log K1|+1), v j = v 0 = 0.
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then 0 else -(|Real.log K1| + 1)
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (v ⟨0 + 1, hi⟩) -
                                   Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                             Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_k1''0, h_k1''1] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vi : v ⟨0 + 1, hi⟩ = -(|Real.log K1| + 1) := by simp [v]
                  have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                  rw [h_vi, h_vj, Real.exp_zero] at h_eq
                  have h_K1_unfold : (1 : ℝ) - Real.log c1 = K1 := rfl
                  rw [h_K1_unfold] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K1| + 1) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_a_le_zero : -(|Real.log K1| + 1) ≤ (0 : ℝ) := by
                    have := abs_nonneg (Real.log K1); linarith
                  have h_log_bound :
                      Real.log (Real.exp (-(|Real.log K1| + 1)) - Real.log K1) ≤
                        |Real.log K1| :=
                    log_exp_sub_le_abs _ _ h_a_le_zero
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · -- (i=1, j=1): same-var at index 1.
                  -- v = (-(|log K_outer|+1), 0).
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (v ⟨0 + 1, hi⟩) -
                                   Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                             Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_k1''0, h_k1''1] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vi : v ⟨0 + 1, hi⟩ = 0 := by simp [v]
                  rw [h_vi, Real.exp_zero] at h_eq
                  have h_inner : Real.log (1 - Real.log c1) = Real.log K1 := rfl
                  rw [h_inner] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_outer_eq : (1 : ℝ) - Real.log K1 = K_outer := rfl
                  rw [h_outer_eq] at h_eq
                  have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                    by linarith [le_abs_self (Real.log K_outer)]
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · exact absurd hj (by omega)
              · exact absurd hi (by omega)
            | var l =>
              -- Sub-sub-case B.4.var-var: all vars. v = (0, 0):
              -- (kids'' 0).eval = 0, (kids'' 1).eval = 0.
              -- (kids' 1).eval = exp 0 - log 0 = 1 - 0 = 1. log 1 = 0.
              -- (kids 1).eval = exp(v i) - 0 = exp 0 = 1. log 1 = 0.
              -- Equation: exp((kids 0).eval (0,0)) = 0. Contra exp_pos.
              let v : Fin 2 → ℝ := fun _ => 0
              have h_eq := hr v
              change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                     Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
              rw [h_k1] at h_eq
              change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                     Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                               Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                     v 0 + v 1 at h_eq
              rw [h_k1'0, h_k1'1] at h_eq
              change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                     Real.log (Real.exp (v i) -
                               Real.log (Real.exp ((kids'' ⟨0, hk1''0_lt⟩).eval v) -
                                         Real.log ((kids'' ⟨1, hk1''1_lt⟩).eval v))) =
                     v 0 + v 1 at h_eq
              rw [h_k1''0, h_k1''1] at h_eq
              simp only [MinimalBasis.Term.eval] at h_eq
              have h_v_eq : ∀ a : Fin 2, v a = 0 := fun _ => rfl
              simp only [h_v_eq, Real.exp_zero, Real.log_zero, sub_zero,
                         Real.log_one] at h_eq
              have h_sum : (v 0 + v 1 : ℝ) = 0 := by simp [v]
              rw [h_sum] at h_eq
              have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
              linarith
            | app op''' kids''' =>
              -- 4-level depth contradiction: T ≤ 3 → kids 1 ≤ 2 → kids' 1 ≤ 1 →
              -- kids'' depth ≤ 0 → kids'' 1 = .app forces depth ≥ 1, contra.
              exfalso
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids i).depth) ≤ 3 at hd
              have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids i).depth) :=
                  Finset.le_sup (f := fun i => (kids i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1] at h1
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids' i).depth) ≤ 2 at h1
              have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids' i).depth) :=
                  Finset.le_sup (f := fun i => (kids' i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1'1] at h2
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids'' i).depth) ≤ 1 at h2
              have h3 : (kids'' ⟨1, hk1''1_lt⟩).depth ≤ 0 := by
                have hle : (kids'' ⟨1, hk1''1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids'' i).depth) :=
                  Finset.le_sup (f := fun i => (kids'' i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1''1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1''1] at h3
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity op'''))).sup
                         (fun i => (kids''' i).depth) ≤ 0 at h3
              omega
          | app op''' kids''' =>
            -- 4-level depth contradiction (kids'' 0 = .app).
            exfalso
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids i).depth) ≤ 3 at hd
            have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
              have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids i).depth) :=
                Finset.le_sup (f := fun i => (kids i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1] at h1
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids' i).depth) ≤ 2 at h1
            have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
              have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids' i).depth) :=
                Finset.le_sup (f := fun i => (kids' i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1'1] at h2
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids'' i).depth) ≤ 1 at h2
            have h3 : (kids'' ⟨0, hk1''0_lt⟩).depth ≤ 0 := by
              have hle : (kids'' ⟨0, hk1''0_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids'' i).depth) :=
                Finset.le_sup (f := fun i => (kids'' i).depth)
                  (Finset.mem_univ
                    (⟨0, hk1''0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1''0] at h3
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity op'''))).sup
                       (fun i => (kids''' i).depth) ≤ 0 at h3
            omega
      | app _ kids_a =>
        -- kids' 0 = .app .eml kids_a. Depth chain: kids' 0.depth ≤ 1
        -- ⇒ kids_a children leaves (depth ≤ 0).
        -- kids' 1.depth ≤ 1 ⇒ kids' 1 is leaf or .app of leaves.
        -- Enumerate: case on kids' 1, then on (kids_a 0, kids_a 1).
        have hka0_lt : (0 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
        have hka1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
        cases h_k1'1' : (kids' ⟨1, hk1'1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
        | const c =>
          -- kids' 1 = .const c. (kids 1).eval v = exp((kids' 0).eval v) - log c.
          -- (kids' 0).eval v = exp((kids_a 0).eval v) - log((kids_a 1).eval v).
          cases h_ka0 : (kids_a ⟨0, hka0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
          | const c0 =>
            cases h_ka1 : (kids_a ⟨1, hka1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
            | const c1 =>
              -- All constants. K = exp(exp c0 - log c1) - log c.
              let K : ℝ := Real.exp (Real.exp c0 - Real.log c1) - Real.log c
              let v : Fin 2 → ℝ := fun i => if i = 0 then -(|Real.log K| + 1) else 0
              have h_eq := hr v
              change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                     Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
              rw [h_k1] at h_eq
              change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                     Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                               Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                     v 0 + v 1 at h_eq
              rw [h_k1'0, h_k1'1'] at h_eq
              change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                     Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                         Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                               Real.log c) =
                     v 0 + v 1 at h_eq
              rw [h_ka0, h_ka1] at h_eq
              simp only [MinimalBasis.Term.eval] at h_eq
              have h_K_unfold : Real.exp (Real.exp c0 - Real.log c1) - Real.log c = K := rfl
              rw [h_K_unfold] at h_eq
              have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
              rw [h_sum] at h_eq
              have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
                by linarith [le_abs_self (Real.log K)]
              have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
              linarith
            | var l =>
              -- kids_a 0 = const c0, kids_a 1 = var l. (kids_a 1).eval = v l.
              -- (kids' 0).eval = exp c0 - log(v l). Set v l = 0 → log = 0
              --   ⇒ (kids' 0).eval = exp c0. (kids 1).eval = exp(exp c0) - log c = K.
              -- K-bound on the OTHER slot.
              let K : ℝ := Real.exp (Real.exp c0) - Real.log c
              rcases l with ⟨_ | _ | _, hl⟩
              · -- l = 0: v = (0, -(|log K|+1)).
                let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else -(|Real.log K| + 1)
                have h_eq := hr v
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                rw [h_k1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                 Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                       v 0 + v 1 at h_eq
                rw [h_k1'0, h_k1'1'] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                           Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                 Real.log c) =
                       v 0 + v 1 at h_eq
                rw [h_ka0, h_ka1] at h_eq
                simp only [MinimalBasis.Term.eval] at h_eq
                have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                rw [h_vl, Real.log_zero, sub_zero] at h_eq
                have h_K_unfold : Real.exp (Real.exp c0) - Real.log c = K := rfl
                rw [h_K_unfold] at h_eq
                have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
                rw [h_sum] at h_eq
                have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
                  by linarith [le_abs_self (Real.log K)]
                have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                linarith
              · -- l = 1: v = (-(|log K|+1), 0).
                let v : Fin 2 → ℝ := fun i => if i = 0 then -(|Real.log K| + 1) else 0
                have h_eq := hr v
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                rw [h_k1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                 Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                       v 0 + v 1 at h_eq
                rw [h_k1'0, h_k1'1'] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                           Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                 Real.log c) =
                       v 0 + v 1 at h_eq
                rw [h_ka0, h_ka1] at h_eq
                simp only [MinimalBasis.Term.eval] at h_eq
                have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                rw [h_vl, Real.log_zero, sub_zero] at h_eq
                have h_K_unfold : Real.exp (Real.exp c0) - Real.log c = K := rfl
                rw [h_K_unfold] at h_eq
                have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
                rw [h_sum] at h_eq
                have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
                  by linarith [le_abs_self (Real.log K)]
                have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                linarith
              · exact absurd hl (by omega)
            | app op_d kids_d =>
              -- Depth contradiction: kids_a 1 = .app forces depth ≥ 1, but
              -- depth chain forces kids_a 1.depth ≤ 0.
              exfalso
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids i).depth) ≤ 3 at hd
              have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids i).depth) :=
                  Finset.le_sup (f := fun i => (kids i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1] at h1
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids' i).depth) ≤ 2 at h1
              have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
                have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids' i).depth) :=
                  Finset.le_sup (f := fun i => (kids' i).depth)
                    (Finset.mem_univ
                      (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1'0] at h2
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids_a i).depth) ≤ 1 at h2
              have h3 : (kids_a ⟨1, hka1_lt⟩).depth ≤ 0 := by
                have hle : (kids_a ⟨1, hka1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids_a i).depth) :=
                  Finset.le_sup (f := fun i => (kids_a i).depth)
                    (Finset.mem_univ
                      (⟨1, hka1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_ka1] at h3
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity op_d))).sup
                         (fun i => (kids_d i).depth) ≤ 0 at h3
              omega
          | var j =>
            -- kids_a 0 = var j. (kids' 0).eval v = exp(v j) - log((kids_a 1).eval v).
            -- Inner case on kids_a 1: const c1, var l, app (depth contra).
            cases h_ka1' : (kids_a ⟨1, hka1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
            | const c1 =>
              -- (kids' 0).eval v = exp(v j) - log c1. Set v j = 0: K_inner = 1 - log c1.
              -- (kids 1).eval = exp K_inner - log c = K_outer.
              let K_inner : ℝ := 1 - Real.log c1
              let K_outer : ℝ := Real.exp K_inner - Real.log c
              rcases j with ⟨_ | _ | _, hj⟩
              · -- j = 0: v = (0, -(|log K_outer|+1)).
                let v : Fin 2 → ℝ :=
                  fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                have h_eq := hr v
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                rw [h_k1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                 Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                       v 0 + v 1 at h_eq
                rw [h_k1'0, h_k1'1'] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                           Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                 Real.log c) =
                       v 0 + v 1 at h_eq
                rw [h_ka0, h_ka1'] at h_eq
                simp only [MinimalBasis.Term.eval] at h_eq
                have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                rw [h_vj, Real.exp_zero] at h_eq
                have h_Kinner_unfold : (1 : ℝ) - Real.log c1 = K_inner := rfl
                rw [h_Kinner_unfold] at h_eq
                have h_Kouter_unfold : Real.exp K_inner - Real.log c = K_outer := rfl
                rw [h_Kouter_unfold] at h_eq
                have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                rw [h_sum] at h_eq
                have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                  by linarith [le_abs_self (Real.log K_outer)]
                have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                linarith
              · -- j = 1: v = (-(|log K_outer|+1), 0).
                let v : Fin 2 → ℝ :=
                  fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                have h_eq := hr v
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                rw [h_k1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                 Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                       v 0 + v 1 at h_eq
                rw [h_k1'0, h_k1'1'] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                           Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                 Real.log c) =
                       v 0 + v 1 at h_eq
                rw [h_ka0, h_ka1'] at h_eq
                simp only [MinimalBasis.Term.eval] at h_eq
                have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                rw [h_vj, Real.exp_zero] at h_eq
                have h_Kinner_unfold : (1 : ℝ) - Real.log c1 = K_inner := rfl
                rw [h_Kinner_unfold] at h_eq
                have h_Kouter_unfold : Real.exp K_inner - Real.log c = K_outer := rfl
                rw [h_Kouter_unfold] at h_eq
                have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                rw [h_sum] at h_eq
                have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                  by linarith [le_abs_self (Real.log K_outer)]
                have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                linarith
              · exact absurd hj (by omega)
            | var l =>
              -- (kids' 0).eval = exp(v j) - log(v l). 4 sub-cases on (j, l).
              -- Same-var: set v_shared = 0 ⇒ exp(0) - log(0) = 1. K = e - log c.
              -- Cross-var: set v_l = 0 (log = 0), v_j = -(|log c|+3). Use new helper.
              rcases j with ⟨_ | _ | _, hj⟩
              · rcases l with ⟨_ | _ | _, hl⟩
                · -- (j=0, l=0): same-var. v = (0, -(|log K|+1)) where K = e - log c.
                  let K : ℝ := Real.exp 1 - Real.log c
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then 0 else -(|Real.log K| + 1)
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log c) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0, h_ka1'] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                  rw [h_vj, Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                  -- h_eq: exp((kids 0).eval v) - log(exp 1 - log c) = v 0 + v 1.
                  have h_K_unfold : Real.exp 1 - Real.log c = K := rfl
                  rw [h_K_unfold] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
                    by linarith [le_abs_self (Real.log K)]
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · -- (j=0, l=1): cross-var. v 0 = -(|log c|+3), v 1 = 0.
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then -(|Real.log c| + 3) else 0
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log c) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0, h_ka1'] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vj : v ⟨0, hj⟩ = -(|Real.log c| + 3) := by simp [v]
                  have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                  rw [h_vj, h_vl, Real.log_zero, sub_zero] at h_eq
                  -- h_eq: exp((kids 0).eval v) - log(exp(exp(-(|log c|+3))) - log c) = v 0 + v 1
                  have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log c| + 3) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_v_le_zero : -(|Real.log c| + 3) ≤ (0 : ℝ) := by
                    have := abs_nonneg (Real.log c); linarith
                  have h_log_bound :
                      Real.log (Real.exp (Real.exp (-(|Real.log c| + 3))) - Real.log c) ≤
                        1 + |Real.log c| :=
                    log_exp_exp_v_sub_const_le _ _ h_v_le_zero
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · exact absurd hl (by omega)
              · rcases l with ⟨_ | _ | _, hl⟩
                · -- (j=1, l=0): cross-var. v 0 = 0, v 1 = -(|log c|+3).
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then 0 else -(|Real.log c| + 3)
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log c) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0, h_ka1'] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vj : v ⟨0 + 1, hj⟩ = -(|Real.log c| + 3) := by simp [v]
                  have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                  rw [h_vj, h_vl, Real.log_zero, sub_zero] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log c| + 3) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_v_le_zero : -(|Real.log c| + 3) ≤ (0 : ℝ) := by
                    have := abs_nonneg (Real.log c); linarith
                  have h_log_bound :
                      Real.log (Real.exp (Real.exp (-(|Real.log c| + 3))) - Real.log c) ≤
                        1 + |Real.log c| :=
                    log_exp_exp_v_sub_const_le _ _ h_v_le_zero
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · -- (j=1, l=1): same-var at index 1.
                  let K : ℝ := Real.exp 1 - Real.log c
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then -(|Real.log K| + 1) else 0
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log c) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0, h_ka1'] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                  rw [h_vj, Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                  have h_K_unfold : Real.exp 1 - Real.log c = K := rfl
                  rw [h_K_unfold] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K| + 1) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_RHS_le : -(|Real.log K| + 1) + Real.log K ≤ -1 :=
                    by linarith [le_abs_self (Real.log K)]
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · exact absurd hl (by omega)
              · exact absurd hj (by omega)
            | app op_d kids_d =>
              -- Depth contradiction: kids_a 1 = .app forces depth ≥ 1.
              exfalso
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids i).depth) ≤ 3 at hd
              have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids i).depth) :=
                  Finset.le_sup (f := fun i => (kids i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1] at h1
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids' i).depth) ≤ 2 at h1
              have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
                have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids' i).depth) :=
                  Finset.le_sup (f := fun i => (kids' i).depth)
                    (Finset.mem_univ
                      (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1'0] at h2
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids_a i).depth) ≤ 1 at h2
              have h3 : (kids_a ⟨1, hka1_lt⟩).depth ≤ 0 := by
                have hle : (kids_a ⟨1, hka1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids_a i).depth) :=
                  Finset.le_sup (f := fun i => (kids_a i).depth)
                    (Finset.mem_univ
                      (⟨1, hka1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_ka1'] at h3
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity op_d))).sup
                         (fun i => (kids_d i).depth) ≤ 0 at h3
              omega
          | app op_d kids_d =>
            -- Depth contradiction: kids_a 0 = .app forces depth ≥ 1.
            exfalso
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids i).depth) ≤ 3 at hd
            have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
              have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids i).depth) :=
                Finset.le_sup (f := fun i => (kids i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1] at h1
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids' i).depth) ≤ 2 at h1
            have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
              have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids' i).depth) :=
                Finset.le_sup (f := fun i => (kids' i).depth)
                  (Finset.mem_univ
                    (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1'0] at h2
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids_a i).depth) ≤ 1 at h2
            have h3 : (kids_a ⟨0, hka0_lt⟩).depth ≤ 0 := by
              have hle : (kids_a ⟨0, hka0_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids_a i).depth) :=
                Finset.le_sup (f := fun i => (kids_a i).depth)
                  (Finset.mem_univ
                    (⟨0, hka0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_ka0] at h3
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity op_d))).sup
                       (fun i => (kids_d i).depth) ≤ 0 at h3
            omega
        | var k =>
          -- kids' 1 = .var k. (kids 1).eval v = exp((kids' 0).eval v) - log(v k).
          -- Setting v k = 0 makes log(v k) = 0 (junk), reducing the equation to
          --   exp((kids 0).eval v) = (kids' 0).eval v + v 0 + v 1.
          -- (kids' 0).eval = exp((kids_a 0).eval v) - log((kids_a 1).eval v).
          -- Enumerate (kids_a 0, kids_a 1) × k ∈ Fin 2.
          rcases k with ⟨_ | _ | _, hk⟩
          · -- k = 0: v_k = v_0 = 0. v_1 is the "active" slot.
            cases h_ka0_k0 : (kids_a ⟨0, hka0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
            | const c0 =>
              cases h_ka1_k0 : (kids_a ⟨1, hka1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
              | const c1 =>
                -- All const: (kids' 0).eval = exp c0 - log c1 = K (const).
                -- v = (0, -(|K|+2)). exp((kids 0).eval v) = K + v 1 = K - |K| - 2 ≤ -2.
                let K : ℝ := Real.exp c0 - Real.log c1
                let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else -(|K| + 2)
                have h_eq := hr v
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                rw [h_k1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                 Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                       v 0 + v 1 at h_eq
                rw [h_k1'0, h_k1'1'] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                           Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                 Real.log (v ⟨0, hk⟩)) =
                       v 0 + v 1 at h_eq
                rw [h_ka0_k0, h_ka1_k0] at h_eq
                simp only [MinimalBasis.Term.eval] at h_eq
                have h_vk : v ⟨0, hk⟩ = 0 := by simp [v]
                rw [h_vk, Real.log_zero, sub_zero, Real.log_exp] at h_eq
                have h_K_unfold : Real.exp c0 - Real.log c1 = K := rfl
                rw [h_K_unfold] at h_eq
                have h_sum : (v 0 + v 1 : ℝ) = -(|K| + 2) := by simp [v]
                rw [h_sum] at h_eq
                have h_RHS_le : -(|K| + 2) + K ≤ -2 := by linarith [le_abs_self K]
                have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                linarith
              | var l =>
                rcases l with ⟨_ | _ | _, hl⟩
                · -- (kids_a 1 = var 0). v_l = v_0 = 0. log 0 = 0. (kids' 0).eval = exp c0 = K.
                  let K : ℝ := Real.exp c0
                  let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else -(|K| + 2)
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log (v ⟨0, hk⟩)) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0_k0, h_ka1_k0] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vk : v ⟨0, hk⟩ = 0 := by simp [v]
                  rw [h_vk] at h_eq
                  simp only [Real.log_zero, sub_zero] at h_eq
                  rw [Real.log_exp] at h_eq
                  have h_K_unfold : Real.exp c0 = K := rfl
                  rw [h_K_unfold] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|K| + 2) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_RHS_le : -(|K| + 2) + K ≤ -2 := by linarith [le_abs_self K]
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · -- (kids_a 1 = var 1). v_l = v_1 = -(exp c0 + 5).
                  -- log(v_1) = log(exp c0 + 5) ≥ 0.
                  -- (kids' 0).eval = exp c0 - log(exp c0 + 5).
                  -- Equation: exp((kids 0).eval v) = exp c0 - log(exp c0 + 5) - (exp c0 + 5)
                  --   = -log(exp c0 + 5) - 5 ≤ -5.
                  let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else -(Real.exp c0 + 5)
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log (v ⟨0, hk⟩)) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0_k0, h_ka1_k0] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vk : v ⟨0, hk⟩ = 0 := by simp [v]
                  have h_vl : v ⟨0 + 1, hl⟩ = -(Real.exp c0 + 5) := by simp [v]
                  rw [h_vk, h_vl, Real.log_zero, sub_zero, Real.log_exp,
                      show -(Real.exp c0 + 5) = -(Real.exp c0 + 5) from rfl,
                      Real.log_neg_eq_log] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(Real.exp c0 + 5) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_exp_c0_plus_5_pos : Real.exp c0 + 5 ≥ 1 := by
                    have := Real.exp_pos c0; linarith
                  have h_log_nonneg : Real.log (Real.exp c0 + 5) ≥ 0 :=
                    Real.log_nonneg h_exp_c0_plus_5_pos
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · exact absurd hl (by omega)
              | app op_d kids_d =>
                -- Depth contradiction.
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 3 at hd
                have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                  have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids' i).depth) ≤ 2 at h1
                have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
                  have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids' i).depth) :=
                    Finset.le_sup (f := fun i => (kids' i).depth)
                      (Finset.mem_univ
                        (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1'0] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids_a i).depth) ≤ 1 at h2
                have h3 : (kids_a ⟨1, hka1_lt⟩).depth ≤ 0 := by
                  have hle : (kids_a ⟨1, hka1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids_a i).depth) :=
                    Finset.le_sup (f := fun i => (kids_a i).depth)
                      (Finset.mem_univ
                        (⟨1, hka1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_ka1_k0] at h3
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op_d))).sup
                           (fun i => (kids_d i).depth) ≤ 0 at h3
                omega
            | var j =>
              -- kids_a 0 = var j for k = 0. (kids' 0).eval = exp(v j) - log((kids_a 1).eval v).
              cases h_ka1_k0_j : (kids_a ⟨1, hka1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
              | const c1 =>
                rcases j with ⟨_ | _ | _, hj⟩
                · -- (j=0, kids_a 1 = const c1). v_j = v_0 = 0. K = 1 - log c1.
                  let K : ℝ := 1 - Real.log c1
                  let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else -(|K| + 2)
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log (v ⟨0, hk⟩)) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0_k0, h_ka1_k0_j] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                  rw [h_vj] at h_eq
                  simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                  rw [Real.log_exp] at h_eq
                  have h_K_unfold : (1 : ℝ) - Real.log c1 = K := rfl
                  rw [h_K_unfold] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|K| + 2) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_RHS_le : -(|K| + 2) + K ≤ -2 := by linarith [le_abs_self K]
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · -- (j=1, kids_a 1 = const c1). v_j = v_1 = -(|log c1|+3).
                  -- (kids' 0).eval = exp(v 1) - log c1. exp(v 1) ≤ 1.
                  -- exp((kids 0).eval) = exp(v 1) - log c1 + 0 + v 1 ≤ 1 + |log c1| + v 1 = -2.
                  let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else -(|Real.log c1| + 3)
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log (v ⟨0, hk⟩)) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0_k0, h_ka1_k0_j] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vk : v ⟨0, hk⟩ = 0 := by simp [v]
                  have h_vj : v ⟨0 + 1, hj⟩ = -(|Real.log c1| + 3) := by simp [v]
                  rw [h_vk, h_vj] at h_eq
                  simp only [Real.log_zero, sub_zero] at h_eq
                  rw [Real.log_exp] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log c1| + 3) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_exp_le_one : Real.exp (-(|Real.log c1| + 3)) ≤ 1 := by
                    apply Real.exp_le_one_iff.mpr
                    have := abs_nonneg (Real.log c1); linarith
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith [le_abs_self (Real.log c1), neg_abs_le (Real.log c1)]
                · exact absurd hj (by omega)
              | var l =>
                rcases j with ⟨_ | _ | _, hj⟩
                · rcases l with ⟨_ | _ | _, hl⟩
                  · -- (j=0, l=0): v_0 = 0. (kids' 0).eval = 1 - 0 = 1 = K.
                    let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else -3
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (v ⟨0, hk⟩)) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_k0, h_ka1_k0_j] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vk : v ⟨0, hk⟩ = 0 := by simp [v]
                    rw [h_vk] at h_eq
                    simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                    rw [Real.log_exp] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -3 := by simp [v]
                    rw [h_sum] at h_eq
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  · -- (j=0, l=1): v 0 = 0, v 1 = -1. log(-1) = 0. (kids' 0).eval = 1 - 0 = 1.
                    let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else -1
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (v ⟨0, hk⟩)) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_k0, h_ka1_k0_j] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                    have h_vl : v ⟨0 + 1, hl⟩ = -1 := by simp [v]
                    rw [h_vj, h_vl] at h_eq
                    have h_log_neg_one : Real.log (-1 : ℝ) = 0 := by
                      rw [show (-1 : ℝ) = -(1 : ℝ) by ring, Real.log_neg_eq_log, Real.log_one]
                    rw [h_log_neg_one] at h_eq
                    simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                    rw [Real.log_exp] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -1 := by simp [v]
                    rw [h_sum] at h_eq
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  · exact absurd hl (by omega)
                · rcases l with ⟨_ | _ | _, hl⟩
                  · -- (j=1, l=0): v 0 = 0 (so v l = 0, log = 0), v 1 = -3.
                    -- (kids' 0).eval = exp(v 1) - 0 = exp(-3) ≤ 1.
                    -- Equation: exp((kids 0).eval) = exp(-3) + v 1 = exp(-3) - 3 ≤ -2.
                    let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else -3
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (v ⟨0, hk⟩)) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_k0, h_ka1_k0_j] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vj : v ⟨0 + 1, hj⟩ = -3 := by simp [v]
                    have h_vk : v ⟨0, hk⟩ = 0 := by simp [v]
                    rw [h_vj, h_vk] at h_eq
                    simp only [Real.log_zero, sub_zero] at h_eq
                    rw [Real.log_exp] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -3 := by simp [v]
                    rw [h_sum] at h_eq
                    have h_exp_le_one : Real.exp (-3 : ℝ) ≤ 1 := by
                      apply Real.exp_le_one_iff.mpr; norm_num
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  · -- (j=1, l=1): v 0 = 0, v 1 = -2. v_j = v_l = -2.
                    -- (kids' 0).eval = exp(-2) - log(-2) = exp(-2) - log 2.
                    -- exp((kids 0).eval) = exp(-2) - log 2 - 2 ≤ 1 - log 2 - 2 = -1 - log 2 < -1.
                    let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else -2
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (v ⟨0, hk⟩)) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_k0, h_ka1_k0_j] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vj : v ⟨0 + 1, hj⟩ = -2 := by simp [v]
                    have h_vk : v ⟨0, hk⟩ = 0 := by simp [v]
                    rw [h_vj, h_vk] at h_eq
                    have h_log_neg_two : Real.log (-2 : ℝ) = Real.log 2 := by
                      rw [show (-2 : ℝ) = -(2 : ℝ) by ring, Real.log_neg_eq_log]
                    rw [h_log_neg_two] at h_eq
                    simp only [Real.log_zero, sub_zero] at h_eq
                    rw [Real.log_exp] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -2 := by simp [v]
                    rw [h_sum] at h_eq
                    have h_exp_neg2_le_one : Real.exp (-2 : ℝ) ≤ 1 := by
                      apply Real.exp_le_one_iff.mpr; norm_num
                    have h_log2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num)
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  · exact absurd hl (by omega)
                · exact absurd hj (by omega)
              | app op_d kids_d =>
                -- Depth contradiction.
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 3 at hd
                have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                  have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids' i).depth) ≤ 2 at h1
                have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
                  have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids' i).depth) :=
                    Finset.le_sup (f := fun i => (kids' i).depth)
                      (Finset.mem_univ
                        (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1'0] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids_a i).depth) ≤ 1 at h2
                have h3 : (kids_a ⟨1, hka1_lt⟩).depth ≤ 0 := by
                  have hle : (kids_a ⟨1, hka1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids_a i).depth) :=
                    Finset.le_sup (f := fun i => (kids_a i).depth)
                      (Finset.mem_univ
                        (⟨1, hka1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_ka1_k0_j] at h3
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op_d))).sup
                           (fun i => (kids_d i).depth) ≤ 0 at h3
                omega
            | app op_d kids_d =>
              -- Depth contradiction: kids_a 0 = .app.
              exfalso
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids i).depth) ≤ 3 at hd
              have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids i).depth) :=
                  Finset.le_sup (f := fun i => (kids i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1] at h1
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids' i).depth) ≤ 2 at h1
              have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
                have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids' i).depth) :=
                  Finset.le_sup (f := fun i => (kids' i).depth)
                    (Finset.mem_univ
                      (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1'0] at h2
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids_a i).depth) ≤ 1 at h2
              have h3 : (kids_a ⟨0, hka0_lt⟩).depth ≤ 0 := by
                have hle : (kids_a ⟨0, hka0_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids_a i).depth) :=
                  Finset.le_sup (f := fun i => (kids_a i).depth)
                    (Finset.mem_univ
                      (⟨0, hka0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_ka0_k0] at h3
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity op_d))).sup
                         (fun i => (kids_d i).depth) ≤ 0 at h3
              omega
          · -- k = 1: v_k = v_1 = 0. v_0 is the "active" slot.
            -- Mirror of k=0 with var indices swapped.
            cases h_ka0_k1 : (kids_a ⟨0, hka0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
            | const c0 =>
              cases h_ka1_k1 : (kids_a ⟨1, hka1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
              | const c1 =>
                -- All const: K = exp c0 - log c1. v = (-(|K|+2), 0). K-bound.
                let K : ℝ := Real.exp c0 - Real.log c1
                let v : Fin 2 → ℝ := fun i => if i = 0 then -(|K| + 2) else 0
                have h_eq := hr v
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                rw [h_k1] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                 Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                       v 0 + v 1 at h_eq
                rw [h_k1'0, h_k1'1'] at h_eq
                change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                       Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                           Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                 Real.log (v ⟨0 + 1, hk⟩)) =
                       v 0 + v 1 at h_eq
                rw [h_ka0_k1, h_ka1_k1] at h_eq
                simp only [MinimalBasis.Term.eval] at h_eq
                have h_vk : v ⟨0 + 1, hk⟩ = 0 := by simp [v]
                rw [h_vk] at h_eq
                simp only [Real.log_zero, sub_zero] at h_eq
                rw [Real.log_exp] at h_eq
                have h_K_unfold : Real.exp c0 - Real.log c1 = K := rfl
                rw [h_K_unfold] at h_eq
                have h_sum : (v 0 + v 1 : ℝ) = -(|K| + 2) := by simp [v]
                rw [h_sum] at h_eq
                have h_RHS_le : -(|K| + 2) + K ≤ -2 := by linarith [le_abs_self K]
                have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                linarith
              | var l =>
                rcases l with ⟨_ | _ | _, hl⟩
                · -- (kids_a 1 = var 0). v_l = v_0 = active = -(exp c0 + 5).
                  let v : Fin 2 → ℝ := fun i => if i = 0 then -(Real.exp c0 + 5) else 0
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log (v ⟨0 + 1, hk⟩)) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0_k1, h_ka1_k1] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vk : v ⟨0 + 1, hk⟩ = 0 := by simp [v]
                  have h_vl : v ⟨0, hl⟩ = -(Real.exp c0 + 5) := by simp [v]
                  rw [h_vk, h_vl] at h_eq
                  have h_log_neg : Real.log (-(Real.exp c0 + 5)) =
                                   Real.log (Real.exp c0 + 5) := Real.log_neg_eq_log _
                  rw [h_log_neg] at h_eq
                  simp only [Real.log_zero, sub_zero] at h_eq
                  rw [Real.log_exp] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(Real.exp c0 + 5) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_exp_c0_plus_5_pos : Real.exp c0 + 5 ≥ 1 := by
                    have := Real.exp_pos c0; linarith
                  have h_log_nonneg : Real.log (Real.exp c0 + 5) ≥ 0 :=
                    Real.log_nonneg h_exp_c0_plus_5_pos
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · -- (kids_a 1 = var 1). v_l = v_1 = 0. log 0 = 0. K = exp c0.
                  let K : ℝ := Real.exp c0
                  let v : Fin 2 → ℝ := fun i => if i = 0 then -(|K| + 2) else 0
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log (v ⟨0 + 1, hk⟩)) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0_k1, h_ka1_k1] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vk : v ⟨0 + 1, hk⟩ = 0 := by simp [v]
                  rw [h_vk] at h_eq
                  simp only [Real.log_zero, sub_zero] at h_eq
                  rw [Real.log_exp] at h_eq
                  have h_K_unfold : Real.exp c0 = K := rfl
                  rw [h_K_unfold] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|K| + 2) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_RHS_le : -(|K| + 2) + K ≤ -2 := by linarith [le_abs_self K]
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · exact absurd hl (by omega)
              | app op_d kids_d =>
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 3 at hd
                have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                  have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids' i).depth) ≤ 2 at h1
                have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
                  have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids' i).depth) :=
                    Finset.le_sup (f := fun i => (kids' i).depth)
                      (Finset.mem_univ
                        (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1'0] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids_a i).depth) ≤ 1 at h2
                have h3 : (kids_a ⟨1, hka1_lt⟩).depth ≤ 0 := by
                  have hle : (kids_a ⟨1, hka1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids_a i).depth) :=
                    Finset.le_sup (f := fun i => (kids_a i).depth)
                      (Finset.mem_univ
                        (⟨1, hka1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_ka1_k1] at h3
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op_d))).sup
                           (fun i => (kids_d i).depth) ≤ 0 at h3
                omega
            | var j =>
              cases h_ka1_k1' : (kids_a ⟨1, hka1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
              | const c1 =>
                rcases j with ⟨_ | _ | _, hj⟩
                · -- (j=0, const c1) at k=1. v_j = v_0 = -(|log c1|+3).
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then -(|Real.log c1| + 3) else 0
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log (v ⟨0 + 1, hk⟩)) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0_k1, h_ka1_k1'] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vk : v ⟨0 + 1, hk⟩ = 0 := by simp [v]
                  have h_vj : v ⟨0, hj⟩ = -(|Real.log c1| + 3) := by simp [v]
                  rw [h_vk, h_vj] at h_eq
                  simp only [Real.log_zero, sub_zero] at h_eq
                  rw [Real.log_exp] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log c1| + 3) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_exp_le_one : Real.exp (-(|Real.log c1| + 3)) ≤ 1 := by
                    apply Real.exp_le_one_iff.mpr
                    have := abs_nonneg (Real.log c1); linarith
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith [le_abs_self (Real.log c1), neg_abs_le (Real.log c1)]
                · -- (j=1, const c1) at k=1. v_j = v_1 = 0. K = 1 - log c1.
                  let K : ℝ := 1 - Real.log c1
                  let v : Fin 2 → ℝ := fun i => if i = 0 then -(|K| + 2) else 0
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log (v ⟨0 + 1, hk⟩)) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0_k1, h_ka1_k1'] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                  rw [h_vj] at h_eq
                  simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                  rw [Real.log_exp] at h_eq
                  have h_K_unfold : (1 : ℝ) - Real.log c1 = K := rfl
                  rw [h_K_unfold] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|K| + 2) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_RHS_le : -(|K| + 2) + K ≤ -2 := by linarith [le_abs_self K]
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                · exact absurd hj (by omega)
              | var l =>
                rcases j with ⟨_ | _ | _, hj⟩
                · rcases l with ⟨_ | _ | _, hl⟩
                  · -- (j=0, l=0) at k=1: v_j = v_l = v_0. Set v 0 = -2.
                    let v : Fin 2 → ℝ := fun i => if i = 0 then -2 else 0
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (v ⟨0 + 1, hk⟩)) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_k1, h_ka1_k1'] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vk : v ⟨0 + 1, hk⟩ = 0 := by simp [v]
                    have h_vj : v ⟨0, hj⟩ = -2 := by simp [v]
                    rw [h_vk, h_vj] at h_eq
                    have h_log_neg_two : Real.log (-2 : ℝ) = Real.log 2 := by
                      rw [show (-2 : ℝ) = -(2 : ℝ) by ring, Real.log_neg_eq_log]
                    rw [h_log_neg_two] at h_eq
                    simp only [Real.log_zero, sub_zero] at h_eq
                    rw [Real.log_exp] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -2 := by simp [v]
                    rw [h_sum] at h_eq
                    have h_exp_neg2_le_one : Real.exp (-2 : ℝ) ≤ 1 := by
                      apply Real.exp_le_one_iff.mpr; norm_num
                    have h_log2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num)
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  · -- (j=0, l=1) at k=1: v_j = v_0, v_l = v_1 = 0. log 0 = 0.
                    -- (kids' 0).eval = exp(v 0). Pick v 0 = -3.
                    let v : Fin 2 → ℝ := fun i => if i = 0 then -3 else 0
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (v ⟨0 + 1, hk⟩)) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_k1, h_ka1_k1'] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vj : v ⟨0, hj⟩ = -3 := by simp [v]
                    have h_vk : v ⟨0 + 1, hk⟩ = 0 := by simp [v]
                    rw [h_vj, h_vk] at h_eq
                    simp only [Real.log_zero, sub_zero] at h_eq
                    rw [Real.log_exp] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -3 := by simp [v]
                    rw [h_sum] at h_eq
                    have h_exp_le_one : Real.exp (-3 : ℝ) ≤ 1 := by
                      apply Real.exp_le_one_iff.mpr; norm_num
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  · exact absurd hl (by omega)
                · rcases l with ⟨_ | _ | _, hl⟩
                  · -- (j=1, l=0) at k=1: v_j = v_1 = 0, v_l = v_0. v 0 = -1.
                    -- log(-1) = 0. (kids' 0).eval = 1 - 0 = 1.
                    -- exp((kids 0).eval) = 1 + (-1) + 0 = 0. Contradiction.
                    let v : Fin 2 → ℝ := fun i => if i = 0 then -1 else 0
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (v ⟨0 + 1, hk⟩)) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_k1, h_ka1_k1'] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                    have h_vl : v ⟨0, hl⟩ = -1 := by simp [v]
                    rw [h_vj, h_vl] at h_eq
                    have h_log_neg_one : Real.log (-1 : ℝ) = 0 := by
                      rw [show (-1 : ℝ) = -(1 : ℝ) by ring, Real.log_neg_eq_log, Real.log_one]
                    rw [h_log_neg_one] at h_eq
                    simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                    rw [Real.log_exp] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -1 := by simp [v]
                    rw [h_sum] at h_eq
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  · -- (j=1, l=1) at k=1: v_j = v_l = v_1 = 0. K = 1.
                    let v : Fin 2 → ℝ := fun i => if i = 0 then -3 else 0
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (v ⟨0 + 1, hk⟩)) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_k1, h_ka1_k1'] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                    rw [h_vj] at h_eq
                    simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                    rw [Real.log_exp] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -3 := by simp [v]
                    rw [h_sum] at h_eq
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  · exact absurd hl (by omega)
                · exact absurd hj (by omega)
              | app op_d kids_d =>
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 3 at hd
                have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                  have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids' i).depth) ≤ 2 at h1
                have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
                  have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids' i).depth) :=
                    Finset.le_sup (f := fun i => (kids' i).depth)
                      (Finset.mem_univ
                        (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1'0] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids_a i).depth) ≤ 1 at h2
                have h3 : (kids_a ⟨1, hka1_lt⟩).depth ≤ 0 := by
                  have hle : (kids_a ⟨1, hka1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids_a i).depth) :=
                    Finset.le_sup (f := fun i => (kids_a i).depth)
                      (Finset.mem_univ
                        (⟨1, hka1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_ka1_k1'] at h3
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op_d))).sup
                           (fun i => (kids_d i).depth) ≤ 0 at h3
                omega
            | app op_d kids_d =>
              -- Depth contra: kids_a 0 = .app.
              exfalso
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids i).depth) ≤ 3 at hd
              have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids i).depth) :=
                  Finset.le_sup (f := fun i => (kids i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1] at h1
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids' i).depth) ≤ 2 at h1
              have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
                have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids' i).depth) :=
                  Finset.le_sup (f := fun i => (kids' i).depth)
                    (Finset.mem_univ
                      (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1'0] at h2
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids_a i).depth) ≤ 1 at h2
              have h3 : (kids_a ⟨0, hka0_lt⟩).depth ≤ 0 := by
                have hle : (kids_a ⟨0, hka0_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids_a i).depth) :=
                  Finset.le_sup (f := fun i => (kids_a i).depth)
                    (Finset.mem_univ
                      (⟨0, hka0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_ka0_k1] at h3
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity op_d))).sup
                         (fun i => (kids_d i).depth) ≤ 0 at h3
              omega
          · exact absurd hk (by omega)
        | app op_r kids_r =>
          -- kids' 1 = .app .eml kids_r. kids_r children leaves (depth ≤ 0).
          -- Enumerate (kids_a 0, kids_a 1) × (kids_r 0, kids_r 1).
          have hkr0_lt : (0 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
          have hkr1_lt : (1 : ℕ) < EmlBasis.arity EmlOp.eml := by decide
          cases h_ka0_r : (kids_a ⟨0, hka0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
          | const c0 =>
            cases h_ka1_r : (kids_a ⟨1, hka1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
            | const c1 =>
              -- (kids_a 0, kids_a 1) = (const c0, const c1). (kids' 0).eval = exp c0 - log c1 = K_a.
              -- Case on (kids_r 0, kids_r 1) with K_a a constant.
              cases h_kr0_cc : (kids_r ⟨0, hkr0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
              | const r0 =>
                cases h_kr1_cc : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                | const r1 =>
                  -- All const. K_outer = exp(exp c0 - log c1) - log(exp r0 - log r1). K-bound.
                  let K_a : ℝ := Real.exp c0 - Real.log c1
                  let K_r : ℝ := Real.exp r0 - Real.log r1
                  let K_outer : ℝ := Real.exp K_a - Real.log K_r
                  let v : Fin 2 → ℝ :=
                    fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                  have h_eq := hr v
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                  rw [h_k1] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                   Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                         v 0 + v 1 at h_eq
                  rw [h_k1'0, h_k1'1'] at h_eq
                  change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                         Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                             Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                   Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                             Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                         v 0 + v 1 at h_eq
                  rw [h_ka0_r, h_ka1_r, h_kr0_cc, h_kr1_cc] at h_eq
                  simp only [MinimalBasis.Term.eval] at h_eq
                  have h_Ka_unfold : Real.exp c0 - Real.log c1 = K_a := rfl
                  have h_Kr_unfold : Real.exp r0 - Real.log r1 = K_r := rfl
                  rw [h_Ka_unfold, h_Kr_unfold] at h_eq
                  have h_Kouter_unfold : Real.exp K_a - Real.log K_r = K_outer := rfl
                  rw [h_Kouter_unfold] at h_eq
                  have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                  rw [h_sum] at h_eq
                  have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                    by linarith [le_abs_self (Real.log K_outer)]
                  have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                  linarith
                | var k =>
                  -- (kids_r 1 = var k). Set v k = 0 ⇒ log 0 = 0.
                  -- (kids' 1).eval = exp r0 - 0 = exp r0. (kids 1).eval = exp K_a - r0 = K_outer.
                  let K_a : ℝ := Real.exp c0 - Real.log c1
                  let K_outer : ℝ := Real.exp K_a - r0
                  rcases k with ⟨_ | _ | _, hk⟩
                  · -- k = 0
                    let v : Fin 2 → ℝ :=
                      fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                               Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_r, h_ka1_r, h_kr0_cc, h_kr1_cc] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vk : v ⟨0, hk⟩ = 0 := by simp [v]
                    rw [h_vk] at h_eq
                    simp only [Real.log_zero, sub_zero] at h_eq
                    rw [Real.log_exp] at h_eq
                    have h_Ka_unfold : Real.exp c0 - Real.log c1 = K_a := rfl
                    rw [h_Ka_unfold] at h_eq
                    have h_Kouter_unfold : Real.exp K_a - r0 = K_outer := rfl
                    rw [h_Kouter_unfold] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                    rw [h_sum] at h_eq
                    have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                      by linarith [le_abs_self (Real.log K_outer)]
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  · -- k = 1
                    let v : Fin 2 → ℝ :=
                      fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                               Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_r, h_ka1_r, h_kr0_cc, h_kr1_cc] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vk : v ⟨0 + 1, hk⟩ = 0 := by simp [v]
                    rw [h_vk] at h_eq
                    simp only [Real.log_zero, sub_zero] at h_eq
                    rw [Real.log_exp] at h_eq
                    have h_Ka_unfold : Real.exp c0 - Real.log c1 = K_a := rfl
                    rw [h_Ka_unfold] at h_eq
                    have h_Kouter_unfold : Real.exp K_a - r0 = K_outer := rfl
                    rw [h_Kouter_unfold] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                    rw [h_sum] at h_eq
                    have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                      by linarith [le_abs_self (Real.log K_outer)]
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  · exact absurd hk (by omega)
                | app op_d kids_d =>
                  -- Depth contra: kids_r 1 = .app.
                  exfalso
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids i).depth) ≤ 3 at hd
                  have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                    have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids i).depth) :=
                      Finset.le_sup (f := fun i => (kids i).depth)
                        (Finset.mem_univ
                          (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k1] at h1
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids' i).depth) ≤ 2 at h1
                  have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                    have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids' i).depth) :=
                      Finset.le_sup (f := fun i => (kids' i).depth)
                        (Finset.mem_univ
                          (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k1'1'] at h2
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids_r i).depth) ≤ 1 at h2
                  have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                    have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids_r i).depth) :=
                      Finset.le_sup (f := fun i => (kids_r i).depth)
                        (Finset.mem_univ
                          (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_kr1_cc] at h3
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity op_d))).sup
                             (fun i => (kids_d i).depth) ≤ 0 at h3
                  omega
              | var k =>
                -- (kids_a 0, kids_a 1) = (const c0, const c1), kids_r 0 = var k.
                -- (kids' 0).eval = K_a. exp(v_k) is the active part of kids' 1.
                -- Case on kids_r 1.
                cases h_kr1_vk : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                | const r1 =>
                  -- Set v_k = 0 ⇒ exp 0 = 1. (kids' 1).eval = 1 - log r1 = K_r.
                  -- K-bound on other slot. 2 sub-cases on k.
                  let K_a : ℝ := Real.exp c0 - Real.log c1
                  let K_r : ℝ := 1 - Real.log r1
                  let K_outer : ℝ := Real.exp K_a - Real.log K_r
                  rcases k with ⟨_ | _ | _, hk⟩
                  · -- k = 0
                    let v : Fin 2 → ℝ :=
                      fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                               Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_r, h_ka1_r, h_kr0_cc, h_kr1_vk] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vk : v ⟨0, hk⟩ = 0 := by simp [v]
                    rw [h_vk, Real.exp_zero] at h_eq
                    have h_Ka_unfold : Real.exp c0 - Real.log c1 = K_a := rfl
                    have h_Kr_unfold : (1 : ℝ) - Real.log r1 = K_r := rfl
                    rw [h_Ka_unfold, h_Kr_unfold] at h_eq
                    have h_Kouter_unfold : Real.exp K_a - Real.log K_r = K_outer := rfl
                    rw [h_Kouter_unfold] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                    rw [h_sum] at h_eq
                    have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                      by linarith [le_abs_self (Real.log K_outer)]
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  · -- k = 1
                    let v : Fin 2 → ℝ :=
                      fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                               Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_r, h_ka1_r, h_kr0_cc, h_kr1_vk] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vk : v ⟨0 + 1, hk⟩ = 0 := by simp [v]
                    rw [h_vk, Real.exp_zero] at h_eq
                    have h_Ka_unfold : Real.exp c0 - Real.log c1 = K_a := rfl
                    have h_Kr_unfold : (1 : ℝ) - Real.log r1 = K_r := rfl
                    rw [h_Ka_unfold, h_Kr_unfold] at h_eq
                    have h_Kouter_unfold : Real.exp K_a - Real.log K_r = K_outer := rfl
                    rw [h_Kouter_unfold] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                    rw [h_sum] at h_eq
                    have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                      by linarith [le_abs_self (Real.log K_outer)]
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  · exact absurd hk (by omega)
                | var l =>
                  -- (kids_r 0 = var k, kids_r 1 = var l). 4 (k, l) sub-cases.
                  let K_a : ℝ := Real.exp c0 - Real.log c1
                  rcases k with ⟨_ | _ | _, hk⟩
                  · rcases l with ⟨_ | _ | _, hl⟩
                    · -- (k=0, l=0): same-var at 0. v 0 = 0 ⇒ exp 0 - log 0 = 1.
                      -- K_outer = exp K_a. K-bound on v 1.
                      let K_outer : ℝ := Real.exp K_a
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_r, h_kr0_cc, h_kr1_vk] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vk : v ⟨0, hk⟩ = 0 := by simp [v]
                      rw [h_vk] at h_eq
                      simp only [Real.exp_zero, Real.log_zero, sub_zero, Real.log_one] at h_eq
                      have h_Ka_unfold : Real.exp c0 - Real.log c1 = K_a := rfl
                      rw [h_Ka_unfold] at h_eq
                      have h_Kouter_unfold : Real.exp K_a = K_outer := rfl
                      rw [h_Kouter_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                        by linarith [le_abs_self (Real.log K_outer)]
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · -- (k=0, l=1): cross. v = (-(|K_a|+2), 0). Use |a|+2 helper.
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then -(|K_a| + 2) else 0
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_r, h_kr0_cc, h_kr1_vk] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vk : v ⟨0, hk⟩ = -(|K_a| + 2) := by simp [v]
                      have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                      rw [h_vk, h_vl] at h_eq
                      simp only [Real.log_zero, sub_zero] at h_eq
                      rw [Real.log_exp] at h_eq
                      -- h_eq: exp((kids 0).eval v) - log(exp K_a - (-(|K_a|+2))) = v 0 + v 1
                      have h_simp : Real.exp K_a - -(|K_a| + 2) = Real.exp K_a + |K_a| + 2 := by
                        ring
                      have h_Ka_unfold : Real.exp c0 - Real.log c1 = K_a := rfl
                      rw [h_Ka_unfold, h_simp] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|K_a| + 2) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_log_bound : Real.log (Real.exp K_a + |K_a| + 2) ≤ |K_a| + 2 :=
                        log_exp_a_plus_abs_a_plus_two_le K_a
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · exact absurd hl (by omega)
                  · rcases l with ⟨_ | _ | _, hl⟩
                    · -- (k=1, l=0): cross. v = (0, -(|K_a|+2)).
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then 0 else -(|K_a| + 2)
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_r, h_kr0_cc, h_kr1_vk] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vk : v ⟨0 + 1, hk⟩ = -(|K_a| + 2) := by simp [v]
                      have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                      rw [h_vk, h_vl] at h_eq
                      simp only [Real.log_zero, sub_zero] at h_eq
                      rw [Real.log_exp] at h_eq
                      have h_simp : Real.exp K_a - -(|K_a| + 2) = Real.exp K_a + |K_a| + 2 := by
                        ring
                      have h_Ka_unfold : Real.exp c0 - Real.log c1 = K_a := rfl
                      rw [h_Ka_unfold, h_simp] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|K_a| + 2) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_log_bound : Real.log (Real.exp K_a + |K_a| + 2) ≤ |K_a| + 2 :=
                        log_exp_a_plus_abs_a_plus_two_le K_a
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · -- (k=1, l=1): same-var at 1. v 1 = 0. K_outer = exp K_a.
                      let K_outer : ℝ := Real.exp K_a
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_r, h_kr0_cc, h_kr1_vk] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vk : v ⟨0 + 1, hk⟩ = 0 := by simp [v]
                      rw [h_vk] at h_eq
                      simp only [Real.exp_zero, Real.log_zero, sub_zero, Real.log_one] at h_eq
                      have h_Ka_unfold : Real.exp c0 - Real.log c1 = K_a := rfl
                      rw [h_Ka_unfold] at h_eq
                      have h_Kouter_unfold : Real.exp K_a = K_outer := rfl
                      rw [h_Kouter_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                        by linarith [le_abs_self (Real.log K_outer)]
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · exact absurd hl (by omega)
                  · exact absurd hk (by omega)
                | app op_d kids_d =>
                  -- Depth contra: kids_r 1 = .app.
                  exfalso
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids i).depth) ≤ 3 at hd
                  have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                    have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids i).depth) :=
                      Finset.le_sup (f := fun i => (kids i).depth)
                        (Finset.mem_univ
                          (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k1] at h1
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids' i).depth) ≤ 2 at h1
                  have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                    have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids' i).depth) :=
                      Finset.le_sup (f := fun i => (kids' i).depth)
                        (Finset.mem_univ
                          (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k1'1'] at h2
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids_r i).depth) ≤ 1 at h2
                  have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                    have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids_r i).depth) :=
                      Finset.le_sup (f := fun i => (kids_r i).depth)
                        (Finset.mem_univ
                          (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_kr1_vk] at h3
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity op_d))).sup
                             (fun i => (kids_d i).depth) ≤ 0 at h3
                  omega
              | app op_d kids_d =>
                -- Depth contra: kids_r 0 = .app.
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 3 at hd
                have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                  have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids' i).depth) ≤ 2 at h1
                have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                  have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids' i).depth) :=
                    Finset.le_sup (f := fun i => (kids' i).depth)
                      (Finset.mem_univ
                        (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1'1'] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids_r i).depth) ≤ 1 at h2
                have h3 : (kids_r ⟨0, hkr0_lt⟩).depth ≤ 0 := by
                  have hle : (kids_r ⟨0, hkr0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids_r i).depth) :=
                    Finset.le_sup (f := fun i => (kids_r i).depth)
                      (Finset.mem_univ
                        (⟨0, hkr0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_kr0_cc] at h3
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op_d))).sup
                           (fun i => (kids_d i).depth) ≤ 0 at h3
                omega
            | var l =>
              -- (kids_a 0 = const c0, kids_a 1 = var l). (kids' 0).eval = exp c0 - log(v l).
              -- Set v_l = 0 ⇒ log 0 = 0 ⇒ (kids' 0).eval = exp c0 = K_a (const).
              -- Then case on (kids_r 0, kids_r 1).
              rcases l with ⟨_ | _ | _, hl⟩
              · -- l = 0: v_l = v_0 = 0. v_1 is the active slot.
                let K_a : ℝ := Real.exp c0
                cases h_kr0_l0 : (kids_r ⟨0, hkr0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                | const r0 =>
                  cases h_kr1_l0 : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                  | const r1 =>
                    -- All const downstream. K_outer = exp K_a - log(exp r0 - log r1). K-bound on v 1.
                    let K_r : ℝ := Real.exp r0 - Real.log r1
                    let K_outer : ℝ := Real.exp K_a - Real.log K_r
                    let v : Fin 2 → ℝ :=
                      fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                               Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_r, h_ka1_r, h_kr0_l0, h_kr1_l0] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                    rw [h_vl] at h_eq
                    simp only [Real.log_zero, sub_zero] at h_eq
                    have h_Ka_unfold : Real.exp c0 = K_a := rfl
                    have h_Kr_unfold : Real.exp r0 - Real.log r1 = K_r := rfl
                    rw [h_Ka_unfold, h_Kr_unfold] at h_eq
                    have h_Kouter_unfold : Real.exp K_a - Real.log K_r = K_outer := rfl
                    rw [h_Kouter_unfold] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                    rw [h_sum] at h_eq
                    have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                      by linarith [le_abs_self (Real.log K_outer)]
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  | var m =>
                    rcases m with ⟨_ | _ | _, hm⟩
                    · -- m = 0: v_m = v_0 = 0. log 0 = 0. (kids' 1).eval = exp r0.
                      let K_outer : ℝ := Real.exp K_a - r0
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_r, h_kr0_l0, h_kr1_l0] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                      rw [h_vl] at h_eq
                      simp only [Real.log_zero, sub_zero] at h_eq
                      rw [Real.log_exp] at h_eq
                      have h_Ka_unfold : Real.exp c0 = K_a := rfl
                      rw [h_Ka_unfold] at h_eq
                      have h_Kouter_unfold : Real.exp K_a - r0 = K_outer := rfl
                      rw [h_Kouter_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                        by linarith [le_abs_self (Real.log K_outer)]
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · -- m = 1: cross-var deep nest. Use log_triple_nest_witness K_a r0.
                      -- Witness: v 1 = -exp(exp(exp K_a + exp r0 + 100)).
                      let t_witness : ℝ :=
                        -Real.exp (Real.exp (Real.exp K_a + Real.exp r0 + 100))
                      let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else t_witness
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_r, h_kr0_l0, h_kr1_l0] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                      have h_vm : v ⟨0 + 1, hm⟩ = t_witness := by simp [v]
                      rw [h_vl, h_vm] at h_eq
                      simp only [Real.log_zero, sub_zero] at h_eq
                      -- h_eq: exp((kids 0).eval v) - log(exp(exp c0) - log(exp r0 - log t_witness)) = 0 + t_witness
                      -- t_witness uses K_a := exp c0 via let-binding, so defeq with exp(exp c0).
                      have h_sum : (v 0 + v 1 : ℝ) = t_witness := by simp [v]
                      rw [h_sum] at h_eq
                      have h_bound := log_triple_nest_witness K_a r0
                      show False
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      -- K_a := exp c0 is let-binding; defeq.
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp K_a - Real.log (Real.exp r0 -
                               Real.log t_witness)) = t_witness at h_eq
                      linarith
                    · exact absurd hm (by omega)
                  | app op_d kids_d =>
                    -- Depth contra: kids_r 1 = .app.
                    exfalso
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids i).depth) ≤ 3 at hd
                    have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                      have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids i).depth) :=
                        Finset.le_sup (f := fun i => (kids i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1] at h1
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids' i).depth) ≤ 2 at h1
                    have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                      have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids' i).depth) :=
                        Finset.le_sup (f := fun i => (kids' i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1'1'] at h2
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids_r i).depth) ≤ 1 at h2
                    have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                      have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids_r i).depth) :=
                        Finset.le_sup (f := fun i => (kids_r i).depth)
                          (Finset.mem_univ
                            (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_kr1_l0] at h3
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity op_d))).sup
                               (fun i => (kids_d i).depth) ≤ 0 at h3
                    omega
                | var k =>
                  -- (kids_a 0 = const c0, kids_a 1 = var 0, kids_r 0 = var k).
                  -- Continue enumeration on kids_r 1.
                  cases h_kr1_l0vk : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                  | const r1 =>
                    rcases k with ⟨_ | _ | _, hk⟩
                    · -- (k=0, const r1): v_k = v_0 = 0. K_r = 1 - log r1. K-bound on v 1.
                      let K_r : ℝ := 1 - Real.log r1
                      let K_outer : ℝ := Real.exp K_a - Real.log K_r
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_r, h_kr0_l0, h_kr1_l0vk] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                      -- v ⟨0, hk⟩ subsumed by h_vl via proof irrelevance.
                      rw [h_vl] at h_eq
                      simp only [Real.log_zero, sub_zero, Real.exp_zero] at h_eq
                      have h_Ka_unfold : Real.exp c0 = K_a := rfl
                      have h_Kr_unfold : (1 : ℝ) - Real.log r1 = K_r := rfl
                      rw [h_Ka_unfold, h_Kr_unfold] at h_eq
                      have h_Kouter_unfold : Real.exp K_a - Real.log K_r = K_outer := rfl
                      rw [h_Kouter_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                        by linarith [le_abs_self (Real.log K_outer)]
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · -- (k=1, const r1): analytic-friction. Apply helper #11.
                      -- v_k = v 1 (active). (kids_r 0).eval = v 1. (kids_r 1).eval = r1.
                      -- (kids' 1).eval = exp(v 1) - log r1.
                      -- Apply log_triple_nest_swap_bound K_a (Real.log r1) (v 1).
                      let v : Fin 2 → ℝ := fun i => if i = 0 then 0
                        else -Real.exp (Real.exp (Real.exp
                          (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100)))
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_r, h_kr0_l0, h_kr1_l0vk] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                      have h_vk : v ⟨0 + 1, hk⟩ = -Real.exp (Real.exp (Real.exp
                          (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100))) := by
                        simp [v]
                      rw [h_vl, h_vk] at h_eq
                      simp only [Real.log_zero, sub_zero] at h_eq
                      have h_Ka_unfold : Real.exp c0 = K_a := rfl
                      rw [h_Ka_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -Real.exp (Real.exp (Real.exp
                          (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100))) := by
                        simp [v]
                      rw [h_sum] at h_eq
                      have h_bound := log_triple_nest_swap_bound K_a (Real.log r1)
                        (-Real.exp (Real.exp (Real.exp
                          (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100))))
                        (le_refl _)
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · exact absurd hk (by omega)
                  | var k' =>
                    rcases k with ⟨_ | _ | _, hk⟩
                    · rcases k' with ⟨_ | _ | _, hk'⟩
                      · -- (k=0, k'=0): same-var at 0. K_r = exp 0 - log 0 = 1.
                        -- K_outer = exp K_a - log 1 = exp K_a.
                        let K_outer : ℝ := Real.exp K_a
                        let v : Fin 2 → ℝ :=
                          fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_r, h_kr0_l0, h_kr1_l0vk] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                        -- v ⟨0, hk⟩ and v ⟨0, hk'⟩ subsumed by h_vl via proof irrelevance.
                        rw [h_vl] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero, Real.log_one] at h_eq
                        have h_Ka_unfold : Real.exp c0 = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_Kouter_unfold : Real.exp K_a = K_outer := rfl
                        rw [h_Kouter_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                          by linarith [le_abs_self (Real.log K_outer)]
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · -- (k=0, k'=1): cross. (kids_r 0).eval = v 0 = 0. (kids_r 1).eval = v 1.
                        -- (kids' 1).eval = exp 0 - log(v 1) = 1 - log(v 1).
                        -- Apply log_triple_nest_witness K_a 0 with t = v 1.
                        let v : Fin 2 → ℝ := fun i => if i = 0 then 0
                          else -Real.exp (Real.exp (Real.exp K_a + Real.exp 0 + 100))
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_r, h_kr0_l0, h_kr1_l0vk] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                        have h_vk' : v ⟨0 + 1, hk'⟩ =
                            -Real.exp (Real.exp (Real.exp K_a + Real.exp 0 + 100)) := by
                          simp [v]
                        -- v ⟨0, hk⟩ subsumed by h_vl via proof irrelevance.
                        rw [h_vl, h_vk'] at h_eq
                        simp only [Real.log_zero, sub_zero] at h_eq
                        have h_Ka_unfold : Real.exp c0 = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) =
                            -Real.exp (Real.exp (Real.exp K_a + Real.exp 0 + 100)) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_bound := log_triple_nest_witness K_a 0
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · exact absurd hk' (by omega)
                    · rcases k' with ⟨_ | _ | _, hk'⟩
                      · -- (k=1, k'=0): (kids_r 0).eval = v 1 (active). (kids_r 1).eval = 0.
                        -- (kids' 1).eval = exp(v 1) - log 0 = exp(v 1). log(exp(v 1)) = v 1.
                        -- K_outer = exp K_a - v 1. v 1 = -(|K_a|+2).
                        let v : Fin 2 → ℝ :=
                          fun i => if i = 0 then 0 else -(|K_a| + 2)
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_r, h_kr0_l0, h_kr1_l0vk] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                        have h_vk : v ⟨0 + 1, hk⟩ = -(|K_a| + 2) := by simp [v]
                        -- v ⟨0, hk'⟩ subsumed by h_vl via proof irrelevance.
                        rw [h_vl, h_vk] at h_eq
                        simp only [Real.log_zero, sub_zero] at h_eq
                        rw [Real.log_exp] at h_eq
                        have h_Ka_unfold : Real.exp c0 = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_simp : Real.exp K_a - -(|K_a| + 2) =
                                      Real.exp K_a + |K_a| + 2 := by ring
                        rw [h_simp] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -(|K_a| + 2) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_log_bound : Real.log (Real.exp K_a + |K_a| + 2) ≤ |K_a| + 2 :=
                          log_exp_a_plus_abs_a_plus_two_le K_a
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · -- (k=1, k'=1): same-var at v 1. Apply log_triple_nest_same_var_bound K_a.
                        let v : Fin 2 → ℝ := fun i => if i = 0 then 0
                          else -Real.exp (Real.exp (Real.exp (|K_a| + 100)))
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_r, h_kr0_l0, h_kr1_l0vk] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vl : v ⟨0, hl⟩ = 0 := by simp [v]
                        have h_vk : v ⟨0 + 1, hk⟩ =
                            -Real.exp (Real.exp (Real.exp (|K_a| + 100))) := by simp [v]
                        -- v ⟨0 + 1, hk'⟩ subsumed by h_vk via proof irrelevance.
                        rw [h_vl, h_vk] at h_eq
                        simp only [Real.log_zero, sub_zero] at h_eq
                        have h_Ka_unfold : Real.exp c0 = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) =
                            -Real.exp (Real.exp (Real.exp (|K_a| + 100))) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_bound := log_triple_nest_same_var_bound K_a
                          (-Real.exp (Real.exp (Real.exp (|K_a| + 100)))) (le_refl _)
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · exact absurd hk' (by omega)
                    · exact absurd hk (by omega)
                  | app op_d kids_d =>
                    -- Depth contra: kids_r 1 = .app.
                    exfalso
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids i).depth) ≤ 3 at hd
                    have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                      have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids i).depth) :=
                        Finset.le_sup (f := fun i => (kids i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1] at h1
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids' i).depth) ≤ 2 at h1
                    have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                      have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids' i).depth) :=
                        Finset.le_sup (f := fun i => (kids' i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1'1'] at h2
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids_r i).depth) ≤ 1 at h2
                    have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                      have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids_r i).depth) :=
                        Finset.le_sup (f := fun i => (kids_r i).depth)
                          (Finset.mem_univ
                            (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_kr1_l0vk] at h3
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity op_d))).sup
                               (fun i => (kids_d i).depth) ≤ 0 at h3
                    omega
                | app op_d kids_d =>
                  -- Depth contra: kids_r 0 = .app.
                  exfalso
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids i).depth) ≤ 3 at hd
                  have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                    have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids i).depth) :=
                      Finset.le_sup (f := fun i => (kids i).depth)
                        (Finset.mem_univ
                          (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k1] at h1
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids' i).depth) ≤ 2 at h1
                  have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                    have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids' i).depth) :=
                      Finset.le_sup (f := fun i => (kids' i).depth)
                        (Finset.mem_univ
                          (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k1'1'] at h2
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids_r i).depth) ≤ 1 at h2
                  have h3 : (kids_r ⟨0, hkr0_lt⟩).depth ≤ 0 := by
                    have hle : (kids_r ⟨0, hkr0_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids_r i).depth) :=
                      Finset.le_sup (f := fun i => (kids_r i).depth)
                        (Finset.mem_univ
                          (⟨0, hkr0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_kr0_l0] at h3
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity op_d))).sup
                             (fun i => (kids_d i).depth) ≤ 0 at h3
                  omega
              · -- l = 1: v_l = v_1 = 0. v_0 is active. Mirror of l = 0.
                let K_a : ℝ := Real.exp c0
                cases h_kr0_l1 : (kids_r ⟨0, hkr0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                | const r0 =>
                  cases h_kr1_l1 : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                  | const r1 =>
                    -- All const. K_r = exp r0 - log r1. K-bound on v 0.
                    let K_r : ℝ := Real.exp r0 - Real.log r1
                    let K_outer : ℝ := Real.exp K_a - Real.log K_r
                    let v : Fin 2 → ℝ :=
                      fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                               Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_r, h_ka1_r, h_kr0_l1, h_kr1_l1] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                    rw [h_vl] at h_eq
                    simp only [Real.log_zero, sub_zero] at h_eq
                    have h_Ka_unfold : Real.exp c0 = K_a := rfl
                    have h_Kr_unfold : Real.exp r0 - Real.log r1 = K_r := rfl
                    rw [h_Ka_unfold, h_Kr_unfold] at h_eq
                    have h_Kouter_unfold : Real.exp K_a - Real.log K_r = K_outer := rfl
                    rw [h_Kouter_unfold] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                    rw [h_sum] at h_eq
                    have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                      by linarith [le_abs_self (Real.log K_outer)]
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  | var m =>
                    rcases m with ⟨_ | _ | _, hm⟩
                    · -- m = 0: v_m = v_0 (active). (kids' 1).eval = exp r0 - log(v_0).
                      -- Mirror of l=0 m=1: use log_triple_nest_witness K_a r0.
                      let v : Fin 2 → ℝ := fun i => if i = 0
                        then -Real.exp (Real.exp (Real.exp K_a + Real.exp r0 + 100))
                        else 0
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_r, h_kr0_l1, h_kr1_l1] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                      have h_vm : v ⟨0, hm⟩ =
                          -Real.exp (Real.exp (Real.exp K_a + Real.exp r0 + 100)) := by simp [v]
                      rw [h_vl, h_vm] at h_eq
                      simp only [Real.log_zero, sub_zero] at h_eq
                      have h_Ka_unfold : Real.exp c0 = K_a := rfl
                      rw [h_Ka_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) =
                          -Real.exp (Real.exp (Real.exp K_a + Real.exp r0 + 100)) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_bound := log_triple_nest_witness K_a r0
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · -- m = 1: v_m = v_1 = 0. (kids' 1).eval = exp r0 - log 0 = exp r0.
                      -- K_outer = exp K_a - r0.
                      let K_outer : ℝ := Real.exp K_a - r0
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_r, h_kr0_l1, h_kr1_l1] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                      rw [h_vl] at h_eq
                      simp only [Real.log_zero, sub_zero] at h_eq
                      rw [Real.log_exp] at h_eq
                      have h_Ka_unfold : Real.exp c0 = K_a := rfl
                      rw [h_Ka_unfold] at h_eq
                      have h_Kouter_unfold : Real.exp K_a - r0 = K_outer := rfl
                      rw [h_Kouter_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                        by linarith [le_abs_self (Real.log K_outer)]
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · exact absurd hm (by omega)
                  | app op_d kids_d =>
                    -- Depth contra: kids_r 1 = .app.
                    exfalso
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids i).depth) ≤ 3 at hd
                    have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                      have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids i).depth) :=
                        Finset.le_sup (f := fun i => (kids i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1] at h1
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids' i).depth) ≤ 2 at h1
                    have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                      have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids' i).depth) :=
                        Finset.le_sup (f := fun i => (kids' i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1'1'] at h2
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids_r i).depth) ≤ 1 at h2
                    have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                      have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids_r i).depth) :=
                        Finset.le_sup (f := fun i => (kids_r i).depth)
                          (Finset.mem_univ
                            (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_kr1_l1] at h3
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity op_d))).sup
                               (fun i => (kids_d i).depth) ≤ 0 at h3
                    omega
                | var k =>
                  -- (kids_a 0 = const c0, kids_a 1 = var 1, kids_r 0 = var k).
                  -- Mirror of 5683 (l=0) but with v_0/v_1 swap.
                  cases h_kr1_l1vk : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                  | const r1 =>
                    rcases k with ⟨_ | _ | _, hk⟩
                    · -- (k=0, const r1): v_k = v_0 (active). Apply helper #11 (mirror).
                      let v : Fin 2 → ℝ := fun i => if i = 0
                        then -Real.exp (Real.exp (Real.exp
                          (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100)))
                        else 0
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_r, h_kr0_l1, h_kr1_l1vk] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                      have h_vk : v ⟨0, hk⟩ = -Real.exp (Real.exp (Real.exp
                          (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100))) := by
                        simp [v]
                      rw [h_vl, h_vk] at h_eq
                      simp only [Real.log_zero, sub_zero] at h_eq
                      have h_Ka_unfold : Real.exp c0 = K_a := rfl
                      rw [h_Ka_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -Real.exp (Real.exp (Real.exp
                          (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100))) := by
                        simp [v]
                      rw [h_sum] at h_eq
                      have h_bound := log_triple_nest_swap_bound K_a (Real.log r1)
                        (-Real.exp (Real.exp (Real.exp
                          (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100))))
                        (le_refl _)
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · -- (k=1, const r1): v_k = v_1 = 0. K_r = 1 - log r1. K-bound on v 0.
                      let K_r : ℝ := 1 - Real.log r1
                      let K_outer : ℝ := Real.exp K_a - Real.log K_r
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_r, h_kr0_l1, h_kr1_l1vk] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                      -- v ⟨0 + 1, hk⟩ subsumed by h_vl via proof irrelevance.
                      rw [h_vl] at h_eq
                      simp only [Real.log_zero, sub_zero, Real.exp_zero] at h_eq
                      have h_Ka_unfold : Real.exp c0 = K_a := rfl
                      have h_Kr_unfold : (1 : ℝ) - Real.log r1 = K_r := rfl
                      rw [h_Ka_unfold, h_Kr_unfold] at h_eq
                      have h_Kouter_unfold : Real.exp K_a - Real.log K_r = K_outer := rfl
                      rw [h_Kouter_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                        by linarith [le_abs_self (Real.log K_outer)]
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · exact absurd hk (by omega)
                  | var k' =>
                    rcases k with ⟨_ | _ | _, hk⟩
                    · rcases k' with ⟨_ | _ | _, hk'⟩
                      · -- (k=0, k'=0): same-var at v 0 (active). Use log_triple_nest_same_var_bound K_a.
                        let v : Fin 2 → ℝ := fun i => if i = 0
                          then -Real.exp (Real.exp (Real.exp (|K_a| + 100)))
                          else 0
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_r, h_kr0_l1, h_kr1_l1vk] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                        have h_vk : v ⟨0, hk⟩ =
                            -Real.exp (Real.exp (Real.exp (|K_a| + 100))) := by simp [v]
                        -- v ⟨0, hk'⟩ subsumed by h_vk via proof irrelevance.
                        rw [h_vl, h_vk] at h_eq
                        simp only [Real.log_zero, sub_zero] at h_eq
                        have h_Ka_unfold : Real.exp c0 = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) =
                            -Real.exp (Real.exp (Real.exp (|K_a| + 100))) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_bound := log_triple_nest_same_var_bound K_a
                          (-Real.exp (Real.exp (Real.exp (|K_a| + 100)))) (le_refl _)
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · -- (k=0, k'=1): cross. v_k = v_0 (active), v_k' = v_1 = 0.
                        -- (kids_r 1).eval = 0. (kids' 1).eval = exp(v_0) - 0 = exp(v_0).
                        -- log(exp(v_0)) = v_0. K_outer = exp K_a - v_0.
                        -- For v 0 = -(|K_a|+2): exp K_a + |K_a|+2. log ≤ |K_a|+2.
                        let v : Fin 2 → ℝ :=
                          fun i => if i = 0 then -(|K_a| + 2) else 0
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_r, h_kr0_l1, h_kr1_l1vk] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                        have h_vk : v ⟨0, hk⟩ = -(|K_a| + 2) := by simp [v]
                        -- v ⟨0 + 1, hk'⟩ subsumed by h_vl via proof irrelevance.
                        rw [h_vl, h_vk] at h_eq
                        simp only [Real.log_zero, sub_zero] at h_eq
                        rw [Real.log_exp] at h_eq
                        have h_Ka_unfold : Real.exp c0 = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_simp : Real.exp K_a - -(|K_a| + 2) =
                                      Real.exp K_a + |K_a| + 2 := by ring
                        rw [h_simp] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -(|K_a| + 2) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_log_bound : Real.log (Real.exp K_a + |K_a| + 2) ≤ |K_a| + 2 :=
                          log_exp_a_plus_abs_a_plus_two_le K_a
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · exact absurd hk' (by omega)
                    · rcases k' with ⟨_ | _ | _, hk'⟩
                      · -- (k=1, k'=0): cross. v_k = v_1 = 0, v_k' = v_0 (active).
                        -- (kids_r 0).eval = 0, (kids_r 1).eval = v_0.
                        -- (kids' 1).eval = exp(0) - log(v_0) = 1 - log(v_0).
                        -- Apply log_triple_nest_witness K_a 0 (active variable inside log).
                        let v : Fin 2 → ℝ := fun i => if i = 0
                          then -Real.exp (Real.exp (Real.exp K_a + Real.exp 0 + 100))
                          else 0
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_r, h_kr0_l1, h_kr1_l1vk] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                        have h_vk' : v ⟨0, hk'⟩ =
                            -Real.exp (Real.exp (Real.exp K_a + Real.exp 0 + 100)) := by
                          simp [v]
                        -- v ⟨0 + 1, hk⟩ subsumed by h_vl via proof irrelevance.
                        rw [h_vl, h_vk'] at h_eq
                        simp only [Real.log_zero, sub_zero] at h_eq
                        have h_Ka_unfold : Real.exp c0 = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) =
                            -Real.exp (Real.exp (Real.exp K_a + Real.exp 0 + 100)) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_bound := log_triple_nest_witness K_a 0
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · -- (k=1, k'=1): same-var at v 1 = 0. K_r' = 1 - log 0 = 1.
                        -- K_outer = exp K_a - log 1 = exp K_a. K-bound on v 0.
                        let K_outer : ℝ := Real.exp K_a
                        let v : Fin 2 → ℝ :=
                          fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_r, h_kr0_l1, h_kr1_l1vk] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vl : v ⟨0 + 1, hl⟩ = 0 := by simp [v]
                        -- v ⟨0 + 1, hk⟩ and v ⟨0 + 1, hk'⟩ subsumed by h_vl via proof irrelevance.
                        rw [h_vl] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero, Real.log_one] at h_eq
                        have h_Ka_unfold : Real.exp c0 = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_Kouter_unfold : Real.exp K_a = K_outer := rfl
                        rw [h_Kouter_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                          by linarith [le_abs_self (Real.log K_outer)]
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · exact absurd hk' (by omega)
                    · exact absurd hk (by omega)
                  | app op_d kids_d =>
                    -- Depth contra: kids_r 1 = .app.
                    exfalso
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids i).depth) ≤ 3 at hd
                    have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                      have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids i).depth) :=
                        Finset.le_sup (f := fun i => (kids i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1] at h1
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids' i).depth) ≤ 2 at h1
                    have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                      have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids' i).depth) :=
                        Finset.le_sup (f := fun i => (kids' i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1'1'] at h2
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids_r i).depth) ≤ 1 at h2
                    have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                      have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids_r i).depth) :=
                        Finset.le_sup (f := fun i => (kids_r i).depth)
                          (Finset.mem_univ
                            (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_kr1_l1vk] at h3
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity op_d))).sup
                               (fun i => (kids_d i).depth) ≤ 0 at h3
                    omega
                | app op_d kids_d =>
                  -- Depth contra: kids_r 0 = .app.
                  exfalso
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids i).depth) ≤ 3 at hd
                  have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                    have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids i).depth) :=
                      Finset.le_sup (f := fun i => (kids i).depth)
                        (Finset.mem_univ
                          (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k1] at h1
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids' i).depth) ≤ 2 at h1
                  have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                    have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids' i).depth) :=
                      Finset.le_sup (f := fun i => (kids' i).depth)
                        (Finset.mem_univ
                          (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k1'1'] at h2
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids_r i).depth) ≤ 1 at h2
                  have h3 : (kids_r ⟨0, hkr0_lt⟩).depth ≤ 0 := by
                    have hle : (kids_r ⟨0, hkr0_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids_r i).depth) :=
                      Finset.le_sup (f := fun i => (kids_r i).depth)
                        (Finset.mem_univ
                          (⟨0, hkr0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_kr0_l1] at h3
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity op_d))).sup
                             (fun i => (kids_d i).depth) ≤ 0 at h3
                  omega
              · exact absurd hl (by omega)
            | app op_d kids_d =>
              -- Depth contra: kids_a 1 = .app.
              exfalso
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids i).depth) ≤ 3 at hd
              have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids i).depth) :=
                  Finset.le_sup (f := fun i => (kids i).depth)
                    (Finset.mem_univ
                      (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1] at h1
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids' i).depth) ≤ 2 at h1
              have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
                have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids' i).depth) :=
                  Finset.le_sup (f := fun i => (kids' i).depth)
                    (Finset.mem_univ
                      (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_k1'0] at h2
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                         (fun i => (kids_a i).depth) ≤ 1 at h2
              have h3 : (kids_a ⟨1, hka1_lt⟩).depth ≤ 0 := by
                have hle : (kids_a ⟨1, hka1_lt⟩).depth ≤
                    (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                      (fun i => (kids_a i).depth) :=
                  Finset.le_sup (f := fun i => (kids_a i).depth)
                    (Finset.mem_univ
                      (⟨1, hka1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                omega
              rw [h_ka1_r] at h3
              change 1 + (Finset.univ :
                  Finset (Fin (EmlBasis.arity op_d))).sup
                         (fun i => (kids_d i).depth) ≤ 0 at h3
              omega
          | var j =>
            -- kids_a 0 = var j. Case on kids_a 1, then kids_r 0, kids_r 1.
            -- (kids' 0).eval v = exp(v j) - log((kids_a 1).eval v).
            rcases j with ⟨_ | _ | _, hj⟩
            · -- j = 0
              cases h_ka1_vj : (kids_a ⟨1, hka1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
              | const c1 =>
                -- (j=0, kids_a 1 = const c1). v_j = v_0 = 0 ⇒ (kids' 0).eval = 1 - log c1 = K_a'.
                -- Then case on (kids_r 0, kids_r 1).
                let K_a' : ℝ := 1 - Real.log c1
                cases h_kr0_j0c1 : (kids_r ⟨0, hkr0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                | const r0 =>
                  cases h_kr1_j0c1 : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                  | const r1 =>
                    -- All-const: K_outer = exp K_a' - log(exp r0 - log r1).
                    let K_r : ℝ := Real.exp r0 - Real.log r1
                    let K_outer : ℝ := Real.exp K_a' - Real.log K_r
                    let v : Fin 2 → ℝ :=
                      fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                               Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_r, h_ka1_vj, h_kr0_j0c1, h_kr1_j0c1] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                    rw [h_vj, Real.exp_zero] at h_eq
                    have h_Ka'_unfold : (1 : ℝ) - Real.log c1 = K_a' := rfl
                    have h_Kr_unfold : Real.exp r0 - Real.log r1 = K_r := rfl
                    rw [h_Ka'_unfold, h_Kr_unfold] at h_eq
                    have h_Kouter_unfold : Real.exp K_a' - Real.log K_r = K_outer := rfl
                    rw [h_Kouter_unfold] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                    rw [h_sum] at h_eq
                    have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                      by linarith [le_abs_self (Real.log K_outer)]
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  | var n =>
                    rcases n with ⟨_ | _ | _, hn⟩
                    · -- (j=0, c1, const r0, var 0): v_n = v_0 = 0, log 0 = 0.
                      -- (kids' 1).eval = exp r0. (kids 1).eval = exp K_a' - r0 = K_outer.
                      let K_outer : ℝ := Real.exp K_a' - r0
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj, h_kr0_j0c1, h_kr1_j0c1] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                      rw [h_vj, Real.exp_zero] at h_eq
                      simp only [Real.log_zero, sub_zero] at h_eq
                      rw [Real.log_exp] at h_eq
                      have h_Ka'_unfold : (1 : ℝ) - Real.log c1 = K_a' := rfl
                      rw [h_Ka'_unfold] at h_eq
                      have h_Kouter_unfold : Real.exp K_a' - r0 = K_outer := rfl
                      rw [h_Kouter_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                        by linarith [le_abs_self (Real.log K_outer)]
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · -- (j=0, c1, const r0, var 1): deep-nest, apply helper #9.
                      -- (kids' 1).eval = exp r0 - log(v 1). Use log_triple_nest_witness K_a' r0.
                      let t_witness : ℝ :=
                        -Real.exp (Real.exp (Real.exp K_a' + Real.exp r0 + 100))
                      let v : Fin 2 → ℝ := fun i => if i = 0 then 0 else t_witness
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj, h_kr0_j0c1, h_kr1_j0c1] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                      have h_vn : v ⟨0 + 1, hn⟩ = t_witness := by simp [v]
                      rw [h_vj, h_vn, Real.exp_zero] at h_eq
                      -- h_eq: exp((kids 0).eval v) - log(exp (1 - log c1) - log(exp r0 - log t_witness)) = v 0 + v 1
                      -- K_a' := 1 - log c1 (defeq via let). Change to use K_a' form.
                      have h_sum : (v 0 + v 1 : ℝ) = t_witness := by simp [v]
                      rw [h_sum] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp K_a' - Real.log (Real.exp r0 -
                               Real.log t_witness)) = t_witness at h_eq
                      have h_bound := log_triple_nest_witness K_a' r0
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · exact absurd hn (by omega)
                  | app op_d kids_d =>
                    exfalso
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids i).depth) ≤ 3 at hd
                    have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                      have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids i).depth) :=
                        Finset.le_sup (f := fun i => (kids i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1] at h1
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids' i).depth) ≤ 2 at h1
                    have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                      have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids' i).depth) :=
                        Finset.le_sup (f := fun i => (kids' i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1'1'] at h2
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids_r i).depth) ≤ 1 at h2
                    have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                      have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids_r i).depth) :=
                        Finset.le_sup (f := fun i => (kids_r i).depth)
                          (Finset.mem_univ
                            (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_kr1_j0c1] at h3
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity op_d))).sup
                               (fun i => (kids_d i).depth) ≤ 0 at h3
                    omega
                | var m =>
                  -- (j=0, c1, var m, ?). Continue on kids_r 1.
                  cases h_kr1_jvm : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                  | const r1 =>
                    rcases m with ⟨_ | _ | _, hm⟩
                    · -- (j=0, c1, var 0, const r1): v_m = v_0 = 0. K-bound on K_outer.
                      let K_r' : ℝ := 1 - Real.log r1
                      let K_outer : ℝ := Real.exp K_a' - Real.log K_r'
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj, h_kr0_j0c1, h_kr1_jvm] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                      rw [h_vj, Real.exp_zero] at h_eq
                      have h_Ka'_unfold : (1 : ℝ) - Real.log c1 = K_a' := rfl
                      have h_Kr'_unfold : (1 : ℝ) - Real.log r1 = K_r' := rfl
                      rw [h_Ka'_unfold, h_Kr'_unfold] at h_eq
                      have h_Kouter_unfold : Real.exp K_a' - Real.log K_r' = K_outer := rfl
                      rw [h_Kouter_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                        by linarith [le_abs_self (Real.log K_outer)]
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · -- (j=0, c1, var 1, const r1): v_m = v 1 (active). Apply helper #11.
                      let v : Fin 2 → ℝ := fun i => if i = 0 then 0
                        else -Real.exp (Real.exp (Real.exp
                          (|K_a'| + |Real.log r1| + |Real.log (Real.log r1)| + 100)))
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj, h_kr0_j0c1, h_kr1_jvm] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                      have h_vm : v ⟨0 + 1, hm⟩ = -Real.exp (Real.exp (Real.exp
                          (|K_a'| + |Real.log r1| + |Real.log (Real.log r1)| + 100))) := by
                        simp [v]
                      rw [h_vj, h_vm, Real.exp_zero] at h_eq
                      have h_Ka'_unfold : (1 : ℝ) - Real.log c1 = K_a' := rfl
                      rw [h_Ka'_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -Real.exp (Real.exp (Real.exp
                          (|K_a'| + |Real.log r1| + |Real.log (Real.log r1)| + 100))) := by
                        simp [v]
                      rw [h_sum] at h_eq
                      have h_bound := log_triple_nest_swap_bound K_a' (Real.log r1)
                        (-Real.exp (Real.exp (Real.exp
                          (|K_a'| + |Real.log r1| + |Real.log (Real.log r1)| + 100))))
                        (le_refl _)
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · exact absurd hm (by omega)
                  | var n =>
                    rcases m with ⟨_ | _ | _, hm⟩
                    · rcases n with ⟨_ | _ | _, hn⟩
                      · -- (m=0, n=0): v_m = v_n = v_0 = 0. K_outer = exp K_a'.
                        let K_outer : ℝ := Real.exp K_a'
                        let v : Fin 2 → ℝ :=
                          fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj, h_kr0_j0c1, h_kr1_jvm] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                        rw [h_vj] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero, Real.log_one] at h_eq
                        have h_Ka'_unfold : (1 : ℝ) - Real.log c1 = K_a' := rfl
                        rw [h_Ka'_unfold] at h_eq
                        have h_Kouter_unfold : Real.exp K_a' = K_outer := rfl
                        rw [h_Kouter_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                          by linarith [le_abs_self (Real.log K_outer)]
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · -- (m=0, n=1): cross-var. Apply helper #9 (K=K_a', r=0).
                        -- t_witness inline to avoid let-binding opacity vs helper unfold.
                        let v : Fin 2 → ℝ := fun i => if i = 0 then 0
                          else -Real.exp (Real.exp (Real.exp K_a' + Real.exp 0 + 100))
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj, h_kr0_j0c1, h_kr1_jvm] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                        have h_vn : v ⟨0 + 1, hn⟩ =
                            -Real.exp (Real.exp (Real.exp K_a' + Real.exp 0 + 100)) := by
                          simp [v]
                        rw [h_vj, h_vn] at h_eq
                        -- Convert Real.exp 0 → 1 in h_eq to align K_a' = 1 - log c1.
                        have h_exp_0 : Real.exp (0 : ℝ) = 1 := Real.exp_zero
                        -- Only rewrite the inner-most Real.exp 0 used in the K_a' position.
                        -- Use show to align via defeq once Real.exp 0 = 1 applied.
                        have h_sum : (v 0 + v 1 : ℝ) =
                            -Real.exp (Real.exp (Real.exp K_a' + Real.exp 0 + 100)) := by
                          simp [v]
                        rw [h_sum] at h_eq
                        have h_bound := log_triple_nest_witness K_a' 0
                        -- Both h_eq and h_bound have the SAME Real.exp 0 occurrences.
                        -- The K_a' in h_bound is `Real.exp K_a'`. In h_eq, it's `Real.exp (Real.exp 0 - Real.log c1)`.
                        -- Use conv + show to align via Real.exp_zero.
                        rw [show Real.exp (Real.exp 0 - Real.log c1) = Real.exp K_a' by
                            rw [Real.exp_zero]] at h_eq
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · exact absurd hn (by omega)
                    · rcases n with ⟨_ | _ | _, hn⟩
                      · -- (m=1, n=0): v_m = v_1 (active), v_n = v_0 = 0.
                        -- (kids' 1).eval = exp(v_1) - 0 = exp(v_1).
                        -- (kids 1).eval = exp K_a' - log(exp v_1) = exp K_a' - v_1.
                        -- At v 1 = -(|K_a'|+2): exp K_a' + |K_a'| + 2. log ≤ |K_a'|+2.
                        let v : Fin 2 → ℝ :=
                          fun i => if i = 0 then 0 else -(|K_a'| + 2)
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj, h_kr0_j0c1, h_kr1_jvm] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                        have h_vm : v ⟨0 + 1, hm⟩ = -(|K_a'| + 2) := by simp [v]
                        rw [h_vj, h_vm] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                        rw [Real.log_exp] at h_eq
                        have h_Ka'_unfold : (1 : ℝ) - Real.log c1 = K_a' := rfl
                        rw [h_Ka'_unfold] at h_eq
                        have h_simp : Real.exp K_a' - -(|K_a'| + 2) =
                                      Real.exp K_a' + |K_a'| + 2 := by ring
                        rw [h_simp] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -(|K_a'| + 2) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_log_bound : Real.log (Real.exp K_a' + |K_a'| + 2) ≤ |K_a'| + 2 :=
                          log_exp_a_plus_abs_a_plus_two_le K_a'
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · -- (m=1, n=1) same-var deep-nest. Apply helper #10.
                        let v : Fin 2 → ℝ := fun i => if i = 0 then 0
                          else -Real.exp (Real.exp (Real.exp (|K_a'| + 100)))
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj, h_kr0_j0c1, h_kr1_jvm] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                        have h_vm : v ⟨0 + 1, hm⟩ =
                            -Real.exp (Real.exp (Real.exp (|K_a'| + 100))) := by simp [v]
                        rw [h_vj, h_vm] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) =
                            -Real.exp (Real.exp (Real.exp (|K_a'| + 100))) := by simp [v]
                        rw [h_sum] at h_eq
                        rw [show Real.exp (Real.exp 0 - Real.log c1) = Real.exp K_a' by
                            rw [Real.exp_zero]] at h_eq
                        have h_bound := log_triple_nest_same_var_bound K_a'
                          (-Real.exp (Real.exp (Real.exp (|K_a'| + 100)))) (le_refl _)
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · exact absurd hn (by omega)
                    · exact absurd hm (by omega)
                  | app op_d kids_d =>
                    -- Depth contra: kids_r 1 = .app.
                    exfalso
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids i).depth) ≤ 3 at hd
                    have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                      have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids i).depth) :=
                        Finset.le_sup (f := fun i => (kids i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1] at h1
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids' i).depth) ≤ 2 at h1
                    have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                      have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids' i).depth) :=
                        Finset.le_sup (f := fun i => (kids' i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1'1'] at h2
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids_r i).depth) ≤ 1 at h2
                    have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                      have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids_r i).depth) :=
                        Finset.le_sup (f := fun i => (kids_r i).depth)
                          (Finset.mem_univ
                            (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_kr1_jvm] at h3
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity op_d))).sup
                               (fun i => (kids_d i).depth) ≤ 0 at h3
                    omega
                | app op_d kids_d =>
                  -- Depth contra: kids_r 0 = .app.
                  exfalso
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids i).depth) ≤ 3 at hd
                  have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                    have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids i).depth) :=
                      Finset.le_sup (f := fun i => (kids i).depth)
                        (Finset.mem_univ
                          (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k1] at h1
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids' i).depth) ≤ 2 at h1
                  have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                    have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids' i).depth) :=
                      Finset.le_sup (f := fun i => (kids' i).depth)
                        (Finset.mem_univ
                          (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k1'1'] at h2
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids_r i).depth) ≤ 1 at h2
                  have h3 : (kids_r ⟨0, hkr0_lt⟩).depth ≤ 0 := by
                    have hle : (kids_r ⟨0, hkr0_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids_r i).depth) :=
                      Finset.le_sup (f := fun i => (kids_r i).depth)
                        (Finset.mem_univ
                          (⟨0, hkr0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_kr0_j0c1] at h3
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity op_d))).sup
                             (fun i => (kids_d i).depth) ≤ 0 at h3
                  omega
              | var l =>
                rcases l with ⟨_ | _ | _, hl⟩
                · -- l = 0: kids_a 0 = var 0 = kids_a 1. Same-var. v_0 = 0 ⇒ (kids' 0).eval = 1.
                  -- K_a := 1. Active variable v_1. Template-replicates from 5683 with K_a = 1.
                  let K_a : ℝ := 1
                  cases h_kr0_jvl0 : (kids_r ⟨0, hkr0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                  | const r0 =>
                    cases h_kr1_jvl0 : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                    | const r1 =>
                      -- All const. K_r = exp r0 - log r1. K-bound on v 1.
                      let K_r : ℝ := Real.exp r0 - Real.log r1
                      let K_outer : ℝ := Real.exp K_a - Real.log K_r
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj, h_kr0_jvl0, h_kr1_jvl0] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                      rw [h_vj] at h_eq
                      simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                      have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                      rw [h_Ka_unfold] at h_eq
                      have h_Kr_unfold : Real.exp r0 - Real.log r1 = K_r := rfl
                      rw [h_Kr_unfold] at h_eq
                      have h_Kouter_unfold : Real.exp K_a - Real.log K_r = K_outer := rfl
                      rw [h_Kouter_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                        by linarith [le_abs_self (Real.log K_outer)]
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    | var m =>
                      rcases m with ⟨_ | _ | _, hm⟩
                      · -- (const r0, var m=0): v_m = v_0 = 0. K_outer = exp K_a - r0.
                        let K_outer : ℝ := Real.exp K_a - r0
                        let v : Fin 2 → ℝ :=
                          fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj, h_kr0_jvl0, h_kr1_jvl0] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                        rw [h_vj] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                        rw [Real.log_exp] at h_eq
                        have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_Kouter_unfold : Real.exp K_a - r0 = K_outer := rfl
                        rw [h_Kouter_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                          by linarith [le_abs_self (Real.log K_outer)]
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · -- (const r0, var m=1): v_m = v_1 active. log_triple_nest_witness K_a r0.
                        let v : Fin 2 → ℝ := fun i => if i = 0 then 0
                          else -Real.exp (Real.exp (Real.exp K_a + Real.exp r0 + 100))
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj, h_kr0_jvl0, h_kr1_jvl0] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                        have h_vm : v ⟨0 + 1, hm⟩ =
                            -Real.exp (Real.exp (Real.exp K_a + Real.exp r0 + 100)) := by
                          simp [v]
                        rw [h_vj, h_vm] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                        have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) =
                            -Real.exp (Real.exp (Real.exp K_a + Real.exp r0 + 100)) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_bound := log_triple_nest_witness K_a r0
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · exact absurd hm (by omega)
                    | app op_d kids_d =>
                      -- Depth contra: kids_r 1 = .app.
                      exfalso
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids i).depth) ≤ 3 at hd
                      have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                        have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids i).depth) :=
                          Finset.le_sup (f := fun i => (kids i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1] at h1
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids' i).depth) ≤ 2 at h1
                      have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                        have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids' i).depth) :=
                          Finset.le_sup (f := fun i => (kids' i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1'1'] at h2
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids_r i).depth) ≤ 1 at h2
                      have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                        have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids_r i).depth) :=
                          Finset.le_sup (f := fun i => (kids_r i).depth)
                            (Finset.mem_univ
                              (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_kr1_jvl0] at h3
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity op_d))).sup
                                 (fun i => (kids_d i).depth) ≤ 0 at h3
                      omega
                  | var k =>
                    cases h_kr1_jvl0vk : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                    | const r1 =>
                      rcases k with ⟨_ | _ | _, hk⟩
                      · -- (k=0, const r1): v_k = v_0 = 0. K_r = 1 - log r1. K-bound on v 1.
                        let K_r : ℝ := 1 - Real.log r1
                        let K_outer : ℝ := Real.exp K_a - Real.log K_r
                        let v : Fin 2 → ℝ :=
                          fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj, h_kr0_jvl0, h_kr1_jvl0vk] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                        rw [h_vj] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                        have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_Kr_unfold : (1 : ℝ) - Real.log r1 = K_r := rfl
                        rw [h_Kr_unfold] at h_eq
                        have h_Kouter_unfold : Real.exp K_a - Real.log K_r = K_outer := rfl
                        rw [h_Kouter_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                          by linarith [le_abs_self (Real.log K_outer)]
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · -- (k=1, const r1): v_k = v_1 active. Apply helper #11.
                        let v : Fin 2 → ℝ := fun i => if i = 0 then 0
                          else -Real.exp (Real.exp (Real.exp
                            (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100)))
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj, h_kr0_jvl0, h_kr1_jvl0vk] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                        have h_vk : v ⟨0 + 1, hk⟩ = -Real.exp (Real.exp (Real.exp
                            (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100))) := by
                          simp [v]
                        rw [h_vj, h_vk] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                        have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -Real.exp (Real.exp (Real.exp
                            (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100))) := by
                          simp [v]
                        rw [h_sum] at h_eq
                        have h_bound := log_triple_nest_swap_bound K_a (Real.log r1)
                          (-Real.exp (Real.exp (Real.exp
                            (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100))))
                          (le_refl _)
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · exact absurd hk (by omega)
                    | var k' =>
                      rcases k with ⟨_ | _ | _, hk⟩
                      · rcases k' with ⟨_ | _ | _, hk'⟩
                        · -- (k=0, k'=0): same-var at 0. K_outer = exp K_a.
                          let K_outer : ℝ := Real.exp K_a
                          let v : Fin 2 → ℝ :=
                            fun i => if i = 0 then 0 else -(|Real.log K_outer| + 1)
                          have h_eq := hr v
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                          rw [h_k1] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                           Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                                 v 0 + v 1 at h_eq
                          rw [h_k1'0, h_k1'1'] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                     Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                           Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                     Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                                 v 0 + v 1 at h_eq
                          rw [h_ka0_r, h_ka1_vj, h_kr0_jvl0, h_kr1_jvl0vk] at h_eq
                          simp only [MinimalBasis.Term.eval] at h_eq
                          have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                          rw [h_vj] at h_eq
                          simp only [Real.exp_zero, Real.log_zero, sub_zero, Real.log_one] at h_eq
                          have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                          rw [h_Ka_unfold] at h_eq
                          have h_Kouter_unfold : Real.exp K_a = K_outer := rfl
                          rw [h_Kouter_unfold] at h_eq
                          have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                          rw [h_sum] at h_eq
                          have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                            by linarith [le_abs_self (Real.log K_outer)]
                          have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                          linarith
                        · -- (k=0, k'=1): cross. log_triple_nest_witness K_a 0.
                          let v : Fin 2 → ℝ := fun i => if i = 0 then 0
                            else -Real.exp (Real.exp (Real.exp K_a + Real.exp 0 + 100))
                          have h_eq := hr v
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                          rw [h_k1] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                           Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                                 v 0 + v 1 at h_eq
                          rw [h_k1'0, h_k1'1'] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                     Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                           Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                     Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                                 v 0 + v 1 at h_eq
                          rw [h_ka0_r, h_ka1_vj, h_kr0_jvl0, h_kr1_jvl0vk] at h_eq
                          simp only [MinimalBasis.Term.eval] at h_eq
                          have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                          have h_vk' : v ⟨0 + 1, hk'⟩ =
                              -Real.exp (Real.exp (Real.exp K_a + Real.exp 0 + 100)) := by
                            simp [v]
                          rw [h_vj, h_vk'] at h_eq
                          simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                          have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                          rw [h_Ka_unfold] at h_eq
                          have h_sum : (v 0 + v 1 : ℝ) =
                              -Real.exp (Real.exp (Real.exp K_a + Real.exp 0 + 100)) := by simp [v]
                          rw [h_sum] at h_eq
                          have h_bound := log_triple_nest_witness K_a 0
                          simp only [Real.exp_zero, h_Ka_unfold] at h_eq h_bound
                          have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                          linarith
                        · exact absurd hk' (by omega)
                      · rcases k' with ⟨_ | _ | _, hk'⟩
                        · -- (k=1, k'=0): cross mirror. log_exp_a_plus_abs_a_plus_two_le K_a.
                          let v : Fin 2 → ℝ :=
                            fun i => if i = 0 then 0 else -(|K_a| + 2)
                          have h_eq := hr v
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                          rw [h_k1] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                           Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                                 v 0 + v 1 at h_eq
                          rw [h_k1'0, h_k1'1'] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                     Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                           Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                     Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                                 v 0 + v 1 at h_eq
                          rw [h_ka0_r, h_ka1_vj, h_kr0_jvl0, h_kr1_jvl0vk] at h_eq
                          simp only [MinimalBasis.Term.eval] at h_eq
                          have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                          have h_vk : v ⟨0 + 1, hk⟩ = -(|K_a| + 2) := by simp [v]
                          rw [h_vj, h_vk] at h_eq
                          simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                          rw [Real.log_exp] at h_eq
                          have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                          rw [h_Ka_unfold] at h_eq
                          have h_simp : Real.exp K_a - -(|K_a| + 2) =
                                        Real.exp K_a + |K_a| + 2 := by ring
                          rw [h_simp] at h_eq
                          have h_sum : (v 0 + v 1 : ℝ) = -(|K_a| + 2) := by simp [v]
                          rw [h_sum] at h_eq
                          have h_log_bound : Real.log (Real.exp K_a + |K_a| + 2) ≤ |K_a| + 2 :=
                            log_exp_a_plus_abs_a_plus_two_le K_a
                          have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                          linarith
                        · -- (k=1, k'=1): same-var at v 1. log_triple_nest_same_var_bound K_a.
                          let v : Fin 2 → ℝ := fun i => if i = 0 then 0
                            else -Real.exp (Real.exp (Real.exp (|K_a| + 100)))
                          have h_eq := hr v
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                          rw [h_k1] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                           Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                                 v 0 + v 1 at h_eq
                          rw [h_k1'0, h_k1'1'] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                     Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                           Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                     Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                                 v 0 + v 1 at h_eq
                          rw [h_ka0_r, h_ka1_vj, h_kr0_jvl0, h_kr1_jvl0vk] at h_eq
                          simp only [MinimalBasis.Term.eval] at h_eq
                          have h_vj : v ⟨0, hj⟩ = 0 := by simp [v]
                          have h_vk : v ⟨0 + 1, hk⟩ =
                              -Real.exp (Real.exp (Real.exp (|K_a| + 100))) := by simp [v]
                          rw [h_vj, h_vk] at h_eq
                          simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                          have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                          rw [h_Ka_unfold] at h_eq
                          have h_sum : (v 0 + v 1 : ℝ) =
                              -Real.exp (Real.exp (Real.exp (|K_a| + 100))) := by simp [v]
                          rw [h_sum] at h_eq
                          have h_bound := log_triple_nest_same_var_bound K_a
                            (-Real.exp (Real.exp (Real.exp (|K_a| + 100)))) (le_refl _)
                          have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                          linarith
                        · exact absurd hk' (by omega)
                      · exact absurd hk (by omega)
                    | app op_d kids_d =>
                      -- Depth contra: kids_r 1 = .app.
                      exfalso
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids i).depth) ≤ 3 at hd
                      have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                        have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids i).depth) :=
                          Finset.le_sup (f := fun i => (kids i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1] at h1
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids' i).depth) ≤ 2 at h1
                      have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                        have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids' i).depth) :=
                          Finset.le_sup (f := fun i => (kids' i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1'1'] at h2
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids_r i).depth) ≤ 1 at h2
                      have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                        have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids_r i).depth) :=
                          Finset.le_sup (f := fun i => (kids_r i).depth)
                            (Finset.mem_univ
                              (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_kr1_jvl0vk] at h3
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity op_d))).sup
                                 (fun i => (kids_d i).depth) ≤ 0 at h3
                      omega
                  | app op_d kids_d =>
                    -- Depth contra: kids_r 0 = .app.
                    exfalso
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids i).depth) ≤ 3 at hd
                    have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                      have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids i).depth) :=
                        Finset.le_sup (f := fun i => (kids i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1] at h1
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids' i).depth) ≤ 2 at h1
                    have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                      have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids' i).depth) :=
                        Finset.le_sup (f := fun i => (kids' i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1'1'] at h2
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids_r i).depth) ≤ 1 at h2
                    have h3 : (kids_r ⟨0, hkr0_lt⟩).depth ≤ 0 := by
                      have hle : (kids_r ⟨0, hkr0_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids_r i).depth) :=
                        Finset.le_sup (f := fun i => (kids_r i).depth)
                          (Finset.mem_univ
                            (⟨0, hkr0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_kr0_jvl0] at h3
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity op_d))).sup
                               (fun i => (kids_d i).depth) ≤ 0 at h3
                    omega
                · -- l = 1: kids_a 0 = var 0, kids_a 1 = var 1. Cross-var.
                  -- Diagonal witness v_0 = v_1 = t_w. Apply cross_var_diagonal_contra.
                  cases h_kr0_jvl1c : (kids_r ⟨0, hkr0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                  | const r0 =>
                    cases h_kr1_jvl1c : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                    | const r1 =>
                      -- Shape 1 (const, const): B := log(exp r0 - log r1).
                      let B : ℝ := Real.log (Real.exp r0 - Real.log r1)
                      let t_w : ℝ := -|B| - Real.exp 1 - 1
                      let v : Fin 2 → ℝ := fun i => if i = 0 then t_w else t_w
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj, h_kr0_jvl1c, h_kr1_jvl1c] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0, hj⟩ = t_w := by simp [v]
                      have h_vl : v ⟨0 + 1, hl⟩ = t_w := by simp [v]
                      rw [h_vj, h_vl] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = 2 * t_w := by simp [v]; ring
                      rw [h_sum] at h_eq
                      have h_B_unfold : Real.log (Real.exp r0 - Real.log r1) = B := rfl
                      rw [h_B_unfold] at h_eq
                      -- Now apply cross_var_diagonal_contra.
                      have h_K_pos : (0 : ℝ) < Real.exp ((kids ⟨0, hk0_lt⟩).eval v) :=
                        Real.exp_pos _
                      have hB_nn : (0 : ℝ) ≤ |B| := abs_nonneg B
                      have h_exp_1_pos : Real.exp 1 > 0 := Real.exp_pos 1
                      have h_exp_1_ge_2 : Real.exp 1 ≥ 2 := by
                        have := Real.add_one_le_exp (1:ℝ); linarith
                      have h_t_neg : t_w < 0 := by simp [t_w]; linarith
                      have h_neg_t_pos : -t_w > 0 := by linarith
                      have h_neg_t_ge_1 : -t_w ≥ 1 := by simp [t_w]; linarith
                      -- exp t_w ≤ 1, log t_w ≥ 0.
                      have h_exp_tw_le_1 : Real.exp t_w ≤ 1 := by
                        rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
                        exact Real.exp_le_exp.mpr (le_of_lt h_t_neg)
                      have h_exp_tw_pos : Real.exp t_w > 0 := Real.exp_pos t_w
                      have h_log_tw_eq : Real.log t_w = Real.log (-t_w) := by
                        conv_lhs => rw [show t_w = -(-t_w) from by ring]
                        rw [Real.log_neg_eq_log]
                      have h_log_tw_nn : Real.log t_w ≥ 0 := by
                        rw [h_log_tw_eq]; exact Real.log_nonneg h_neg_t_ge_1
                      have h_Q_le_1 : Real.exp t_w - Real.log t_w ≤ 1 := by linarith
                      have h_eQ_le : Real.exp (Real.exp t_w - Real.log t_w) ≤ Real.exp 1 :=
                        Real.exp_le_exp.mpr h_Q_le_1
                      have h_eQ_pos : Real.exp (Real.exp t_w - Real.log t_w) > 0 := Real.exp_pos _
                      have h_Y_abs_le :
                          |Real.exp (Real.exp t_w - Real.log t_w) - B| ≤ Real.exp 1 + |B| := by
                        calc |Real.exp (Real.exp t_w - Real.log t_w) - B|
                            ≤ |Real.exp (Real.exp t_w - Real.log t_w)| + |B| := abs_sub _ _
                          _ = Real.exp (Real.exp t_w - Real.log t_w) + |B| := by
                              rw [abs_of_pos h_eQ_pos]
                          _ ≤ Real.exp 1 + |B| := by linarith
                      have h_Y_upper :
                          Real.log (Real.exp (Real.exp t_w - Real.log t_w) - B) ≤ -t_w := by
                        have h_log_eq_abs :
                            Real.log (Real.exp (Real.exp t_w - Real.log t_w) - B) =
                            Real.log |Real.exp (Real.exp t_w - Real.log t_w) - B| :=
                          (Real.log_abs _).symm
                        rw [h_log_eq_abs]
                        have h_sum_pos : (0 : ℝ) < Real.exp 1 + |B| := by linarith
                        by_cases h_Y_zero : Real.exp (Real.exp t_w - Real.log t_w) - B = 0
                        · rw [h_Y_zero, abs_zero, Real.log_zero]; linarith
                        · have h_abs_pos :
                              |Real.exp (Real.exp t_w - Real.log t_w) - B| > 0 :=
                            abs_pos.mpr h_Y_zero
                          have h_log_le :
                              Real.log |Real.exp (Real.exp t_w - Real.log t_w) - B| ≤
                              Real.log (Real.exp 1 + |B|) :=
                            Real.log_le_log h_abs_pos h_Y_abs_le
                          have h_log_sum :
                              Real.log (Real.exp 1 + |B|) ≤ Real.exp 1 + |B| - 1 :=
                            Real.log_le_sub_one_of_pos h_sum_pos
                          have : -t_w ≥ Real.exp 1 + |B| + 1 := by simp [t_w]; linarith
                          linarith
                      exact cross_var_diagonal_contra
                        (Real.exp ((kids ⟨0, hk0_lt⟩).eval v))
                        (Real.exp (Real.exp t_w - Real.log t_w) - B)
                        t_w h_K_pos h_Y_upper h_t_neg h_eq
                    | var m =>
                      -- Shape 2 (const r0, var m) under diagonal. S(t_w) = exp(r0) - log(t_w).
                      -- Witness `t_w := -exp(exp r0 + 10)` makes log t_w = exp r0 + 10,
                      -- so S(t_w) = -10 (uniform constant).
                      let t_w : ℝ := -Real.exp (Real.exp r0 + 10)
                      let v : Fin 2 → ℝ := fun i => if i = 0 then t_w else t_w
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj, h_kr0_jvl1c, h_kr1_jvl1c] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0, hj⟩ = t_w := by simp [v]
                      have h_vl : v ⟨0 + 1, hl⟩ = t_w := by simp [v]
                      have h_vm : v m = t_w := by simp [v, ite_self]
                      rw [h_vj, h_vl, h_vm] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = 2 * t_w := by simp [v]; ring
                      rw [h_sum] at h_eq
                      -- Bound setup.
                      have h_exp_r0_pos : Real.exp r0 > 0 := Real.exp_pos r0
                      have h_inner_ge_10 : Real.exp r0 + 10 ≥ 10 := by linarith
                      have h_exp_10_ge_11 : Real.exp 10 ≥ 11 := by
                        have := Real.add_one_le_exp (10 : ℝ); linarith
                      have h_exp_inner_ge_11 : Real.exp (Real.exp r0 + 10) ≥ 11 := by
                        have h_mono : Real.exp 10 ≤ Real.exp (Real.exp r0 + 10) :=
                          Real.exp_le_exp.mpr h_inner_ge_10
                        linarith
                      have h_t_w_neg : t_w < 0 := by
                        simp [t_w]; exact Real.exp_pos _
                      have h_t_bound : t_w ≤ -3 := by
                        simp [t_w]; linarith
                      have h_neg_t_w_pos : -t_w > 0 := by linarith
                      have h_neg_t_w_eq : -t_w = Real.exp (Real.exp r0 + 10) := by simp [t_w]
                      have h_log_t_w : Real.log t_w = Real.exp r0 + 10 := by
                        rw [show t_w = -(Real.exp (Real.exp r0 + 10)) from rfl]
                        rw [Real.log_neg_eq_log, Real.log_exp]
                      have h_S_val : Real.exp r0 - Real.log t_w = -10 := by
                        rw [h_log_t_w]; ring
                      -- h_S_logbound : |Real.log (Real.exp r0 - Real.log t_w)| ≤ |t_w|.
                      have h_S_logbound :
                          |Real.log (Real.exp r0 - Real.log t_w)| ≤ |t_w| := by
                        rw [h_S_val]
                        -- |Real.log (-10)| = Real.log 10.
                        rw [show (-10 : ℝ) = -(10 : ℝ) from by ring]
                        rw [Real.log_neg_eq_log]
                        have h_log_10_pos : Real.log 10 > 0 := Real.log_pos (by norm_num)
                        rw [abs_of_pos h_log_10_pos]
                        -- Real.log 10 ≤ 9 (via log_le_sub_one).
                        have h_log_10_le : Real.log 10 ≤ 9 := by
                          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 10)
                          linarith
                        -- |t_w| = -t_w = Real.exp (Real.exp r0 + 10) ≥ 11.
                        have h_abs_t_w : |t_w| ≥ 11 := by
                          rw [abs_of_neg h_t_w_neg, h_neg_t_w_eq]; linarith
                        linarith
                      have h_bound := log_diagonal_cross_bound
                        (fun t => Real.exp r0 - Real.log t) t_w h_S_logbound h_t_bound
                      simp only at h_bound
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    | app op_d kids_d =>
                      -- Depth contra: kids_r 1 = .app.
                      exfalso
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids i).depth) ≤ 3 at hd
                      have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                        have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids i).depth) :=
                          Finset.le_sup (f := fun i => (kids i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1] at h1
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids' i).depth) ≤ 2 at h1
                      have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                        have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids' i).depth) :=
                          Finset.le_sup (f := fun i => (kids' i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1'1'] at h2
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids_r i).depth) ≤ 1 at h2
                      have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                        have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids_r i).depth) :=
                          Finset.le_sup (f := fun i => (kids_r i).depth)
                            (Finset.mem_univ
                              (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_kr1_jvl1c] at h3
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity op_d))).sup
                                 (fun i => (kids_d i).depth) ≤ 0 at h3
                      omega
                  | var k =>
                    cases h_kr1_jvl1v : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                    | const r1 =>
                      -- Shape 3 (var k, const r1). Use cross_var_diagonal_contra (one-sided)
                      -- with adaptive exp-deep witness per design note.
                      let t_w : ℝ :=
                        -Real.exp (|Real.log r1| + |Real.log (Real.log r1)| + 11) - 4
                      let v : Fin 2 → ℝ := fun i => if i = 0 then t_w else t_w
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj, h_kr0_jvl1c, h_kr1_jvl1v] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0, hj⟩ = t_w := by simp [v]
                      have h_vl : v ⟨0 + 1, hl⟩ = t_w := by simp [v]
                      have h_vk : v k = t_w := by simp [v, ite_self]
                      rw [h_vj, h_vl, h_vk] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = 2 * t_w := by simp [v]; ring
                      rw [h_sum] at h_eq
                      -- Setup bounds.
                      have h_log_r1_abs_nn : (0 : ℝ) ≤ |Real.log r1| := abs_nonneg _
                      have h_log_log_r1_abs_nn : (0 : ℝ) ≤ |Real.log (Real.log r1)| :=
                        abs_nonneg _
                      have h_inner_ge_11 :
                          |Real.log r1| + |Real.log (Real.log r1)| + 11 ≥ 11 := by linarith
                      have h_exp_inner_ge_11 :
                          Real.exp (|Real.log r1| + |Real.log (Real.log r1)| + 11) ≥ 12 := by
                        have := Real.add_one_le_exp
                          (|Real.log r1| + |Real.log (Real.log r1)| + 11); linarith
                      have h_t_w_neg : t_w < 0 := by
                        simp [t_w]
                        have := Real.exp_pos
                          (|Real.log r1| + |Real.log (Real.log r1)| + 11); linarith
                      have h_neg_t_w_pos : -t_w > 0 := by linarith
                      have h_neg_t_w_ge_16 : -t_w ≥ 16 := by simp [t_w]; linarith
                      have h_abs_t_w_eq : |t_w| = -t_w := abs_of_neg h_t_w_neg
                      have h_exp_t_w_le_1 : Real.exp t_w ≤ 1 := by
                        rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
                        exact Real.exp_le_exp.mpr (by linarith)
                      have h_exp_t_w_pos : Real.exp t_w > 0 := Real.exp_pos t_w
                      have h_log_t_w_eq : Real.log t_w = Real.log (-t_w) := by
                        conv_lhs => rw [show t_w = -(-t_w) from by ring]
                        rw [Real.log_neg_eq_log]
                      have h_log_neg_t_w_nn : Real.log (-t_w) ≥ 0 :=
                        Real.log_nonneg (by linarith)
                      have h_log_t_w_nn : Real.log t_w ≥ 0 := by
                        rw [h_log_t_w_eq]; exact h_log_neg_t_w_nn
                      have h_Q_le_1 : Real.exp t_w - Real.log t_w ≤ 1 := by linarith
                      have h_exp_Q_le_e : Real.exp (Real.exp t_w - Real.log t_w) ≤ Real.exp 1 :=
                        Real.exp_le_exp.mpr h_Q_le_1
                      have h_exp_1_pos : Real.exp 1 > 0 := Real.exp_pos 1
                      have h_exp_1_lt_3 : Real.exp 1 < 3 := by
                        have := Real.exp_one_lt_d9; linarith
                      have h_exp_Q_pos : Real.exp (Real.exp t_w - Real.log t_w) > 0 :=
                        Real.exp_pos _
                      -- Apply cross_var_diagonal_contra. Goal: derive False from h_eq.
                      have h_K_pos : (0 : ℝ) < Real.exp ((kids ⟨0, hk0_lt⟩).eval v) :=
                        Real.exp_pos _
                      -- Bound Real.log Y ≤ -t_w where Y = exp(Q) - log(S), S = exp(t_w) - log r1.
                      -- By_cases on Real.log r1 = 0 (covers r1 ∈ {0, ±1}).
                      have h_Y_upper :
                          Real.log (Real.exp (Real.exp t_w - Real.log t_w) -
                                    Real.log (Real.exp t_w - Real.log r1)) ≤ -t_w := by
                        by_cases h_log_r1_zero : Real.log r1 = 0
                        · -- Branch A: r1 ∈ {0, ±1}. S = exp(t_w). log S = t_w.
                          rw [h_log_r1_zero, sub_zero, Real.log_exp]
                          -- Now goal: log(exp(Q) - t_w) ≤ -t_w.
                          have h_Y_pos : Real.exp (Real.exp t_w - Real.log t_w) - t_w > 0 := by
                            linarith
                          -- exp Q ≤ e ≤ -t_w/2 for -t_w ≥ 2e. We have -t_w ≥ 16 ≥ 2e ≈ 5.44.
                          have h_e_le_neg_t : Real.exp 1 ≤ -t_w := by linarith
                          have h_Y_le : Real.exp (Real.exp t_w - Real.log t_w) - t_w ≤ 2 * (-t_w) := by
                            linarith
                          have h_2_neg_t_pos : (0 : ℝ) < 2 * (-t_w) := by linarith
                          have h_log_Y_le_log_2_neg_t :
                              Real.log (Real.exp (Real.exp t_w - Real.log t_w) - t_w) ≤
                              Real.log (2 * (-t_w)) :=
                            Real.log_le_log h_Y_pos h_Y_le
                          have h_log_2_neg_t_split :
                              Real.log (2 * (-t_w)) = Real.log 2 + Real.log (-t_w) :=
                            Real.log_mul (by norm_num) (ne_of_gt h_neg_t_w_pos)
                          have h_log_2_le_1 : Real.log 2 ≤ 1 := by
                            have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
                            linarith
                          have h_log_neg_t_le : Real.log (-t_w) ≤ -t_w - 1 :=
                            Real.log_le_sub_one_of_pos h_neg_t_w_pos
                          linarith
                        · -- Branch B: Real.log r1 ≠ 0. |log r1| > 0.
                          -- Bound |log S| via |S| ≥ |log r1|/2 (exp-deep witness).
                          have h_S_abs_le :
                              |Real.exp t_w - Real.log r1| ≤ 1 + |Real.log r1| := by
                            calc |Real.exp t_w - Real.log r1|
                                ≤ |Real.exp t_w| + |Real.log r1| := abs_sub _ _
                              _ = Real.exp t_w + |Real.log r1| := by
                                  rw [abs_of_pos h_exp_t_w_pos]
                              _ ≤ 1 + |Real.log r1| := by linarith
                          have h_log_r1_abs_pos : |Real.log r1| > 0 :=
                            abs_pos.mpr h_log_r1_zero
                          -- Linearize the witness via add_one_le_exp.
                          have h_t_w_linear :
                              t_w ≤ -|Real.log r1| - |Real.log (Real.log r1)| - 16 := by
                            have h_exp_ge :
                                Real.exp (|Real.log r1| + |Real.log (Real.log r1)| + 11)
                                  ≥ |Real.log r1| + |Real.log (Real.log r1)| + 12 := by
                              have := Real.add_one_le_exp
                                (|Real.log r1| + |Real.log (Real.log r1)| + 11)
                              linarith
                            simp [t_w]; linarith
                          -- Split exp(t_w) into three factors via Real.exp_add.
                          have h_exp_t_w_split :
                              Real.exp t_w ≤
                              Real.exp (-|Real.log r1|) *
                              Real.exp (-|Real.log (Real.log r1)|) *
                              Real.exp (-16) := by
                            have h := Real.exp_le_exp.mpr h_t_w_linear
                            rw [show (-|Real.log r1| - |Real.log (Real.log r1)| - 16 : ℝ) =
                                (-|Real.log r1|) + (-|Real.log (Real.log r1)|) + (-16) from by ring,
                                Real.exp_add, Real.exp_add] at h
                            exact h
                          -- Numeric bounds on the three factors.
                          have h_exp_neg_abs_log_r1_le_1 :
                              Real.exp (-|Real.log r1|) ≤ 1 := by
                            rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
                            exact Real.exp_le_exp.mpr (neg_nonpos.mpr (abs_nonneg _))
                          have h_exp_1_ge_2 : Real.exp 1 ≥ 2 := by
                            have := Real.add_one_le_exp (1 : ℝ); linarith
                          have h_exp_neg_16_le_half : Real.exp (-16 : ℝ) ≤ 1 / 2 := by
                            have h_exp_16_pos : (0 : ℝ) < Real.exp 16 := Real.exp_pos _
                            have h_exp_neg_16_pos : (0 : ℝ) < Real.exp (-16) := Real.exp_pos _
                            have h_ge_2 : (2 : ℝ) ≤ Real.exp 16 := by
                              have h1 : Real.exp 1 ≤ Real.exp 16 :=
                                Real.exp_le_exp.mpr (by norm_num)
                              linarith
                            have h_prod : Real.exp (-16) * Real.exp 16 = 1 := by
                              rw [← Real.exp_add]; simp
                            nlinarith [h_prod, h_exp_neg_16_pos, h_exp_16_pos, h_ge_2]
                          -- Case-split |log r1| < 1 vs ≥ 1 to bound exp(-|log log r1|).
                          have h_exp_t_w_le_half_log_r1 :
                              Real.exp t_w ≤ |Real.log r1| / 2 := by
                            by_cases h_lt_1 : |Real.log r1| < 1
                            · -- Case A: |log r1| < 1. exp(-|log log r1|) = |log r1|.
                              have h_log_log_r1_neg : Real.log (Real.log r1) < 0 := by
                                rw [← Real.log_abs]
                                exact Real.log_neg h_log_r1_abs_pos h_lt_1
                              have h_abs_log_log_eq :
                                  |Real.log (Real.log r1)| = -Real.log (Real.log r1) :=
                                abs_of_neg h_log_log_r1_neg
                              have h_exp_neg_log_log_eq :
                                  Real.exp (-|Real.log (Real.log r1)|) = |Real.log r1| := by
                                rw [h_abs_log_log_eq, neg_neg]
                                rw [show Real.log (Real.log r1) = Real.log |Real.log r1| from
                                    (Real.log_abs _).symm]
                                exact Real.exp_log h_log_r1_abs_pos
                              rw [h_exp_neg_log_log_eq] at h_exp_t_w_split
                              -- Chain: exp t_w ≤ exp(-|log r1|) * |log r1| * exp(-16) ≤
                              --                  1 * |log r1| * (1/2) = |log r1|/2.
                              have h_log_r1_abs_nn : (0 : ℝ) ≤ |Real.log r1| := abs_nonneg _
                              have h_exp_neg_log_r1_nn :
                                  (0 : ℝ) ≤ Real.exp (-|Real.log r1|) := (Real.exp_pos _).le
                              have h_exp_neg_16_nn :
                                  (0 : ℝ) ≤ Real.exp (-16 : ℝ) := (Real.exp_pos _).le
                              have h_step1 :
                                  Real.exp (-|Real.log r1|) * |Real.log r1| ≤
                                  1 * |Real.log r1| :=
                                mul_le_mul_of_nonneg_right h_exp_neg_abs_log_r1_le_1
                                  h_log_r1_abs_nn
                              have h_step2 :
                                  Real.exp (-|Real.log r1|) * |Real.log r1| *
                                  Real.exp (-16) ≤
                                  1 * |Real.log r1| * (1 / 2) := by
                                have h_left_nn :
                                    (0 : ℝ) ≤ Real.exp (-|Real.log r1|) * |Real.log r1| :=
                                  mul_nonneg h_exp_neg_log_r1_nn h_log_r1_abs_nn
                                have h_right_nn : (0 : ℝ) ≤ 1 * |Real.log r1| := by
                                  positivity
                                have h_a :
                                    Real.exp (-|Real.log r1|) * |Real.log r1| *
                                    Real.exp (-16) ≤
                                    1 * |Real.log r1| * Real.exp (-16) :=
                                  mul_le_mul_of_nonneg_right h_step1 h_exp_neg_16_nn
                                have h_b :
                                    1 * |Real.log r1| * Real.exp (-16) ≤
                                    1 * |Real.log r1| * (1 / 2) :=
                                  mul_le_mul_of_nonneg_left h_exp_neg_16_le_half h_right_nn
                                linarith
                              linarith
                            · -- Case B: |log r1| ≥ 1. exp(-|log log r1|) ≤ 1.
                              push_neg at h_lt_1
                              have h_exp_neg_log_log_le_1 :
                                  Real.exp (-|Real.log (Real.log r1)|) ≤ 1 := by
                                rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
                                exact Real.exp_le_exp.mpr (neg_nonpos.mpr (abs_nonneg _))
                              have h_e_neg_log_log_nn :
                                  (0 : ℝ) ≤ Real.exp (-|Real.log (Real.log r1)|) :=
                                (Real.exp_pos _).le
                              have h_e_neg_r1_nn :
                                  (0 : ℝ) ≤ Real.exp (-|Real.log r1|) := (Real.exp_pos _).le
                              have h_e_neg_16_nn :
                                  (0 : ℝ) ≤ Real.exp (-16 : ℝ) := (Real.exp_pos _).le
                              -- exp(-|log r1|) * exp(-|log log r1|) ≤ 1 * 1
                              have h_step1 :
                                  Real.exp (-|Real.log r1|) *
                                  Real.exp (-|Real.log (Real.log r1)|) ≤ 1 := by
                                have h_a :
                                    Real.exp (-|Real.log r1|) *
                                    Real.exp (-|Real.log (Real.log r1)|) ≤
                                    1 * Real.exp (-|Real.log (Real.log r1)|) :=
                                  mul_le_mul_of_nonneg_right
                                    h_exp_neg_abs_log_r1_le_1 h_e_neg_log_log_nn
                                linarith
                              have h_step1_nn :
                                  (0 : ℝ) ≤ Real.exp (-|Real.log r1|) *
                                            Real.exp (-|Real.log (Real.log r1)|) :=
                                mul_nonneg h_e_neg_r1_nn h_e_neg_log_log_nn
                              have h_step2 :
                                  Real.exp (-|Real.log r1|) *
                                  Real.exp (-|Real.log (Real.log r1)|) *
                                  Real.exp (-16) ≤ 1 * Real.exp (-16) :=
                                mul_le_mul_of_nonneg_right h_step1 h_e_neg_16_nn
                              -- 1 * exp(-16) ≤ 1/2 ≤ |log r1| / 2.
                              linarith
                          -- |S| ≥ |log r1|/2 via reverse triangle.
                          have h_S_abs_ge_half :
                              |Real.exp t_w - Real.log r1| ≥ |Real.log r1| / 2 := by
                            have h_exp_abs : |Real.exp t_w| = Real.exp t_w :=
                              abs_of_pos h_exp_t_w_pos
                            have h_swap : |Real.exp t_w - Real.log r1| =
                                          |Real.log r1 - Real.exp t_w| := by
                              rw [show Real.exp t_w - Real.log r1 =
                                       -(Real.log r1 - Real.exp t_w) from by ring,
                                  abs_neg]
                            rw [h_swap]
                            have h2 := abs_sub_abs_le_abs_sub (Real.log r1) (Real.exp t_w)
                            have h4 : |Real.log r1| - |Real.exp t_w| ≤
                                      |Real.log r1 - Real.exp t_w| := by
                              have := le_abs_self (|Real.log r1| - |Real.exp t_w|)
                              linarith
                            rw [h_exp_abs] at h4
                            linarith
                          -- log|S| upper: ≤ |log r1| via log_le_sub_one.
                          have h_S_pos : |Real.exp t_w - Real.log r1| > 0 := by linarith
                          have h_log_S_eq_log_abs :
                              Real.log (Real.exp t_w - Real.log r1) =
                              Real.log |Real.exp t_w - Real.log r1| :=
                            (Real.log_abs _).symm
                          have h_log_S_abs_upper :
                              Real.log |Real.exp t_w - Real.log r1| ≤ |Real.log r1| := by
                            have h_le := Real.log_le_log h_S_pos h_S_abs_le
                            have h_sum_pos : (0 : ℝ) < 1 + |Real.log r1| := by linarith
                            have h_log_sum := Real.log_le_sub_one_of_pos h_sum_pos
                            linarith
                          -- log|S| lower: ≥ -|log log r1| - 1 via log_le_log on |S| ≥ |log r1|/2.
                          have h_log_half_log_r1 :
                              Real.log (|Real.log r1| / 2) ≥
                              -|Real.log (Real.log r1)| - 1 := by
                            have h_log_split :
                                Real.log (|Real.log r1| / 2) =
                                Real.log |Real.log r1| - Real.log 2 := by
                              rw [Real.log_div (ne_of_gt h_log_r1_abs_pos)
                                  (by norm_num : (2:ℝ) ≠ 0)]
                            rw [h_log_split]
                            have h_log_abs_eq :
                                Real.log |Real.log r1| = Real.log (Real.log r1) :=
                              Real.log_abs _
                            have h_neg_abs_le :
                                -|Real.log (Real.log r1)| ≤ Real.log (Real.log r1) :=
                              neg_abs_le _
                            have h_log_2_le_1 : Real.log 2 ≤ 1 := by
                              have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
                              linarith
                            linarith
                          have h_log_S_abs_lower :
                              Real.log |Real.exp t_w - Real.log r1| ≥
                              -|Real.log (Real.log r1)| - 1 := by
                            have h_le := Real.log_le_log
                              (by linarith : (0:ℝ) < |Real.log r1| / 2) h_S_abs_ge_half
                            linarith
                          -- |log S| ≤ |log r1| + |log log r1| + 1.
                          have h_log_S_abs_bound :
                              |Real.log (Real.exp t_w - Real.log r1)| ≤
                              |Real.log r1| + |Real.log (Real.log r1)| + 1 := by
                            rw [h_log_S_eq_log_abs]
                            by_cases h : 0 ≤ Real.log |Real.exp t_w - Real.log r1|
                            · rw [abs_of_nonneg h]; linarith
                            · push_neg at h
                              rw [abs_of_neg h]; linarith
                          -- |Y| ≤ exp(Q) + |log S| ≤ e + |log r1| + |log log r1| + 1.
                          have h_Y_abs_le :
                              |Real.exp (Real.exp t_w - Real.log t_w) -
                               Real.log (Real.exp t_w - Real.log r1)| ≤
                              Real.exp 1 + |Real.log r1| +
                              |Real.log (Real.log r1)| + 1 := by
                            calc |Real.exp (Real.exp t_w - Real.log t_w) -
                                  Real.log (Real.exp t_w - Real.log r1)|
                                ≤ |Real.exp (Real.exp t_w - Real.log t_w)| +
                                  |Real.log (Real.exp t_w - Real.log r1)| := abs_sub _ _
                              _ = Real.exp (Real.exp t_w - Real.log t_w) +
                                  |Real.log (Real.exp t_w - Real.log r1)| := by
                                    rw [abs_of_pos h_exp_Q_pos]
                              _ ≤ Real.exp 1 +
                                  (|Real.log r1| + |Real.log (Real.log r1)| + 1) := by
                                    linarith
                              _ = Real.exp 1 + |Real.log r1| +
                                  |Real.log (Real.log r1)| + 1 := by ring
                          -- log|Y| ≤ |Y| - 1 ≤ -t_w via exp-depth.
                          have h_log_Y_eq_abs :
                              Real.log (Real.exp (Real.exp t_w - Real.log t_w) -
                                        Real.log (Real.exp t_w - Real.log r1)) =
                              Real.log |Real.exp (Real.exp t_w - Real.log t_w) -
                                        Real.log (Real.exp t_w - Real.log r1)| :=
                            (Real.log_abs _).symm
                          rw [h_log_Y_eq_abs]
                          by_cases h_Y_zero :
                              Real.exp (Real.exp t_w - Real.log t_w) -
                              Real.log (Real.exp t_w - Real.log r1) = 0
                          · rw [h_Y_zero, abs_zero, Real.log_zero]; linarith
                          · have h_Y_abs_pos :
                                |Real.exp (Real.exp t_w - Real.log t_w) -
                                 Real.log (Real.exp t_w - Real.log r1)| > 0 :=
                              abs_pos.mpr h_Y_zero
                            have h_Y_abs_sum_pos : (0 : ℝ) <
                                Real.exp 1 + |Real.log r1| +
                                |Real.log (Real.log r1)| + 1 := by linarith
                            have h_log_le_sum := Real.log_le_log h_Y_abs_pos h_Y_abs_le
                            have h_log_sum_le :
                                Real.log (Real.exp 1 + |Real.log r1| +
                                          |Real.log (Real.log r1)| + 1) ≤
                                Real.exp 1 + |Real.log r1| +
                                |Real.log (Real.log r1)| := by
                              have := Real.log_le_sub_one_of_pos h_Y_abs_sum_pos
                              linarith
                            have h_neg_t_w_ge_sum : -t_w ≥
                                Real.exp 1 + |Real.log r1| +
                                |Real.log (Real.log r1)| := by
                              have h_inner_ge_e :
                                  Real.exp (|Real.log r1| +
                                            |Real.log (Real.log r1)| + 11) ≥
                                  |Real.log r1| + |Real.log (Real.log r1)| + 12 := by
                                have := Real.add_one_le_exp
                                  (|Real.log r1| + |Real.log (Real.log r1)| + 11)
                                linarith
                              simp [t_w]; linarith [h_exp_1_lt_3]
                            linarith
                      exact cross_var_diagonal_contra
                        (Real.exp ((kids ⟨0, hk0_lt⟩).eval v))
                        (Real.exp (Real.exp t_w - Real.log t_w) -
                         Real.log (Real.exp t_w - Real.log r1))
                        t_w h_K_pos h_Y_upper h_t_w_neg h_eq
                    | var k' =>
                      -- Shape 4 (var k, var k') under diagonal. S(t_w) = exp(t_w) - log(t_w) = Q.
                      let t_w : ℝ := -10
                      let v : Fin 2 → ℝ := fun i => if i = 0 then t_w else t_w
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj, h_kr0_jvl1c, h_kr1_jvl1v] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0, hj⟩ = t_w := by simp [v]
                      have h_vl : v ⟨0 + 1, hl⟩ = t_w := by simp [v]
                      have h_vk : v k = t_w := by simp [v, ite_self]
                      have h_vk' : v k' = t_w := by simp [v, ite_self]
                      rw [h_vj, h_vl, h_vk, h_vk'] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = 2 * t_w := by simp [v]; ring
                      rw [h_sum] at h_eq
                      have h_t_bound : t_w ≤ -3 := by norm_num [t_w]
                      have h_t_lt_0 : t_w < 0 := by norm_num [t_w]
                      have h_abs_t : |t_w| = -t_w := abs_of_neg h_t_lt_0
                      have h_neg_t_ge_3 : -t_w ≥ 3 := by norm_num [t_w]
                      have h_neg_t_pos : (0 : ℝ) < -t_w := by norm_num [t_w]
                      have h_S_logbound :
                          |Real.log (Real.exp t_w - Real.log t_w)| ≤ |t_w| := by
                        have h_exp_tw_le_1 : Real.exp t_w ≤ 1 := by
                          rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
                          exact Real.exp_le_exp.mpr (by linarith)
                        have h_exp_tw_pos : Real.exp t_w > 0 := Real.exp_pos t_w
                        have h_log_tw_eq : Real.log t_w = Real.log (-t_w) := by
                          conv_lhs => rw [show t_w = -(-t_w) from by ring]
                          rw [Real.log_neg_eq_log]
                        have h_exp_1_lt_3 : Real.exp 1 < 3 := by
                          have := Real.exp_one_lt_d9; linarith
                        have h_log_3_ge_1 : Real.log 3 ≥ 1 := by
                          have h : Real.log (Real.exp 1) ≤ Real.log 3 :=
                            Real.log_le_log (Real.exp_pos 1) (le_of_lt h_exp_1_lt_3)
                          rw [Real.log_exp] at h; exact h
                        have h_log_neg_t_ge_1 : Real.log (-t_w) ≥ 1 := by
                          have h : Real.log 3 ≤ Real.log (-t_w) :=
                            Real.log_le_log (by norm_num : (0:ℝ) < 3) h_neg_t_ge_3
                          linarith
                        have h_log_tw_ge_1 : Real.log t_w ≥ 1 := by
                          rw [h_log_tw_eq]; exact h_log_neg_t_ge_1
                        have h_Q_neg : Real.exp t_w - Real.log t_w ≤ 0 := by linarith
                        have h_Q_abs_le_log :
                            |Real.exp t_w - Real.log t_w| ≤ Real.log (-t_w) := by
                          rw [abs_of_nonpos h_Q_neg]
                          rw [h_log_tw_eq]; linarith
                        have h_Q_abs_ge_1 : |Real.exp t_w - Real.log t_w| ≥ 1 := by
                          rw [abs_of_nonpos h_Q_neg, h_log_tw_eq]
                          have h_log_10 : Real.log 10 ≥ 2 := by
                            have h_exp_2_lt_10 : Real.exp 2 < 10 := by
                              have h_exp_1_sq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
                                rw [show (2 : ℝ) = 1 + 1 from by norm_num, Real.exp_add]
                              have h_exp_1_lt_3 : Real.exp 1 < 3 := by
                                have := Real.exp_one_lt_d9; linarith
                              have h_exp_1_pos : Real.exp 1 > 0 := Real.exp_pos 1
                              rw [h_exp_1_sq]; nlinarith
                            have h := Real.log_le_log (Real.exp_pos 2) (le_of_lt h_exp_2_lt_10)
                            rw [Real.log_exp] at h; exact h
                          have h_log_neg_t : Real.log (-t_w) = Real.log 10 := by
                            simp [t_w]
                          rw [h_log_neg_t]; linarith
                        have h_Q_abs_pos : |Real.exp t_w - Real.log t_w| > 0 := by linarith
                        have h_log_Q_abs_le : Real.log |Real.exp t_w - Real.log t_w| ≤
                                              Real.log (Real.log (-t_w)) := by
                          have h_log_neg_t_pos : Real.log (-t_w) > 0 := by linarith
                          exact Real.log_le_log h_Q_abs_pos h_Q_abs_le_log
                        have h_log_log_le : Real.log (Real.log (-t_w)) ≤ Real.log (-t_w) - 1 :=
                          Real.log_le_sub_one_of_pos (by linarith)
                        have h_log_neg_t_le : Real.log (-t_w) ≤ -t_w - 1 :=
                          Real.log_le_sub_one_of_pos h_neg_t_pos
                        have h_log_Q_abs_nn :
                            Real.log |Real.exp t_w - Real.log t_w| ≥ 0 := by
                          exact Real.log_nonneg (by linarith)
                        have h_log_Q_eq_abs :
                            Real.log (Real.exp t_w - Real.log t_w) =
                            Real.log |Real.exp t_w - Real.log t_w| :=
                          (Real.log_abs _).symm
                        rw [h_log_Q_eq_abs]
                        rw [abs_of_nonneg h_log_Q_abs_nn]
                        linarith
                      have h_bound := log_diagonal_cross_bound
                        (fun t => Real.exp t - Real.log t) t_w h_S_logbound h_t_bound
                      simp only at h_bound
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    | app op_d kids_d =>
                      -- Depth contra: kids_r 1 = .app (inside var k branch).
                      exfalso
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids i).depth) ≤ 3 at hd
                      have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                        have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids i).depth) :=
                          Finset.le_sup (f := fun i => (kids i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1] at h1
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids' i).depth) ≤ 2 at h1
                      have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                        have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids' i).depth) :=
                          Finset.le_sup (f := fun i => (kids' i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1'1'] at h2
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids_r i).depth) ≤ 1 at h2
                      have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                        have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids_r i).depth) :=
                          Finset.le_sup (f := fun i => (kids_r i).depth)
                            (Finset.mem_univ
                              (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_kr1_jvl1v] at h3
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity op_d))).sup
                                 (fun i => (kids_d i).depth) ≤ 0 at h3
                      omega
                  | app op_d kids_d =>
                    -- Depth contra: kids_r 0 = .app.
                    exfalso
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids i).depth) ≤ 3 at hd
                    have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                      have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids i).depth) :=
                        Finset.le_sup (f := fun i => (kids i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1] at h1
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids' i).depth) ≤ 2 at h1
                    have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                      have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids' i).depth) :=
                        Finset.le_sup (f := fun i => (kids' i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1'1'] at h2
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids_r i).depth) ≤ 1 at h2
                    have h3 : (kids_r ⟨0, hkr0_lt⟩).depth ≤ 0 := by
                      have hle : (kids_r ⟨0, hkr0_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids_r i).depth) :=
                        Finset.le_sup (f := fun i => (kids_r i).depth)
                          (Finset.mem_univ
                            (⟨0, hkr0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_kr0_jvl1c] at h3
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity op_d))).sup
                               (fun i => (kids_d i).depth) ≤ 0 at h3
                    omega
                · exact absurd hl (by omega)
              | app op_d kids_d =>
                -- Depth contra: kids_a 1 = .app forces depth ≥ 1, but kids_a children leaves.
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 3 at hd
                have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                  have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids' i).depth) ≤ 2 at h1
                have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
                  have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids' i).depth) :=
                    Finset.le_sup (f := fun i => (kids' i).depth)
                      (Finset.mem_univ
                        (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1'0] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids_a i).depth) ≤ 1 at h2
                have h3 : (kids_a ⟨1, hka1_lt⟩).depth ≤ 0 := by
                  have hle : (kids_a ⟨1, hka1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids_a i).depth) :=
                    Finset.le_sup (f := fun i => (kids_a i).depth)
                      (Finset.mem_univ
                        (⟨1, hka1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_ka1_vj] at h3
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op_d))).sup
                           (fun i => (kids_d i).depth) ≤ 0 at h3
                omega
            · -- j = 1: mirror
              cases h_ka1_vj' : (kids_a ⟨1, hka1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
              | const c1 =>
                -- j=1 mirror of (j=0, c1). v_j = v 1 = 0 (forced), v 0 = active.
                let K_a' : ℝ := 1 - Real.log c1
                cases h_kr0_j1c1 : (kids_r ⟨0, hkr0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                | const r0 =>
                  cases h_kr1_j1c1 : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                  | const r1 =>
                    -- All-const mirror. K-bound with v 0 active.
                    let K_r : ℝ := Real.exp r0 - Real.log r1
                    let K_outer : ℝ := Real.exp K_a' - Real.log K_r
                    let v : Fin 2 → ℝ :=
                      fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                    have h_eq := hr v
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                    rw [h_k1] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                     Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                           v 0 + v 1 at h_eq
                    rw [h_k1'0, h_k1'1'] at h_eq
                    change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                           Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                               Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                     Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                               Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                           v 0 + v 1 at h_eq
                    rw [h_ka0_r, h_ka1_vj', h_kr0_j1c1, h_kr1_j1c1] at h_eq
                    simp only [MinimalBasis.Term.eval] at h_eq
                    have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                    rw [h_vj, Real.exp_zero] at h_eq
                    have h_Ka'_unfold : (1 : ℝ) - Real.log c1 = K_a' := rfl
                    have h_Kr_unfold : Real.exp r0 - Real.log r1 = K_r := rfl
                    rw [h_Ka'_unfold, h_Kr_unfold] at h_eq
                    have h_Kouter_unfold : Real.exp K_a' - Real.log K_r = K_outer := rfl
                    rw [h_Kouter_unfold] at h_eq
                    have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                    rw [h_sum] at h_eq
                    have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                      by linarith [le_abs_self (Real.log K_outer)]
                    have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                    linarith
                  | var n =>
                    rcases n with ⟨_ | _ | _, hn⟩
                    · -- (j=1, c1, const r0, var 0): cross-var, helper #9 with K=K_a', r=r0.
                      let v : Fin 2 → ℝ := fun i => if i = 0
                        then -Real.exp (Real.exp (Real.exp K_a' + Real.exp r0 + 100))
                        else 0
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj', h_kr0_j1c1, h_kr1_j1c1] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                      have h_vn : v ⟨0, hn⟩ =
                          -Real.exp (Real.exp (Real.exp K_a' + Real.exp r0 + 100)) := by simp [v]
                      rw [h_vj, h_vn] at h_eq
                      simp only [Real.exp_zero] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) =
                          -Real.exp (Real.exp (Real.exp K_a' + Real.exp r0 + 100)) := by simp [v]
                      rw [h_sum] at h_eq
                      rw [show Real.exp ((1 : ℝ) - Real.log c1) = Real.exp K_a' from rfl] at h_eq
                      have h_bound := log_triple_nest_witness K_a' r0
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · -- (j=1, c1, const r0, var 1): v_n = v 1 = 0 (matches v_j). K-bound.
                      let K_outer : ℝ := Real.exp K_a' - r0
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj', h_kr0_j1c1, h_kr1_j1c1] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                      rw [h_vj, Real.exp_zero] at h_eq
                      simp only [Real.log_zero, sub_zero] at h_eq
                      rw [Real.log_exp] at h_eq
                      have h_Ka'_unfold : (1 : ℝ) - Real.log c1 = K_a' := rfl
                      rw [h_Ka'_unfold] at h_eq
                      have h_Kouter_unfold : Real.exp K_a' - r0 = K_outer := rfl
                      rw [h_Kouter_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                        by linarith [le_abs_self (Real.log K_outer)]
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · exact absurd hn (by omega)
                  | app op_d kids_d =>
                    exfalso
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids i).depth) ≤ 3 at hd
                    have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                      have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids i).depth) :=
                        Finset.le_sup (f := fun i => (kids i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1] at h1
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids' i).depth) ≤ 2 at h1
                    have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                      have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids' i).depth) :=
                        Finset.le_sup (f := fun i => (kids' i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1'1'] at h2
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids_r i).depth) ≤ 1 at h2
                    have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                      have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids_r i).depth) :=
                        Finset.le_sup (f := fun i => (kids_r i).depth)
                          (Finset.mem_univ
                            (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_kr1_j1c1] at h3
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity op_d))).sup
                               (fun i => (kids_d i).depth) ≤ 0 at h3
                    omega
                | var m =>
                  -- (j=1, c1, var m, ?). Continue on kids_r 1.
                  cases h_kr1_jvm' : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                  | const r1 =>
                    rcases m with ⟨_ | _ | _, hm⟩
                    · -- (j=1, c1, var 0, const r1): v_m = v 0 (active). Apply helper #11.
                      let v : Fin 2 → ℝ := fun i => if i = 0
                        then -Real.exp (Real.exp (Real.exp
                          (|K_a'| + |Real.log r1| + |Real.log (Real.log r1)| + 100)))
                        else 0
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj', h_kr0_j1c1, h_kr1_jvm'] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                      have h_vm : v ⟨0, hm⟩ = -Real.exp (Real.exp (Real.exp
                          (|K_a'| + |Real.log r1| + |Real.log (Real.log r1)| + 100))) := by
                        simp [v]
                      rw [h_vj, h_vm, Real.exp_zero] at h_eq
                      have h_Ka'_unfold : (1 : ℝ) - Real.log c1 = K_a' := rfl
                      rw [h_Ka'_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -Real.exp (Real.exp (Real.exp
                          (|K_a'| + |Real.log r1| + |Real.log (Real.log r1)| + 100))) := by
                        simp [v]
                      rw [h_sum] at h_eq
                      have h_bound := log_triple_nest_swap_bound K_a' (Real.log r1)
                        (-Real.exp (Real.exp (Real.exp
                          (|K_a'| + |Real.log r1| + |Real.log (Real.log r1)| + 100))))
                        (le_refl _)
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · -- (j=1, c1, var 1, const r1): v_m = v 1 = 0. K-bound.
                      let K_r' : ℝ := 1 - Real.log r1
                      let K_outer : ℝ := Real.exp K_a' - Real.log K_r'
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj', h_kr0_j1c1, h_kr1_jvm'] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                      rw [h_vj, Real.exp_zero] at h_eq
                      have h_Ka'_unfold : (1 : ℝ) - Real.log c1 = K_a' := rfl
                      have h_Kr'_unfold : (1 : ℝ) - Real.log r1 = K_r' := rfl
                      rw [h_Ka'_unfold, h_Kr'_unfold] at h_eq
                      have h_Kouter_unfold : Real.exp K_a' - Real.log K_r' = K_outer := rfl
                      rw [h_Kouter_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                        by linarith [le_abs_self (Real.log K_outer)]
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    · exact absurd hm (by omega)
                  | var n =>
                    rcases m with ⟨_ | _ | _, hm⟩
                    · rcases n with ⟨_ | _ | _, hn⟩
                      · -- (j=1, m=0, n=0) same-var deep-nest. Apply helper #10 with K=K_a'.
                        let v : Fin 2 → ℝ := fun i => if i = 0
                          then -Real.exp (Real.exp (Real.exp (|K_a'| + 100)))
                          else 0
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj', h_kr0_j1c1, h_kr1_jvm'] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                        have h_vm : v ⟨0, hm⟩ =
                            -Real.exp (Real.exp (Real.exp (|K_a'| + 100))) := by simp [v]
                        rw [h_vj, h_vm] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) =
                            -Real.exp (Real.exp (Real.exp (|K_a'| + 100))) := by simp [v]
                        rw [h_sum] at h_eq
                        rw [show Real.exp (Real.exp 0 - Real.log c1) = Real.exp K_a' by
                            rw [Real.exp_zero]] at h_eq
                        have h_bound := log_triple_nest_same_var_bound K_a'
                          (-Real.exp (Real.exp (Real.exp (|K_a'| + 100)))) (le_refl _)
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · -- (j=1, m=0, n=1): v_m = v 0 (active), v_n = v 1 = 0. Use helper #2.
                        let v : Fin 2 → ℝ :=
                          fun i => if i = 0 then -(|K_a'| + 2) else 0
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj', h_kr0_j1c1, h_kr1_jvm'] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                        have h_vm : v ⟨0, hm⟩ = -(|K_a'| + 2) := by simp [v]
                        rw [h_vj, h_vm] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                        rw [Real.log_exp] at h_eq
                        have h_Ka'_unfold : (1 : ℝ) - Real.log c1 = K_a' := rfl
                        rw [h_Ka'_unfold] at h_eq
                        have h_simp : Real.exp K_a' - -(|K_a'| + 2) =
                                      Real.exp K_a' + |K_a'| + 2 := by ring
                        rw [h_simp] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -(|K_a'| + 2) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_log_bound : Real.log (Real.exp K_a' + |K_a'| + 2) ≤ |K_a'| + 2 :=
                          log_exp_a_plus_abs_a_plus_two_le K_a'
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · exact absurd hn (by omega)
                    · rcases n with ⟨_ | _ | _, hn⟩
                      · -- (j=1, m=1, n=0) cross-var deep-nest. Apply helper #9 (K=K_a', r=0).
                        let v : Fin 2 → ℝ := fun i => if i = 0
                          then -Real.exp (Real.exp (Real.exp K_a' + Real.exp 0 + 100))
                          else 0
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj', h_kr0_j1c1, h_kr1_jvm'] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                        have h_vn : v ⟨0, hn⟩ =
                            -Real.exp (Real.exp (Real.exp K_a' + Real.exp 0 + 100)) := by
                          simp [v]
                        rw [h_vj, h_vn] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) =
                            -Real.exp (Real.exp (Real.exp K_a' + Real.exp 0 + 100)) := by simp [v]
                        rw [h_sum] at h_eq
                        rw [show Real.exp (Real.exp 0 - Real.log c1) = Real.exp K_a' by
                            rw [Real.exp_zero]] at h_eq
                        have h_bound := log_triple_nest_witness K_a' 0
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · -- (j=1, m=1, n=1): v_m = v_n = v 1 = 0. K-bound, K_outer = exp K_a'.
                        let K_outer : ℝ := Real.exp K_a'
                        let v : Fin 2 → ℝ :=
                          fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj', h_kr0_j1c1, h_kr1_jvm'] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                        rw [h_vj] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero, Real.log_one] at h_eq
                        have h_Ka'_unfold : (1 : ℝ) - Real.log c1 = K_a' := rfl
                        rw [h_Ka'_unfold] at h_eq
                        have h_Kouter_unfold : Real.exp K_a' = K_outer := rfl
                        rw [h_Kouter_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                          by linarith [le_abs_self (Real.log K_outer)]
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · exact absurd hn (by omega)
                    · exact absurd hm (by omega)
                  | app op_d kids_d =>
                    -- Depth contra: kids_r 1 = .app.
                    exfalso
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids i).depth) ≤ 3 at hd
                    have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                      have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids i).depth) :=
                        Finset.le_sup (f := fun i => (kids i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1] at h1
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids' i).depth) ≤ 2 at h1
                    have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                      have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids' i).depth) :=
                        Finset.le_sup (f := fun i => (kids' i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1'1'] at h2
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids_r i).depth) ≤ 1 at h2
                    have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                      have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids_r i).depth) :=
                        Finset.le_sup (f := fun i => (kids_r i).depth)
                          (Finset.mem_univ
                            (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_kr1_jvm'] at h3
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity op_d))).sup
                               (fun i => (kids_d i).depth) ≤ 0 at h3
                    omega
                | app op_d kids_d =>
                  -- Depth contra: kids_r 0 = .app.
                  exfalso
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids i).depth) ≤ 3 at hd
                  have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                    have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids i).depth) :=
                      Finset.le_sup (f := fun i => (kids i).depth)
                        (Finset.mem_univ
                          (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k1] at h1
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids' i).depth) ≤ 2 at h1
                  have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                    have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids' i).depth) :=
                      Finset.le_sup (f := fun i => (kids' i).depth)
                        (Finset.mem_univ
                          (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_k1'1'] at h2
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                             (fun i => (kids_r i).depth) ≤ 1 at h2
                  have h3 : (kids_r ⟨0, hkr0_lt⟩).depth ≤ 0 := by
                    have hle : (kids_r ⟨0, hkr0_lt⟩).depth ≤
                        (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                          (fun i => (kids_r i).depth) :=
                      Finset.le_sup (f := fun i => (kids_r i).depth)
                        (Finset.mem_univ
                          (⟨0, hkr0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                    omega
                  rw [h_kr0_j1c1] at h3
                  change 1 + (Finset.univ :
                      Finset (Fin (EmlBasis.arity op_d))).sup
                             (fun i => (kids_d i).depth) ≤ 0 at h3
                  omega
              | var l =>
                rcases l with ⟨_ | _ | _, hl⟩
                · -- l = 0: kids_a 0 = var 1, kids_a 1 = var 0. Cross-var.
                  -- Diagonal witness v_0 = v_1 = t_w. Apply cross_var_diagonal_contra.
                  cases h_kr0_jvl1c : (kids_r ⟨0, hkr0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                  | const r0 =>
                    cases h_kr1_jvl1c : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                    | const r1 =>
                      -- Shape 1 (const, const): B := log(exp r0 - log r1).
                      let B : ℝ := Real.log (Real.exp r0 - Real.log r1)
                      let t_w : ℝ := -|B| - Real.exp 1 - 1
                      let v : Fin 2 → ℝ := fun i => if i = 0 then t_w else t_w
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1c, h_kr1_jvl1c] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0 + 1, hj⟩ = t_w := by simp [v]
                      have h_vl : v ⟨0, hl⟩ = t_w := by simp [v]
                      rw [h_vj, h_vl] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = 2 * t_w := by simp [v]; ring
                      rw [h_sum] at h_eq
                      have h_B_unfold : Real.log (Real.exp r0 - Real.log r1) = B := rfl
                      rw [h_B_unfold] at h_eq
                      -- Now apply cross_var_diagonal_contra.
                      have h_K_pos : (0 : ℝ) < Real.exp ((kids ⟨0, hk0_lt⟩).eval v) :=
                        Real.exp_pos _
                      have hB_nn : (0 : ℝ) ≤ |B| := abs_nonneg B
                      have h_exp_1_pos : Real.exp 1 > 0 := Real.exp_pos 1
                      have h_exp_1_ge_2 : Real.exp 1 ≥ 2 := by
                        have := Real.add_one_le_exp (1:ℝ); linarith
                      have h_t_neg : t_w < 0 := by simp [t_w]; linarith
                      have h_neg_t_pos : -t_w > 0 := by linarith
                      have h_neg_t_ge_1 : -t_w ≥ 1 := by simp [t_w]; linarith
                      -- exp t_w ≤ 1, log t_w ≥ 0.
                      have h_exp_tw_le_1 : Real.exp t_w ≤ 1 := by
                        rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
                        exact Real.exp_le_exp.mpr (le_of_lt h_t_neg)
                      have h_exp_tw_pos : Real.exp t_w > 0 := Real.exp_pos t_w
                      have h_log_tw_eq : Real.log t_w = Real.log (-t_w) := by
                        conv_lhs => rw [show t_w = -(-t_w) from by ring]
                        rw [Real.log_neg_eq_log]
                      have h_log_tw_nn : Real.log t_w ≥ 0 := by
                        rw [h_log_tw_eq]; exact Real.log_nonneg h_neg_t_ge_1
                      have h_Q_le_1 : Real.exp t_w - Real.log t_w ≤ 1 := by linarith
                      have h_eQ_le : Real.exp (Real.exp t_w - Real.log t_w) ≤ Real.exp 1 :=
                        Real.exp_le_exp.mpr h_Q_le_1
                      have h_eQ_pos : Real.exp (Real.exp t_w - Real.log t_w) > 0 := Real.exp_pos _
                      have h_Y_abs_le :
                          |Real.exp (Real.exp t_w - Real.log t_w) - B| ≤ Real.exp 1 + |B| := by
                        calc |Real.exp (Real.exp t_w - Real.log t_w) - B|
                            ≤ |Real.exp (Real.exp t_w - Real.log t_w)| + |B| := abs_sub _ _
                          _ = Real.exp (Real.exp t_w - Real.log t_w) + |B| := by
                              rw [abs_of_pos h_eQ_pos]
                          _ ≤ Real.exp 1 + |B| := by linarith
                      have h_Y_upper :
                          Real.log (Real.exp (Real.exp t_w - Real.log t_w) - B) ≤ -t_w := by
                        have h_log_eq_abs :
                            Real.log (Real.exp (Real.exp t_w - Real.log t_w) - B) =
                            Real.log |Real.exp (Real.exp t_w - Real.log t_w) - B| :=
                          (Real.log_abs _).symm
                        rw [h_log_eq_abs]
                        have h_sum_pos : (0 : ℝ) < Real.exp 1 + |B| := by linarith
                        by_cases h_Y_zero : Real.exp (Real.exp t_w - Real.log t_w) - B = 0
                        · rw [h_Y_zero, abs_zero, Real.log_zero]; linarith
                        · have h_abs_pos :
                              |Real.exp (Real.exp t_w - Real.log t_w) - B| > 0 :=
                            abs_pos.mpr h_Y_zero
                          have h_log_le :
                              Real.log |Real.exp (Real.exp t_w - Real.log t_w) - B| ≤
                              Real.log (Real.exp 1 + |B|) :=
                            Real.log_le_log h_abs_pos h_Y_abs_le
                          have h_log_sum :
                              Real.log (Real.exp 1 + |B|) ≤ Real.exp 1 + |B| - 1 :=
                            Real.log_le_sub_one_of_pos h_sum_pos
                          have : -t_w ≥ Real.exp 1 + |B| + 1 := by simp [t_w]; linarith
                          linarith
                      exact cross_var_diagonal_contra
                        (Real.exp ((kids ⟨0, hk0_lt⟩).eval v))
                        (Real.exp (Real.exp t_w - Real.log t_w) - B)
                        t_w h_K_pos h_Y_upper h_t_neg h_eq
                    | var m =>
                      -- Shape 2 (const r0, var m) under diagonal. S(t_w) = exp(r0) - log(t_w).
                      -- Witness `t_w := -exp(exp r0 + 10)` makes log t_w = exp r0 + 10,
                      -- so S(t_w) = -10 (uniform constant).
                      let t_w : ℝ := -Real.exp (Real.exp r0 + 10)
                      let v : Fin 2 → ℝ := fun i => if i = 0 then t_w else t_w
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1c, h_kr1_jvl1c] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0 + 1, hj⟩ = t_w := by simp [v]
                      have h_vl : v ⟨0, hl⟩ = t_w := by simp [v]
                      have h_vm : v m = t_w := by simp [v, ite_self]
                      rw [h_vj, h_vl, h_vm] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = 2 * t_w := by simp [v]; ring
                      rw [h_sum] at h_eq
                      -- Bound setup.
                      have h_exp_r0_pos : Real.exp r0 > 0 := Real.exp_pos r0
                      have h_inner_ge_10 : Real.exp r0 + 10 ≥ 10 := by linarith
                      have h_exp_10_ge_11 : Real.exp 10 ≥ 11 := by
                        have := Real.add_one_le_exp (10 : ℝ); linarith
                      have h_exp_inner_ge_11 : Real.exp (Real.exp r0 + 10) ≥ 11 := by
                        have h_mono : Real.exp 10 ≤ Real.exp (Real.exp r0 + 10) :=
                          Real.exp_le_exp.mpr h_inner_ge_10
                        linarith
                      have h_t_w_neg : t_w < 0 := by
                        simp [t_w]; exact Real.exp_pos _
                      have h_t_bound : t_w ≤ -3 := by
                        simp [t_w]; linarith
                      have h_neg_t_w_pos : -t_w > 0 := by linarith
                      have h_neg_t_w_eq : -t_w = Real.exp (Real.exp r0 + 10) := by simp [t_w]
                      have h_log_t_w : Real.log t_w = Real.exp r0 + 10 := by
                        rw [show t_w = -(Real.exp (Real.exp r0 + 10)) from rfl]
                        rw [Real.log_neg_eq_log, Real.log_exp]
                      have h_S_val : Real.exp r0 - Real.log t_w = -10 := by
                        rw [h_log_t_w]; ring
                      -- h_S_logbound : |Real.log (Real.exp r0 - Real.log t_w)| ≤ |t_w|.
                      have h_S_logbound :
                          |Real.log (Real.exp r0 - Real.log t_w)| ≤ |t_w| := by
                        rw [h_S_val]
                        -- |Real.log (-10)| = Real.log 10.
                        rw [show (-10 : ℝ) = -(10 : ℝ) from by ring]
                        rw [Real.log_neg_eq_log]
                        have h_log_10_pos : Real.log 10 > 0 := Real.log_pos (by norm_num)
                        rw [abs_of_pos h_log_10_pos]
                        -- Real.log 10 ≤ 9 (via log_le_sub_one).
                        have h_log_10_le : Real.log 10 ≤ 9 := by
                          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 10)
                          linarith
                        -- |t_w| = -t_w = Real.exp (Real.exp r0 + 10) ≥ 11.
                        have h_abs_t_w : |t_w| ≥ 11 := by
                          rw [abs_of_neg h_t_w_neg, h_neg_t_w_eq]; linarith
                        linarith
                      have h_bound := log_diagonal_cross_bound
                        (fun t => Real.exp r0 - Real.log t) t_w h_S_logbound h_t_bound
                      simp only at h_bound
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    | app op_d kids_d =>
                      -- Depth contra: kids_r 1 = .app.
                      exfalso
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids i).depth) ≤ 3 at hd
                      have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                        have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids i).depth) :=
                          Finset.le_sup (f := fun i => (kids i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1] at h1
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids' i).depth) ≤ 2 at h1
                      have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                        have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids' i).depth) :=
                          Finset.le_sup (f := fun i => (kids' i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1'1'] at h2
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids_r i).depth) ≤ 1 at h2
                      have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                        have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids_r i).depth) :=
                          Finset.le_sup (f := fun i => (kids_r i).depth)
                            (Finset.mem_univ
                              (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_kr1_jvl1c] at h3
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity op_d))).sup
                                 (fun i => (kids_d i).depth) ≤ 0 at h3
                      omega
                  | var k =>
                    cases h_kr1_jvl1v : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                    | const r1 =>
                      -- Shape 3 (var k, const r1). Use cross_var_diagonal_contra (one-sided)
                      -- with adaptive exp-deep witness per design note.
                      let t_w : ℝ :=
                        -Real.exp (|Real.log r1| + |Real.log (Real.log r1)| + 11) - 4
                      let v : Fin 2 → ℝ := fun i => if i = 0 then t_w else t_w
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1c, h_kr1_jvl1v] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0 + 1, hj⟩ = t_w := by simp [v]
                      have h_vl : v ⟨0, hl⟩ = t_w := by simp [v]
                      have h_vk : v k = t_w := by simp [v, ite_self]
                      rw [h_vj, h_vl, h_vk] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = 2 * t_w := by simp [v]; ring
                      rw [h_sum] at h_eq
                      -- Setup bounds.
                      have h_log_r1_abs_nn : (0 : ℝ) ≤ |Real.log r1| := abs_nonneg _
                      have h_log_log_r1_abs_nn : (0 : ℝ) ≤ |Real.log (Real.log r1)| :=
                        abs_nonneg _
                      have h_inner_ge_11 :
                          |Real.log r1| + |Real.log (Real.log r1)| + 11 ≥ 11 := by linarith
                      have h_exp_inner_ge_11 :
                          Real.exp (|Real.log r1| + |Real.log (Real.log r1)| + 11) ≥ 12 := by
                        have := Real.add_one_le_exp
                          (|Real.log r1| + |Real.log (Real.log r1)| + 11); linarith
                      have h_t_w_neg : t_w < 0 := by
                        simp [t_w]
                        have := Real.exp_pos
                          (|Real.log r1| + |Real.log (Real.log r1)| + 11); linarith
                      have h_neg_t_w_pos : -t_w > 0 := by linarith
                      have h_neg_t_w_ge_16 : -t_w ≥ 16 := by simp [t_w]; linarith
                      have h_abs_t_w_eq : |t_w| = -t_w := abs_of_neg h_t_w_neg
                      have h_exp_t_w_le_1 : Real.exp t_w ≤ 1 := by
                        rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
                        exact Real.exp_le_exp.mpr (by linarith)
                      have h_exp_t_w_pos : Real.exp t_w > 0 := Real.exp_pos t_w
                      have h_log_t_w_eq : Real.log t_w = Real.log (-t_w) := by
                        conv_lhs => rw [show t_w = -(-t_w) from by ring]
                        rw [Real.log_neg_eq_log]
                      have h_log_neg_t_w_nn : Real.log (-t_w) ≥ 0 :=
                        Real.log_nonneg (by linarith)
                      have h_log_t_w_nn : Real.log t_w ≥ 0 := by
                        rw [h_log_t_w_eq]; exact h_log_neg_t_w_nn
                      have h_Q_le_1 : Real.exp t_w - Real.log t_w ≤ 1 := by linarith
                      have h_exp_Q_le_e : Real.exp (Real.exp t_w - Real.log t_w) ≤ Real.exp 1 :=
                        Real.exp_le_exp.mpr h_Q_le_1
                      have h_exp_1_pos : Real.exp 1 > 0 := Real.exp_pos 1
                      have h_exp_1_lt_3 : Real.exp 1 < 3 := by
                        have := Real.exp_one_lt_d9; linarith
                      have h_exp_Q_pos : Real.exp (Real.exp t_w - Real.log t_w) > 0 :=
                        Real.exp_pos _
                      -- Apply cross_var_diagonal_contra. Goal: derive False from h_eq.
                      have h_K_pos : (0 : ℝ) < Real.exp ((kids ⟨0, hk0_lt⟩).eval v) :=
                        Real.exp_pos _
                      -- Bound Real.log Y ≤ -t_w where Y = exp(Q) - log(S), S = exp(t_w) - log r1.
                      -- By_cases on Real.log r1 = 0 (covers r1 ∈ {0, ±1}).
                      have h_Y_upper :
                          Real.log (Real.exp (Real.exp t_w - Real.log t_w) -
                                    Real.log (Real.exp t_w - Real.log r1)) ≤ -t_w := by
                        by_cases h_log_r1_zero : Real.log r1 = 0
                        · -- Branch A: r1 ∈ {0, ±1}. S = exp(t_w). log S = t_w.
                          rw [h_log_r1_zero, sub_zero, Real.log_exp]
                          -- Now goal: log(exp(Q) - t_w) ≤ -t_w.
                          have h_Y_pos : Real.exp (Real.exp t_w - Real.log t_w) - t_w > 0 := by
                            linarith
                          -- exp Q ≤ e ≤ -t_w/2 for -t_w ≥ 2e. We have -t_w ≥ 16 ≥ 2e ≈ 5.44.
                          have h_e_le_neg_t : Real.exp 1 ≤ -t_w := by linarith
                          have h_Y_le : Real.exp (Real.exp t_w - Real.log t_w) - t_w ≤ 2 * (-t_w) := by
                            linarith
                          have h_2_neg_t_pos : (0 : ℝ) < 2 * (-t_w) := by linarith
                          have h_log_Y_le_log_2_neg_t :
                              Real.log (Real.exp (Real.exp t_w - Real.log t_w) - t_w) ≤
                              Real.log (2 * (-t_w)) :=
                            Real.log_le_log h_Y_pos h_Y_le
                          have h_log_2_neg_t_split :
                              Real.log (2 * (-t_w)) = Real.log 2 + Real.log (-t_w) :=
                            Real.log_mul (by norm_num) (ne_of_gt h_neg_t_w_pos)
                          have h_log_2_le_1 : Real.log 2 ≤ 1 := by
                            have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
                            linarith
                          have h_log_neg_t_le : Real.log (-t_w) ≤ -t_w - 1 :=
                            Real.log_le_sub_one_of_pos h_neg_t_w_pos
                          linarith
                        · -- Branch B: Real.log r1 ≠ 0. |log r1| > 0.
                          -- Bound |log S| via |S| ≥ |log r1|/2 (exp-deep witness).
                          have h_S_abs_le :
                              |Real.exp t_w - Real.log r1| ≤ 1 + |Real.log r1| := by
                            calc |Real.exp t_w - Real.log r1|
                                ≤ |Real.exp t_w| + |Real.log r1| := abs_sub _ _
                              _ = Real.exp t_w + |Real.log r1| := by
                                  rw [abs_of_pos h_exp_t_w_pos]
                              _ ≤ 1 + |Real.log r1| := by linarith
                          have h_log_r1_abs_pos : |Real.log r1| > 0 :=
                            abs_pos.mpr h_log_r1_zero
                          -- Linearize the witness via add_one_le_exp.
                          have h_t_w_linear :
                              t_w ≤ -|Real.log r1| - |Real.log (Real.log r1)| - 16 := by
                            have h_exp_ge :
                                Real.exp (|Real.log r1| + |Real.log (Real.log r1)| + 11)
                                  ≥ |Real.log r1| + |Real.log (Real.log r1)| + 12 := by
                              have := Real.add_one_le_exp
                                (|Real.log r1| + |Real.log (Real.log r1)| + 11)
                              linarith
                            simp [t_w]; linarith
                          -- Split exp(t_w) into three factors via Real.exp_add.
                          have h_exp_t_w_split :
                              Real.exp t_w ≤
                              Real.exp (-|Real.log r1|) *
                              Real.exp (-|Real.log (Real.log r1)|) *
                              Real.exp (-16) := by
                            have h := Real.exp_le_exp.mpr h_t_w_linear
                            rw [show (-|Real.log r1| - |Real.log (Real.log r1)| - 16 : ℝ) =
                                (-|Real.log r1|) + (-|Real.log (Real.log r1)|) + (-16) from by ring,
                                Real.exp_add, Real.exp_add] at h
                            exact h
                          -- Numeric bounds on the three factors.
                          have h_exp_neg_abs_log_r1_le_1 :
                              Real.exp (-|Real.log r1|) ≤ 1 := by
                            rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
                            exact Real.exp_le_exp.mpr (neg_nonpos.mpr (abs_nonneg _))
                          have h_exp_1_ge_2 : Real.exp 1 ≥ 2 := by
                            have := Real.add_one_le_exp (1 : ℝ); linarith
                          have h_exp_neg_16_le_half : Real.exp (-16 : ℝ) ≤ 1 / 2 := by
                            have h_exp_16_pos : (0 : ℝ) < Real.exp 16 := Real.exp_pos _
                            have h_exp_neg_16_pos : (0 : ℝ) < Real.exp (-16) := Real.exp_pos _
                            have h_ge_2 : (2 : ℝ) ≤ Real.exp 16 := by
                              have h1 : Real.exp 1 ≤ Real.exp 16 :=
                                Real.exp_le_exp.mpr (by norm_num)
                              linarith
                            have h_prod : Real.exp (-16) * Real.exp 16 = 1 := by
                              rw [← Real.exp_add]; simp
                            nlinarith [h_prod, h_exp_neg_16_pos, h_exp_16_pos, h_ge_2]
                          -- Case-split |log r1| < 1 vs ≥ 1 to bound exp(-|log log r1|).
                          have h_exp_t_w_le_half_log_r1 :
                              Real.exp t_w ≤ |Real.log r1| / 2 := by
                            by_cases h_lt_1 : |Real.log r1| < 1
                            · -- Case A: |log r1| < 1. exp(-|log log r1|) = |log r1|.
                              have h_log_log_r1_neg : Real.log (Real.log r1) < 0 := by
                                rw [← Real.log_abs]
                                exact Real.log_neg h_log_r1_abs_pos h_lt_1
                              have h_abs_log_log_eq :
                                  |Real.log (Real.log r1)| = -Real.log (Real.log r1) :=
                                abs_of_neg h_log_log_r1_neg
                              have h_exp_neg_log_log_eq :
                                  Real.exp (-|Real.log (Real.log r1)|) = |Real.log r1| := by
                                rw [h_abs_log_log_eq, neg_neg]
                                rw [show Real.log (Real.log r1) = Real.log |Real.log r1| from
                                    (Real.log_abs _).symm]
                                exact Real.exp_log h_log_r1_abs_pos
                              rw [h_exp_neg_log_log_eq] at h_exp_t_w_split
                              -- Chain: exp t_w ≤ exp(-|log r1|) * |log r1| * exp(-16) ≤
                              --                  1 * |log r1| * (1/2) = |log r1|/2.
                              have h_log_r1_abs_nn : (0 : ℝ) ≤ |Real.log r1| := abs_nonneg _
                              have h_exp_neg_log_r1_nn :
                                  (0 : ℝ) ≤ Real.exp (-|Real.log r1|) := (Real.exp_pos _).le
                              have h_exp_neg_16_nn :
                                  (0 : ℝ) ≤ Real.exp (-16 : ℝ) := (Real.exp_pos _).le
                              have h_step1 :
                                  Real.exp (-|Real.log r1|) * |Real.log r1| ≤
                                  1 * |Real.log r1| :=
                                mul_le_mul_of_nonneg_right h_exp_neg_abs_log_r1_le_1
                                  h_log_r1_abs_nn
                              have h_step2 :
                                  Real.exp (-|Real.log r1|) * |Real.log r1| *
                                  Real.exp (-16) ≤
                                  1 * |Real.log r1| * (1 / 2) := by
                                have h_left_nn :
                                    (0 : ℝ) ≤ Real.exp (-|Real.log r1|) * |Real.log r1| :=
                                  mul_nonneg h_exp_neg_log_r1_nn h_log_r1_abs_nn
                                have h_right_nn : (0 : ℝ) ≤ 1 * |Real.log r1| := by
                                  positivity
                                have h_a :
                                    Real.exp (-|Real.log r1|) * |Real.log r1| *
                                    Real.exp (-16) ≤
                                    1 * |Real.log r1| * Real.exp (-16) :=
                                  mul_le_mul_of_nonneg_right h_step1 h_exp_neg_16_nn
                                have h_b :
                                    1 * |Real.log r1| * Real.exp (-16) ≤
                                    1 * |Real.log r1| * (1 / 2) :=
                                  mul_le_mul_of_nonneg_left h_exp_neg_16_le_half h_right_nn
                                linarith
                              linarith
                            · -- Case B: |log r1| ≥ 1. exp(-|log log r1|) ≤ 1.
                              push_neg at h_lt_1
                              have h_exp_neg_log_log_le_1 :
                                  Real.exp (-|Real.log (Real.log r1)|) ≤ 1 := by
                                rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
                                exact Real.exp_le_exp.mpr (neg_nonpos.mpr (abs_nonneg _))
                              have h_e_neg_log_log_nn :
                                  (0 : ℝ) ≤ Real.exp (-|Real.log (Real.log r1)|) :=
                                (Real.exp_pos _).le
                              have h_e_neg_r1_nn :
                                  (0 : ℝ) ≤ Real.exp (-|Real.log r1|) := (Real.exp_pos _).le
                              have h_e_neg_16_nn :
                                  (0 : ℝ) ≤ Real.exp (-16 : ℝ) := (Real.exp_pos _).le
                              -- exp(-|log r1|) * exp(-|log log r1|) ≤ 1 * 1
                              have h_step1 :
                                  Real.exp (-|Real.log r1|) *
                                  Real.exp (-|Real.log (Real.log r1)|) ≤ 1 := by
                                have h_a :
                                    Real.exp (-|Real.log r1|) *
                                    Real.exp (-|Real.log (Real.log r1)|) ≤
                                    1 * Real.exp (-|Real.log (Real.log r1)|) :=
                                  mul_le_mul_of_nonneg_right
                                    h_exp_neg_abs_log_r1_le_1 h_e_neg_log_log_nn
                                linarith
                              have h_step1_nn :
                                  (0 : ℝ) ≤ Real.exp (-|Real.log r1|) *
                                            Real.exp (-|Real.log (Real.log r1)|) :=
                                mul_nonneg h_e_neg_r1_nn h_e_neg_log_log_nn
                              have h_step2 :
                                  Real.exp (-|Real.log r1|) *
                                  Real.exp (-|Real.log (Real.log r1)|) *
                                  Real.exp (-16) ≤ 1 * Real.exp (-16) :=
                                mul_le_mul_of_nonneg_right h_step1 h_e_neg_16_nn
                              -- 1 * exp(-16) ≤ 1/2 ≤ |log r1| / 2.
                              linarith
                          -- |S| ≥ |log r1|/2 via reverse triangle.
                          have h_S_abs_ge_half :
                              |Real.exp t_w - Real.log r1| ≥ |Real.log r1| / 2 := by
                            have h_exp_abs : |Real.exp t_w| = Real.exp t_w :=
                              abs_of_pos h_exp_t_w_pos
                            have h_swap : |Real.exp t_w - Real.log r1| =
                                          |Real.log r1 - Real.exp t_w| := by
                              rw [show Real.exp t_w - Real.log r1 =
                                       -(Real.log r1 - Real.exp t_w) from by ring,
                                  abs_neg]
                            rw [h_swap]
                            have h2 := abs_sub_abs_le_abs_sub (Real.log r1) (Real.exp t_w)
                            have h4 : |Real.log r1| - |Real.exp t_w| ≤
                                      |Real.log r1 - Real.exp t_w| := by
                              have := le_abs_self (|Real.log r1| - |Real.exp t_w|)
                              linarith
                            rw [h_exp_abs] at h4
                            linarith
                          -- log|S| upper: ≤ |log r1| via log_le_sub_one.
                          have h_S_pos : |Real.exp t_w - Real.log r1| > 0 := by linarith
                          have h_log_S_eq_log_abs :
                              Real.log (Real.exp t_w - Real.log r1) =
                              Real.log |Real.exp t_w - Real.log r1| :=
                            (Real.log_abs _).symm
                          have h_log_S_abs_upper :
                              Real.log |Real.exp t_w - Real.log r1| ≤ |Real.log r1| := by
                            have h_le := Real.log_le_log h_S_pos h_S_abs_le
                            have h_sum_pos : (0 : ℝ) < 1 + |Real.log r1| := by linarith
                            have h_log_sum := Real.log_le_sub_one_of_pos h_sum_pos
                            linarith
                          -- log|S| lower: ≥ -|log log r1| - 1 via log_le_log on |S| ≥ |log r1|/2.
                          have h_log_half_log_r1 :
                              Real.log (|Real.log r1| / 2) ≥
                              -|Real.log (Real.log r1)| - 1 := by
                            have h_log_split :
                                Real.log (|Real.log r1| / 2) =
                                Real.log |Real.log r1| - Real.log 2 := by
                              rw [Real.log_div (ne_of_gt h_log_r1_abs_pos)
                                  (by norm_num : (2:ℝ) ≠ 0)]
                            rw [h_log_split]
                            have h_log_abs_eq :
                                Real.log |Real.log r1| = Real.log (Real.log r1) :=
                              Real.log_abs _
                            have h_neg_abs_le :
                                -|Real.log (Real.log r1)| ≤ Real.log (Real.log r1) :=
                              neg_abs_le _
                            have h_log_2_le_1 : Real.log 2 ≤ 1 := by
                              have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
                              linarith
                            linarith
                          have h_log_S_abs_lower :
                              Real.log |Real.exp t_w - Real.log r1| ≥
                              -|Real.log (Real.log r1)| - 1 := by
                            have h_le := Real.log_le_log
                              (by linarith : (0:ℝ) < |Real.log r1| / 2) h_S_abs_ge_half
                            linarith
                          -- |log S| ≤ |log r1| + |log log r1| + 1.
                          have h_log_S_abs_bound :
                              |Real.log (Real.exp t_w - Real.log r1)| ≤
                              |Real.log r1| + |Real.log (Real.log r1)| + 1 := by
                            rw [h_log_S_eq_log_abs]
                            by_cases h : 0 ≤ Real.log |Real.exp t_w - Real.log r1|
                            · rw [abs_of_nonneg h]; linarith
                            · push_neg at h
                              rw [abs_of_neg h]; linarith
                          -- |Y| ≤ exp(Q) + |log S| ≤ e + |log r1| + |log log r1| + 1.
                          have h_Y_abs_le :
                              |Real.exp (Real.exp t_w - Real.log t_w) -
                               Real.log (Real.exp t_w - Real.log r1)| ≤
                              Real.exp 1 + |Real.log r1| +
                              |Real.log (Real.log r1)| + 1 := by
                            calc |Real.exp (Real.exp t_w - Real.log t_w) -
                                  Real.log (Real.exp t_w - Real.log r1)|
                                ≤ |Real.exp (Real.exp t_w - Real.log t_w)| +
                                  |Real.log (Real.exp t_w - Real.log r1)| := abs_sub _ _
                              _ = Real.exp (Real.exp t_w - Real.log t_w) +
                                  |Real.log (Real.exp t_w - Real.log r1)| := by
                                    rw [abs_of_pos h_exp_Q_pos]
                              _ ≤ Real.exp 1 +
                                  (|Real.log r1| + |Real.log (Real.log r1)| + 1) := by
                                    linarith
                              _ = Real.exp 1 + |Real.log r1| +
                                  |Real.log (Real.log r1)| + 1 := by ring
                          -- log|Y| ≤ |Y| - 1 ≤ -t_w via exp-depth.
                          have h_log_Y_eq_abs :
                              Real.log (Real.exp (Real.exp t_w - Real.log t_w) -
                                        Real.log (Real.exp t_w - Real.log r1)) =
                              Real.log |Real.exp (Real.exp t_w - Real.log t_w) -
                                        Real.log (Real.exp t_w - Real.log r1)| :=
                            (Real.log_abs _).symm
                          rw [h_log_Y_eq_abs]
                          by_cases h_Y_zero :
                              Real.exp (Real.exp t_w - Real.log t_w) -
                              Real.log (Real.exp t_w - Real.log r1) = 0
                          · rw [h_Y_zero, abs_zero, Real.log_zero]; linarith
                          · have h_Y_abs_pos :
                                |Real.exp (Real.exp t_w - Real.log t_w) -
                                 Real.log (Real.exp t_w - Real.log r1)| > 0 :=
                              abs_pos.mpr h_Y_zero
                            have h_Y_abs_sum_pos : (0 : ℝ) <
                                Real.exp 1 + |Real.log r1| +
                                |Real.log (Real.log r1)| + 1 := by linarith
                            have h_log_le_sum := Real.log_le_log h_Y_abs_pos h_Y_abs_le
                            have h_log_sum_le :
                                Real.log (Real.exp 1 + |Real.log r1| +
                                          |Real.log (Real.log r1)| + 1) ≤
                                Real.exp 1 + |Real.log r1| +
                                |Real.log (Real.log r1)| := by
                              have := Real.log_le_sub_one_of_pos h_Y_abs_sum_pos
                              linarith
                            have h_neg_t_w_ge_sum : -t_w ≥
                                Real.exp 1 + |Real.log r1| +
                                |Real.log (Real.log r1)| := by
                              have h_inner_ge_e :
                                  Real.exp (|Real.log r1| +
                                            |Real.log (Real.log r1)| + 11) ≥
                                  |Real.log r1| + |Real.log (Real.log r1)| + 12 := by
                                have := Real.add_one_le_exp
                                  (|Real.log r1| + |Real.log (Real.log r1)| + 11)
                                linarith
                              simp [t_w]; linarith [h_exp_1_lt_3]
                            linarith
                      exact cross_var_diagonal_contra
                        (Real.exp ((kids ⟨0, hk0_lt⟩).eval v))
                        (Real.exp (Real.exp t_w - Real.log t_w) -
                         Real.log (Real.exp t_w - Real.log r1))
                        t_w h_K_pos h_Y_upper h_t_w_neg h_eq
                    | var k' =>
                      -- Shape 4 (var k, var k') under diagonal. S(t_w) = exp(t_w) - log(t_w) = Q.
                      let t_w : ℝ := -10
                      let v : Fin 2 → ℝ := fun i => if i = 0 then t_w else t_w
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1c, h_kr1_jvl1v] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0 + 1, hj⟩ = t_w := by simp [v]
                      have h_vl : v ⟨0, hl⟩ = t_w := by simp [v]
                      have h_vk : v k = t_w := by simp [v, ite_self]
                      have h_vk' : v k' = t_w := by simp [v, ite_self]
                      rw [h_vj, h_vl, h_vk, h_vk'] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = 2 * t_w := by simp [v]; ring
                      rw [h_sum] at h_eq
                      have h_t_bound : t_w ≤ -3 := by norm_num [t_w]
                      have h_t_lt_0 : t_w < 0 := by norm_num [t_w]
                      have h_abs_t : |t_w| = -t_w := abs_of_neg h_t_lt_0
                      have h_neg_t_ge_3 : -t_w ≥ 3 := by norm_num [t_w]
                      have h_neg_t_pos : (0 : ℝ) < -t_w := by norm_num [t_w]
                      have h_S_logbound :
                          |Real.log (Real.exp t_w - Real.log t_w)| ≤ |t_w| := by
                        have h_exp_tw_le_1 : Real.exp t_w ≤ 1 := by
                          rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
                          exact Real.exp_le_exp.mpr (by linarith)
                        have h_exp_tw_pos : Real.exp t_w > 0 := Real.exp_pos t_w
                        have h_log_tw_eq : Real.log t_w = Real.log (-t_w) := by
                          conv_lhs => rw [show t_w = -(-t_w) from by ring]
                          rw [Real.log_neg_eq_log]
                        have h_exp_1_lt_3 : Real.exp 1 < 3 := by
                          have := Real.exp_one_lt_d9; linarith
                        have h_log_3_ge_1 : Real.log 3 ≥ 1 := by
                          have h : Real.log (Real.exp 1) ≤ Real.log 3 :=
                            Real.log_le_log (Real.exp_pos 1) (le_of_lt h_exp_1_lt_3)
                          rw [Real.log_exp] at h; exact h
                        have h_log_neg_t_ge_1 : Real.log (-t_w) ≥ 1 := by
                          have h : Real.log 3 ≤ Real.log (-t_w) :=
                            Real.log_le_log (by norm_num : (0:ℝ) < 3) h_neg_t_ge_3
                          linarith
                        have h_log_tw_ge_1 : Real.log t_w ≥ 1 := by
                          rw [h_log_tw_eq]; exact h_log_neg_t_ge_1
                        have h_Q_neg : Real.exp t_w - Real.log t_w ≤ 0 := by linarith
                        have h_Q_abs_le_log :
                            |Real.exp t_w - Real.log t_w| ≤ Real.log (-t_w) := by
                          rw [abs_of_nonpos h_Q_neg]
                          rw [h_log_tw_eq]; linarith
                        have h_Q_abs_ge_1 : |Real.exp t_w - Real.log t_w| ≥ 1 := by
                          rw [abs_of_nonpos h_Q_neg, h_log_tw_eq]
                          have h_log_10 : Real.log 10 ≥ 2 := by
                            have h_exp_2_lt_10 : Real.exp 2 < 10 := by
                              have h_exp_1_sq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
                                rw [show (2 : ℝ) = 1 + 1 from by norm_num, Real.exp_add]
                              have h_exp_1_lt_3 : Real.exp 1 < 3 := by
                                have := Real.exp_one_lt_d9; linarith
                              have h_exp_1_pos : Real.exp 1 > 0 := Real.exp_pos 1
                              rw [h_exp_1_sq]; nlinarith
                            have h := Real.log_le_log (Real.exp_pos 2) (le_of_lt h_exp_2_lt_10)
                            rw [Real.log_exp] at h; exact h
                          have h_log_neg_t : Real.log (-t_w) = Real.log 10 := by
                            simp [t_w]
                          rw [h_log_neg_t]; linarith
                        have h_Q_abs_pos : |Real.exp t_w - Real.log t_w| > 0 := by linarith
                        have h_log_Q_abs_le : Real.log |Real.exp t_w - Real.log t_w| ≤
                                              Real.log (Real.log (-t_w)) := by
                          have h_log_neg_t_pos : Real.log (-t_w) > 0 := by linarith
                          exact Real.log_le_log h_Q_abs_pos h_Q_abs_le_log
                        have h_log_log_le : Real.log (Real.log (-t_w)) ≤ Real.log (-t_w) - 1 :=
                          Real.log_le_sub_one_of_pos (by linarith)
                        have h_log_neg_t_le : Real.log (-t_w) ≤ -t_w - 1 :=
                          Real.log_le_sub_one_of_pos h_neg_t_pos
                        have h_log_Q_abs_nn :
                            Real.log |Real.exp t_w - Real.log t_w| ≥ 0 := by
                          exact Real.log_nonneg (by linarith)
                        have h_log_Q_eq_abs :
                            Real.log (Real.exp t_w - Real.log t_w) =
                            Real.log |Real.exp t_w - Real.log t_w| :=
                          (Real.log_abs _).symm
                        rw [h_log_Q_eq_abs]
                        rw [abs_of_nonneg h_log_Q_abs_nn]
                        linarith
                      have h_bound := log_diagonal_cross_bound
                        (fun t => Real.exp t - Real.log t) t_w h_S_logbound h_t_bound
                      simp only at h_bound
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    | app op_d kids_d =>
                      -- Depth contra: kids_r 1 = .app (inside var k branch).
                      exfalso
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids i).depth) ≤ 3 at hd
                      have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                        have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids i).depth) :=
                          Finset.le_sup (f := fun i => (kids i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1] at h1
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids' i).depth) ≤ 2 at h1
                      have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                        have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids' i).depth) :=
                          Finset.le_sup (f := fun i => (kids' i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1'1'] at h2
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids_r i).depth) ≤ 1 at h2
                      have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                        have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids_r i).depth) :=
                          Finset.le_sup (f := fun i => (kids_r i).depth)
                            (Finset.mem_univ
                              (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_kr1_jvl1v] at h3
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity op_d))).sup
                                 (fun i => (kids_d i).depth) ≤ 0 at h3
                      omega
                  | app op_d kids_d =>
                    -- Depth contra: kids_r 0 = .app.
                    exfalso
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids i).depth) ≤ 3 at hd
                    have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                      have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids i).depth) :=
                        Finset.le_sup (f := fun i => (kids i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1] at h1
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids' i).depth) ≤ 2 at h1
                    have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                      have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids' i).depth) :=
                        Finset.le_sup (f := fun i => (kids' i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1'1'] at h2
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids_r i).depth) ≤ 1 at h2
                    have h3 : (kids_r ⟨0, hkr0_lt⟩).depth ≤ 0 := by
                      have hle : (kids_r ⟨0, hkr0_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids_r i).depth) :=
                        Finset.le_sup (f := fun i => (kids_r i).depth)
                          (Finset.mem_univ
                            (⟨0, hkr0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_kr0_jvl1c] at h3
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity op_d))).sup
                               (fun i => (kids_d i).depth) ≤ 0 at h3
                    omega
                · -- l = 1: kids_a 0 = var 1 = kids_a 1. Same-var. v_1 = 0 ⇒ (kids' 0).eval = 1.
                  -- K_a := 1. Active variable v_0. Mirror of j=0 l=0 expansion.
                  let K_a : ℝ := 1
                  cases h_kr0_jvl1 : (kids_r ⟨0, hkr0_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                  | const r0 =>
                    cases h_kr1_jvl1 : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                    | const r1 =>
                      -- All const. K_r = exp r0 - log r1. K-bound on v 0.
                      let K_r : ℝ := Real.exp r0 - Real.log r1
                      let K_outer : ℝ := Real.exp K_a - Real.log K_r
                      let v : Fin 2 → ℝ :=
                        fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                      have h_eq := hr v
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                      rw [h_k1] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                       Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                             v 0 + v 1 at h_eq
                      rw [h_k1'0, h_k1'1'] at h_eq
                      change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                             Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                 Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                       Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                 Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                             v 0 + v 1 at h_eq
                      rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1, h_kr1_jvl1] at h_eq
                      simp only [MinimalBasis.Term.eval] at h_eq
                      have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                      rw [h_vj] at h_eq
                      simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                      have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                      rw [h_Ka_unfold] at h_eq
                      have h_Kr_unfold : Real.exp r0 - Real.log r1 = K_r := rfl
                      rw [h_Kr_unfold] at h_eq
                      have h_Kouter_unfold : Real.exp K_a - Real.log K_r = K_outer := rfl
                      rw [h_Kouter_unfold] at h_eq
                      have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                      rw [h_sum] at h_eq
                      have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                        by linarith [le_abs_self (Real.log K_outer)]
                      have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                      linarith
                    | var m =>
                      rcases m with ⟨_ | _ | _, hm⟩
                      · -- (const r0, var m=0): v_m = v_0 active. log_triple_nest_witness K_a r0.
                        let v : Fin 2 → ℝ := fun i => if i = 0
                          then -Real.exp (Real.exp (Real.exp K_a + Real.exp r0 + 100))
                          else 0
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1, h_kr1_jvl1] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                        have h_vm : v ⟨0, hm⟩ =
                            -Real.exp (Real.exp (Real.exp K_a + Real.exp r0 + 100)) := by
                          simp [v]
                        rw [h_vj, h_vm] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                        have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) =
                            -Real.exp (Real.exp (Real.exp K_a + Real.exp r0 + 100)) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_bound := log_triple_nest_witness K_a r0
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · -- (const r0, var m=1): v_m = v_1 = 0. K-bound K_outer = exp K_a - r0.
                        let K_outer : ℝ := Real.exp K_a - r0
                        let v : Fin 2 → ℝ :=
                          fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1, h_kr1_jvl1] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                        rw [h_vj] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                        rw [Real.log_exp] at h_eq
                        have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_Kouter_unfold : Real.exp K_a - r0 = K_outer := rfl
                        rw [h_Kouter_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                          by linarith [le_abs_self (Real.log K_outer)]
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · exact absurd hm (by omega)
                    | app op_d kids_d =>
                      exfalso
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids i).depth) ≤ 3 at hd
                      have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                        have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids i).depth) :=
                          Finset.le_sup (f := fun i => (kids i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1] at h1
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids' i).depth) ≤ 2 at h1
                      have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                        have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids' i).depth) :=
                          Finset.le_sup (f := fun i => (kids' i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1'1'] at h2
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids_r i).depth) ≤ 1 at h2
                      have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                        have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids_r i).depth) :=
                          Finset.le_sup (f := fun i => (kids_r i).depth)
                            (Finset.mem_univ
                              (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_kr1_jvl1] at h3
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity op_d))).sup
                                 (fun i => (kids_d i).depth) ≤ 0 at h3
                      omega
                  | var k =>
                    cases h_kr1_jvl1vk : (kids_r ⟨1, hkr1_lt⟩ : MinimalBasis.Term EmlBasis 2) with
                    | const r1 =>
                      rcases k with ⟨_ | _ | _, hk⟩
                      · -- (k=0, const r1): v_k = v_0 active. Apply helper #11.
                        let v : Fin 2 → ℝ := fun i => if i = 0
                          then -Real.exp (Real.exp (Real.exp
                            (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100)))
                          else 0
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1, h_kr1_jvl1vk] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                        have h_vk : v ⟨0, hk⟩ = -Real.exp (Real.exp (Real.exp
                            (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100))) := by
                          simp [v]
                        rw [h_vj, h_vk] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                        have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -Real.exp (Real.exp (Real.exp
                            (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100))) := by
                          simp [v]
                        rw [h_sum] at h_eq
                        have h_bound := log_triple_nest_swap_bound K_a (Real.log r1)
                          (-Real.exp (Real.exp (Real.exp
                            (|K_a| + |Real.log r1| + |Real.log (Real.log r1)| + 100))))
                          (le_refl _)
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · -- (k=1, const r1): v_k = v_1 = 0. K_r = 1 - log r1. K-bound.
                        let K_r : ℝ := 1 - Real.log r1
                        let K_outer : ℝ := Real.exp K_a - Real.log K_r
                        let v : Fin 2 → ℝ :=
                          fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                        have h_eq := hr v
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                        rw [h_k1] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                         Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                               v 0 + v 1 at h_eq
                        rw [h_k1'0, h_k1'1'] at h_eq
                        change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                               Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                   Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                         Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                   Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                               v 0 + v 1 at h_eq
                        rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1, h_kr1_jvl1vk] at h_eq
                        simp only [MinimalBasis.Term.eval] at h_eq
                        have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                        rw [h_vj] at h_eq
                        simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                        have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                        rw [h_Ka_unfold] at h_eq
                        have h_Kr_unfold : (1 : ℝ) - Real.log r1 = K_r := rfl
                        rw [h_Kr_unfold] at h_eq
                        have h_Kouter_unfold : Real.exp K_a - Real.log K_r = K_outer := rfl
                        rw [h_Kouter_unfold] at h_eq
                        have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                        rw [h_sum] at h_eq
                        have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                          by linarith [le_abs_self (Real.log K_outer)]
                        have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                        linarith
                      · exact absurd hk (by omega)
                    | var k' =>
                      rcases k with ⟨_ | _ | _, hk⟩
                      · rcases k' with ⟨_ | _ | _, hk'⟩
                        · -- (k=0, k'=0): same-var at v_0 active. log_triple_nest_same_var_bound K_a.
                          let v : Fin 2 → ℝ := fun i => if i = 0
                            then -Real.exp (Real.exp (Real.exp (|K_a| + 100)))
                            else 0
                          have h_eq := hr v
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                          rw [h_k1] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                           Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                                 v 0 + v 1 at h_eq
                          rw [h_k1'0, h_k1'1'] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                     Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                           Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                     Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                                 v 0 + v 1 at h_eq
                          rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1, h_kr1_jvl1vk] at h_eq
                          simp only [MinimalBasis.Term.eval] at h_eq
                          have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                          have h_vk : v ⟨0, hk⟩ =
                              -Real.exp (Real.exp (Real.exp (|K_a| + 100))) := by simp [v]
                          rw [h_vj, h_vk] at h_eq
                          simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                          have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                          rw [h_Ka_unfold] at h_eq
                          have h_sum : (v 0 + v 1 : ℝ) =
                              -Real.exp (Real.exp (Real.exp (|K_a| + 100))) := by simp [v]
                          rw [h_sum] at h_eq
                          have h_bound := log_triple_nest_same_var_bound K_a
                            (-Real.exp (Real.exp (Real.exp (|K_a| + 100)))) (le_refl _)
                          have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                          linarith
                        · -- (k=0, k'=1): cross. v_k = v_0 active, v_k' = v_1 = 0.
                          -- (kids_r 1).eval = 0. (kids' 1).eval = exp(v_0) - 0 = exp(v_0).
                          -- K_outer = exp K_a - v_0. log_exp_a_plus_abs_a_plus_two_le K_a.
                          let v : Fin 2 → ℝ :=
                            fun i => if i = 0 then -(|K_a| + 2) else 0
                          have h_eq := hr v
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                          rw [h_k1] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                           Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                                 v 0 + v 1 at h_eq
                          rw [h_k1'0, h_k1'1'] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                     Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                           Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                     Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                                 v 0 + v 1 at h_eq
                          rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1, h_kr1_jvl1vk] at h_eq
                          simp only [MinimalBasis.Term.eval] at h_eq
                          have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                          have h_vk : v ⟨0, hk⟩ = -(|K_a| + 2) := by simp [v]
                          rw [h_vj, h_vk] at h_eq
                          simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                          rw [Real.log_exp] at h_eq
                          have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                          rw [h_Ka_unfold] at h_eq
                          have h_simp : Real.exp K_a - -(|K_a| + 2) =
                                        Real.exp K_a + |K_a| + 2 := by ring
                          rw [h_simp] at h_eq
                          have h_sum : (v 0 + v 1 : ℝ) = -(|K_a| + 2) := by simp [v]
                          rw [h_sum] at h_eq
                          have h_log_bound : Real.log (Real.exp K_a + |K_a| + 2) ≤ |K_a| + 2 :=
                            log_exp_a_plus_abs_a_plus_two_le K_a
                          have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                          linarith
                        · exact absurd hk' (by omega)
                      · rcases k' with ⟨_ | _ | _, hk'⟩
                        · -- (k=1, k'=0): cross mirror. v_k = v_1 = 0, v_k' = v_0 active.
                          -- (kids_r 1).eval = v_0. (kids' 1).eval = exp 0 - log(v_0) = 1 - log(v_0).
                          -- log_triple_nest_witness K_a 0 with t = v_0.
                          let v : Fin 2 → ℝ := fun i => if i = 0
                            then -Real.exp (Real.exp (Real.exp K_a + Real.exp 0 + 100))
                            else 0
                          have h_eq := hr v
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                          rw [h_k1] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                           Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                                 v 0 + v 1 at h_eq
                          rw [h_k1'0, h_k1'1'] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                     Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                           Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                     Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                                 v 0 + v 1 at h_eq
                          rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1, h_kr1_jvl1vk] at h_eq
                          simp only [MinimalBasis.Term.eval] at h_eq
                          have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                          have h_vk' : v ⟨0, hk'⟩ =
                              -Real.exp (Real.exp (Real.exp K_a + Real.exp 0 + 100)) := by
                            simp [v]
                          rw [h_vj, h_vk'] at h_eq
                          simp only [Real.exp_zero, Real.log_zero, sub_zero] at h_eq
                          have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                          rw [h_Ka_unfold] at h_eq
                          have h_sum : (v 0 + v 1 : ℝ) =
                              -Real.exp (Real.exp (Real.exp K_a + Real.exp 0 + 100)) := by simp [v]
                          rw [h_sum] at h_eq
                          have h_bound := log_triple_nest_witness K_a 0
                          simp only [Real.exp_zero, h_Ka_unfold] at h_eq h_bound
                          have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                          linarith
                        · -- (k=1, k'=1): both v_1 = 0. K_outer = exp K_a. K-bound on v_0.
                          let K_outer : ℝ := Real.exp K_a
                          let v : Fin 2 → ℝ :=
                            fun i => if i = 0 then -(|Real.log K_outer| + 1) else 0
                          have h_eq := hr v
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log ((kids ⟨1, hk1_lt⟩).eval v) = v 0 + v 1 at h_eq
                          rw [h_k1] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp ((kids' ⟨0, hk1'0_lt⟩).eval v) -
                                           Real.log ((kids' ⟨1, hk1'1_lt⟩).eval v)) =
                                 v 0 + v 1 at h_eq
                          rw [h_k1'0, h_k1'1'] at h_eq
                          change Real.exp ((kids ⟨0, hk0_lt⟩).eval v) -
                                 Real.log (Real.exp (Real.exp ((kids_a ⟨0, hka0_lt⟩).eval v) -
                                                     Real.log ((kids_a ⟨1, hka1_lt⟩).eval v)) -
                                           Real.log (Real.exp ((kids_r ⟨0, hkr0_lt⟩).eval v) -
                                                     Real.log ((kids_r ⟨1, hkr1_lt⟩).eval v))) =
                                 v 0 + v 1 at h_eq
                          rw [h_ka0_r, h_ka1_vj', h_kr0_jvl1, h_kr1_jvl1vk] at h_eq
                          simp only [MinimalBasis.Term.eval] at h_eq
                          have h_vj : v ⟨0 + 1, hj⟩ = 0 := by simp [v]
                          rw [h_vj] at h_eq
                          simp only [Real.exp_zero, Real.log_zero, sub_zero, Real.log_one] at h_eq
                          have h_Ka_unfold : (1 : ℝ) = K_a := rfl
                          rw [h_Ka_unfold] at h_eq
                          have h_Kouter_unfold : Real.exp K_a = K_outer := rfl
                          rw [h_Kouter_unfold] at h_eq
                          have h_sum : (v 0 + v 1 : ℝ) = -(|Real.log K_outer| + 1) := by simp [v]
                          rw [h_sum] at h_eq
                          have h_RHS_le : -(|Real.log K_outer| + 1) + Real.log K_outer ≤ -1 :=
                            by linarith [le_abs_self (Real.log K_outer)]
                          have h_exp_pos := Real.exp_pos ((kids ⟨0, hk0_lt⟩).eval v)
                          linarith
                        · exact absurd hk' (by omega)
                      · exact absurd hk (by omega)
                    | app op_d kids_d =>
                      exfalso
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids i).depth) ≤ 3 at hd
                      have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                        have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids i).depth) :=
                          Finset.le_sup (f := fun i => (kids i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1] at h1
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids' i).depth) ≤ 2 at h1
                      have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                        have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids' i).depth) :=
                          Finset.le_sup (f := fun i => (kids' i).depth)
                            (Finset.mem_univ
                              (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_k1'1'] at h2
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                                 (fun i => (kids_r i).depth) ≤ 1 at h2
                      have h3 : (kids_r ⟨1, hkr1_lt⟩).depth ≤ 0 := by
                        have hle : (kids_r ⟨1, hkr1_lt⟩).depth ≤
                            (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                              (fun i => (kids_r i).depth) :=
                          Finset.le_sup (f := fun i => (kids_r i).depth)
                            (Finset.mem_univ
                              (⟨1, hkr1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                        omega
                      rw [h_kr1_jvl1vk] at h3
                      change 1 + (Finset.univ :
                          Finset (Fin (EmlBasis.arity op_d))).sup
                                 (fun i => (kids_d i).depth) ≤ 0 at h3
                      omega
                  | app op_d kids_d =>
                    exfalso
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids i).depth) ≤ 3 at hd
                    have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                      have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids i).depth) :=
                        Finset.le_sup (f := fun i => (kids i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1] at h1
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids' i).depth) ≤ 2 at h1
                    have h2 : (kids' ⟨1, hk1'1_lt⟩).depth ≤ 1 := by
                      have hle : (kids' ⟨1, hk1'1_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids' i).depth) :=
                        Finset.le_sup (f := fun i => (kids' i).depth)
                          (Finset.mem_univ
                            (⟨1, hk1'1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_k1'1'] at h2
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                               (fun i => (kids_r i).depth) ≤ 1 at h2
                    have h3 : (kids_r ⟨0, hkr0_lt⟩).depth ≤ 0 := by
                      have hle : (kids_r ⟨0, hkr0_lt⟩).depth ≤
                          (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                            (fun i => (kids_r i).depth) :=
                        Finset.le_sup (f := fun i => (kids_r i).depth)
                          (Finset.mem_univ
                            (⟨0, hkr0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                      omega
                    rw [h_kr0_jvl1] at h3
                    change 1 + (Finset.univ :
                        Finset (Fin (EmlBasis.arity op_d))).sup
                               (fun i => (kids_d i).depth) ≤ 0 at h3
                    omega
                · exact absurd hl (by omega)
              | app op_d kids_d =>
                exfalso
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids i).depth) ≤ 3 at hd
                have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
                  have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids i).depth) :=
                    Finset.le_sup (f := fun i => (kids i).depth)
                      (Finset.mem_univ
                        (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1] at h1
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids' i).depth) ≤ 2 at h1
                have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
                  have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids' i).depth) :=
                    Finset.le_sup (f := fun i => (kids' i).depth)
                      (Finset.mem_univ
                        (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_k1'0] at h2
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                           (fun i => (kids_a i).depth) ≤ 1 at h2
                have h3 : (kids_a ⟨1, hka1_lt⟩).depth ≤ 0 := by
                  have hle : (kids_a ⟨1, hka1_lt⟩).depth ≤
                      (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                        (fun i => (kids_a i).depth) :=
                    Finset.le_sup (f := fun i => (kids_a i).depth)
                      (Finset.mem_univ
                        (⟨1, hka1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
                  omega
                rw [h_ka1_vj'] at h3
                change 1 + (Finset.univ :
                    Finset (Fin (EmlBasis.arity op_d))).sup
                           (fun i => (kids_d i).depth) ≤ 0 at h3
                omega
            · exact absurd hj (by omega)
          | app op_d kids_d =>
            -- Depth contra: kids_a 0 = .app.
            exfalso
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids i).depth) ≤ 3 at hd
            have h1 : (kids ⟨1, hk1_lt⟩).depth ≤ 2 := by
              have hle : (kids ⟨1, hk1_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids i).depth) :=
                Finset.le_sup (f := fun i => (kids i).depth)
                  (Finset.mem_univ
                    (⟨1, hk1_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1] at h1
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids' i).depth) ≤ 2 at h1
            have h2 : (kids' ⟨0, hk1'0_lt⟩).depth ≤ 1 := by
              have hle : (kids' ⟨0, hk1'0_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids' i).depth) :=
                Finset.le_sup (f := fun i => (kids' i).depth)
                  (Finset.mem_univ
                    (⟨0, hk1'0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_k1'0] at h2
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                       (fun i => (kids_a i).depth) ≤ 1 at h2
            have h3 : (kids_a ⟨0, hka0_lt⟩).depth ≤ 0 := by
              have hle : (kids_a ⟨0, hka0_lt⟩).depth ≤
                  (Finset.univ : Finset (Fin (EmlBasis.arity EmlOp.eml))).sup
                    (fun i => (kids_a i).depth) :=
                Finset.le_sup (f := fun i => (kids_a i).depth)
                  (Finset.mem_univ
                    (⟨0, hka0_lt⟩ : Fin (EmlBasis.arity EmlOp.eml)))
              omega
            rw [h_ka0_r] at h3
            change 1 + (Finset.univ :
                Finset (Fin (EmlBasis.arity op_d))).sup
                       (fun i => (kids_d i).depth) ≤ 0 at h3
            omega

end MinimalBasis.EML
