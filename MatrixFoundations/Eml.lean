/-
# EML — Odrzywołek's exp-minus-log operator

Formalization of `eml(x, y) := exp(x) - ln(y)` and the foundational identities
from Odrzywołek (arXiv:2603.21852, April 2026).

This is an early, exploratory file. The framework-based EML obstruction theory
and depth lower bounds live in `Sheffer/Examples/Eml.lean`, built on
`Sheffer/Core.lean`. One legacy `sorry` placeholder remains here for the
Khovanskii-dependent obstruction; the framework version supersedes it.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

namespace EML

/-! ## Target 1 — operator and sanity -/

/-- The EML operator: `eml(x, y) = exp(x) - log(y)`. Defined for all real `x, y`;
the meaningful domain (per Odrzywołek) is `y > 0`, but mathlib's `Real.log` extends
to `ℝ` (with `log(y) = 0` for `y ≤ 0`), so the formula evaluates everywhere. The
elementary-function claims hold on the positive branch.

Marked `noncomputable` because mathlib's `Real.exp` and `Real.log` are; we work
symbolically in proofs, never running `eml` to numeric output inside Lean. The
Python sanity oracle (`proofs/eml.py`) handles numeric checks. -/
noncomputable def eml (x y : ℝ) : ℝ := exp x - log y

/-- §1 sanity. `eml(0, 1) = exp(0) - log(1) = 1 - 0 = 1`. -/
example : eml 0 1 = 1 := by
  simp [eml]

/-- Foundational identity #1 (one level): `exp x = eml(x, 1)`. -/
theorem exp_eq_eml (x : ℝ) : exp x = eml x 1 := by
  simp [eml]

/-- Foundational identity #2 (three levels): `log x = eml(1, eml(eml(1, x), 1))`,
the Odrzywołek formula. Verified by unfolding once and using `Real.log_exp` to
collapse the inner `log(exp(...))`.

This identity holds for *all* real `x`, not just `x > 0`, because mathlib defines
`Real.log` to be `0` on `(-∞, 0]` — the formula still computes `0 = 0` there. -/
theorem log_eq_eml (x : ℝ) :
    log x = eml 1 (eml (eml 1 x) 1) := by
  simp only [eml, Real.log_one, sub_zero, Real.log_exp]
  ring

/-- The operator is symmetric in a degenerate way only when `y = 1`: then
`eml(x, 1) = exp x` and `eml(1, x) = exp 1 − log x = e − log x`, never equal except
at the single fixed point. Recorded as a small example. -/
example : eml 1 1 = Real.exp 1 := by
  simp [eml]

/-! ## Target 2 — addition from EML and 1

Following the OxiEML reference (github.com/cool-japan/oxieml), the explicit
construction is:

  exp(x)   = eml(x, 1)                                    1 level
  log(x)   = eml(1, eml(eml(1, x), 1))                    3 levels  [Odrzywołek]
  sub(x,y) = eml(log x, exp y)                            ~4 levels (x > 0)
  e        = eml(1, 1)                                    1 level
  neg(x)   = sub(sub(e, x), e)  =  (e − x) − e            ~6 levels (x < e)
  add(x,y) = sub(x, neg y)                                ~12 levels

The "5 levels" claim in the abstract / informal writeups is the paper's compiler
output (gradient-based symbolic regression, K=27 for add) — *not* the obvious
sub(x, neg y) construction. Both produce eml-trees expressing add; the obvious
one is what we formalize here, with explicit domain conditions.

**Domain conditions are real and worth flagging** (relevant to Target 4 — the
stylewarning critique). The `sub(x, y) = eml(log x, exp y)` form requires `x > 0`
to give the prose-meaningful answer (for `x ≤ 0` it computes a different number
because mathlib's `log x = 0`). Similarly `neg(x) = (e − x) − e` requires
`x < e`. The composed `add(x, y)` requires `x > 0` and `y > -e + log x` (so the
inner subs all stay in domain). The paper's "all elementary functions" claim is
a global one; the obvious construction has these local restrictions. -/

/-- One-level: `exp x = eml(x, 1)`. -/
noncomputable abbrev myExp (x : ℝ) : ℝ := eml x 1

/-- Three levels: `log x = eml(1, eml(eml(1, x), 1))`. -/
noncomputable abbrev myLog (x : ℝ) : ℝ := eml 1 (eml (eml 1 x) 1)

theorem myExp_eq (x : ℝ) : myExp x = Real.exp x := (exp_eq_eml x).symm

theorem myLog_eq (x : ℝ) : myLog x = Real.log x := (log_eq_eml x).symm

/-- `sub(x, y) = eml(log x, exp y)`. Pure eml-tree: substitute `myLog` and `myExp`
to see the tree. Requires `0 < x` for the prose meaning to match. -/
noncomputable def mySub (x y : ℝ) : ℝ := eml (myLog x) (myExp y)

theorem mySub_eq (x y : ℝ) (hx : 0 < x) : mySub x y = x - y := by
  unfold mySub eml
  rw [myLog_eq, myExp_eq, Real.exp_log hx, Real.log_exp]

/-- `neg(x) = (e − x) − e`. Pure eml-tree (substitute mySub and Real.exp 1).
Requires `x < e` so the inner `e − x > 0` (otherwise the outer mySub's
`log` precondition fails). -/
noncomputable def myNeg (x : ℝ) : ℝ := mySub (mySub (Real.exp 1) x) (Real.exp 1)

theorem myNeg_eq (x : ℝ) (hx : x < Real.exp 1) : myNeg x = -x := by
  unfold myNeg
  have h_inner : mySub (Real.exp 1) x = Real.exp 1 - x :=
    mySub_eq _ _ (Real.exp_pos 1)
  rw [h_inner]
  have h_outer : mySub (Real.exp 1 - x) (Real.exp 1) = Real.exp 1 - x - Real.exp 1 :=
    mySub_eq _ _ (by linarith)
  rw [h_outer]
  ring

/-- `add(x, y) = sub(x, neg y)`. Composes mySub and myNeg; pure eml-tree by
substitution. Requires `0 < x` and `y < e` (so myNeg y is defined). -/
noncomputable def myAdd (x y : ℝ) : ℝ := mySub x (myNeg y)

theorem myAdd_eq (x y : ℝ) (hx : 0 < x) (hy : y < Real.exp 1) :
    myAdd x y = x + y := by
  unfold myAdd
  rw [mySub_eq _ _ hx, myNeg_eq _ hy]
  ring

/-! ## Target 3 — multiplication

`x · y = exp(log x + log y) = myExp(myAdd(myLog x, myLog y))`. Pure eml-tree
by substitution. Domain inherits from myAdd applied to `(log x, log y)`:
the inner needs `0 < log x` (i.e. `1 < x`) AND `log y < e` (i.e. `y < e^e`).

This is *tighter* than addition's domain, exactly because myAdd's
preconditions were already restrictive — composing them onto `log` arguments
narrows further. Each downstream operation inherits *narrower* domains than
its components. **This is the structural pattern Target 4 should formalize.** -/

/-- `mul(x, y) = exp(add(log x, log y))`. Pure eml-tree (substitute myAdd
which substitutes mySub, myNeg, myExp, myLog). Requires `1 < x` and `y < Real.exp (Real.exp 1)`
(roughly `y < 15.15`) — the second arg of myAdd needs `< e`, applied to `log y`. -/
noncomputable def myMul (x y : ℝ) : ℝ := myExp (myAdd (myLog x) (myLog y))

theorem myMul_eq (x y : ℝ) (hx : 1 < x) (hy : y < Real.exp (Real.exp 1)) (hy_pos : 0 < y) :
    myMul x y = x * y := by
  unfold myMul
  rw [myExp_eq]
  rw [myAdd_eq]
  · rw [myLog_eq, myLog_eq]
    rw [Real.exp_add, Real.exp_log hx_pos, Real.exp_log hy_pos]
  · -- 0 < myLog x = log x. Needs 1 < x.
    rw [myLog_eq]
    exact Real.log_pos hx
  · -- myLog y = log y < Real.exp 1
    rw [myLog_eq]
    exact (Real.log_lt_iff_lt_exp hy_pos).mpr hy
  where
    hx_pos : 0 < x := lt_trans zero_lt_one hx

/-! ## Target 4 — Stylewarning's critique, formalized as a framework

Stylewarning (*Not all elementary functions can be expressed with exp-minus-log*,
April 2026) argues that some elementary functions cannot be written as a finite
composition of `eml(x, y) = exp(x) − log(y)` with leaves drawn from input variables
and the constant `1`. His cleanest counterexample is a branch of the generic quintic
root, with the obstruction being **topological Galois theory** (Khovanskii):

- Every EML-term has **solvable monodromy group** (proof by structural induction
  over the eml-tree: `exp` has trivial monodromy, `log` has cyclic ℤ monodromy,
  composition of solvable-monodromy functions is solvable).
- The generic quintic root function has monodromy group `S_5` (classical Galois).
- `S_5` is **not solvable**.
- Therefore, no eml-tree expresses the generic quintic root globally on ℂ.

Formalizing the full monodromy argument requires Riemann-surface and analytic-
continuation machinery beyond mathlib's current coverage. The artifact below is
more modest, in three pieces:

1. **Framework.** A precise inductive type `EmlTree` for finitary eml-trees over
   `n` input variables plus the constant `1`, with evaluation `EmlTree.eval` and
   the predicate `EmlTree.representsGlobally f` saying that the tree's evaluation
   equals `f` at every environment.

2. **Concrete obstruction (proved fully).** The obvious sub-of-neg construction
   for negation does NOT globally represent `−·` on ℝ, witnessed at `x = e + 1`.
   This is the constraint-narrowing finding from Targets 2–3 made formal: even
   for so simple a function as negation, the obvious eml-tree fails outside its
   domain. **This is a weaker claim than "no eml-tree represents negation
   globally" — that stronger claim needs monodromy.**

3. **Khovanskii–Stylewarning theorem (statement, with `sorry`).** No eml-tree of
   any size or topology globally represents the generic quintic root function.
   Proof requires monodromy machinery and is left as a future-work formalization;
   the obstruction is precisely stated. -/

/-- Finitary eml-trees over `n` input variables. Leaves are either the constant
`1` or one of the input variables `var i : Fin n → EmlTree n`; internal nodes
are `eml`. This is the syntactic object Odrzywołek's grammar `S → 1 | eml(S, S)`
generates, parameterized by a finite set of variables. -/
inductive EmlTree (n : ℕ) : Type where
  | one : EmlTree n
  | var : Fin n → EmlTree n
  | eml : EmlTree n → EmlTree n → EmlTree n
  deriving Inhabited

/-- Evaluate an eml-tree at an environment (assignment of values to variables). -/
noncomputable def EmlTree.eval : ∀ {n : ℕ}, EmlTree n → (Fin n → ℝ) → ℝ
  | _, .one,       _   => 1
  | _, .var i,     env => env i
  | _, .eml t₁ t₂, env => EML.eml (t₁.eval env) (t₂.eval env)

/-- `T` globally represents `f` iff `T.eval` equals `f` at every input. -/
def EmlTree.representsGlobally {n : ℕ} (T : EmlTree n) (f : (Fin n → ℝ) → ℝ) :
    Prop :=
  ∀ env, T.eval env = f env

/-- Sanity: the trivial tree `var 0` represents the identity function on ℝ. -/
example : (EmlTree.var 0 : EmlTree 1).representsGlobally (fun env => env 0) := by
  intro env
  simp [EmlTree.eval]

/-- Sanity: the tree `eml (var 0) one` represents `exp ∘ (·)`. -/
example : (EmlTree.eml (EmlTree.var 0) EmlTree.one : EmlTree 1).representsGlobally
    (fun env => Real.exp (env 0)) := by
  intro env
  simp [EmlTree.eval, EML.eml, Real.log_one]

/-! ### The concrete obstruction (proved)

The obvious negation construction (defined as `myNeg` above, which corresponds
to a specific `EmlTree 1`) does NOT globally represent negation. We don't need
to write out the full tree's `EmlTree` representation explicitly to prove the
non-representation: it suffices to show the *function* `myNeg` differs from
`-·` at some point, since any eml-tree whose evaluation equals `myNeg` (which
is the obvious construction) inherits that disagreement.

Witness: at `x = e + 1`, the inner `mySub e x` evaluates to `-1`; the outer
`mySub _ e` then takes `log(-1) = 0` (mathlib's junk-value convention),
yielding `1 - e` instead of the expected `-(e+1)`. -/

/-- `myNeg` does not equal `-·` globally on ℝ; concrete witness `x = e + 1`.

At `x = e + 1`, the obvious construction's inner `mySub e x` correctly computes
`e − (e+1) = −1`, but the outer `mySub _ e` then takes `Real.log (−1) = 0`
(mathlib's junk-value convention extends `log` to be `0` on `(−∞, 0]`), giving
`exp 0 − log(exp e) = 1 − e`. The expected value was `−(e+1) = −e − 1`. The
two are unequal because `1 − e = −e − 1` would force `1 = −1`.

This concretely shows the constraint-narrowing finding from Targets 2–3: even
the simplest function (negation) cannot be globally represented by the *obvious*
eml-tree construction. The stronger claim — that *no* eml-tree of any size
represents negation globally — needs more machinery (analyticity of eml-trees
versus discontinuity of mathlib's extended `Real.log`, or full monodromy). -/
theorem myNeg_not_globally_neg : ∃ x : ℝ, myNeg x ≠ -x := by
  refine ⟨Real.exp 1 + 1, ?_⟩
  have h_e_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  -- Step 1: Compute myNeg explicitly at e + 1.
  have h_value : myNeg (Real.exp 1 + 1) = 1 - Real.exp 1 := by
    unfold myNeg
    -- Inner mySub: 0 < e satisfies the hypothesis.
    rw [mySub_eq _ _ h_e_pos]
    -- Inner result: e - (e+1) = -1.
    have h_inner : Real.exp 1 - (Real.exp 1 + 1) = -1 := by ring
    rw [h_inner]
    -- Outer: mySub (-1) e. Compute through the eml form directly.
    unfold mySub
    rw [myLog_eq, myExp_eq]
    -- Use Real.log (-1) = 0 (mathlib's log_neg_eq_log + log_one).
    have h_log_neg_one : Real.log (-1 : ℝ) = 0 := by
      rw [show (-1 : ℝ) = -(1 : ℝ) by ring, Real.log_neg_eq_log, Real.log_one]
    rw [h_log_neg_one]
    -- Now: eml 0 (exp e) = exp 0 - log(exp e) = 1 - e.
    unfold eml
    rw [Real.exp_zero, Real.log_exp]
  -- Step 2: 1 - e ≠ -(e + 1) because that would force 1 = -1.
  rw [h_value]
  intro heq
  -- heq : 1 - Real.exp 1 = -(Real.exp 1 + 1)
  -- Subtract to get 1 - Real.exp 1 - (-(Real.exp 1 + 1)) = 0, i.e., 2 = 0.
  have : (2 : ℝ) = 0 := by linarith
  norm_num at this

/-! ### The Khovanskii–Stylewarning theorem (statement, sorry-marked)

We state this for ℝ-valued evaluation; the genuine result is over ℂ, and the
quintic-root function should be understood as a specific multivalued algebraic
function defined by `f^5 + a₁f^4 + … + a₅ = 0` on a coefficient space.

A faithful Lean statement requires: (a) a precise definition of "the generic
quintic root function" as a multivalued analytic function, (b) monodromy theory
for compositions of `exp` and `log`. Neither is in mathlib at the depth needed.

The statement below is a placeholder over a reduced setting (real evaluation,
finite-input) that captures the *form* of the obstruction but not the *content*.
Future-work formalization fills in the Khovanskii proof. -/

/-- **Khovanskii–Stylewarning (sketch, to-be-formalized).** No eml-tree
representing a function `(Fin 5 → ℝ) → ℝ` globally agrees with "the generic
quintic root branch" — interpreted as the function sending coefficients
`(a₁, a₂, a₃, a₄, a₅)` to a chosen real root of `f⁵ + a₁f⁴ + a₂f³ + a₃f² + a₄f + a₅`,
where it exists and is real.

The full proof goes through: every eml-tree's evaluation, lifted to ℂ via
analytic continuation, has solvable monodromy group; the generic quintic
root has `S₅` monodromy by classical Galois theory; `S₅` is not solvable
(a 4-line mathlib argument: `S₅` contains `A₅`, `A₅` is simple non-abelian,
hence non-solvable). The conclusion follows by contraposition.

**This statement is `sorry` because the monodromy lift is not in mathlib.**
The bones of the proof — the negative result for the obvious negation
construction (`myNeg_not_globally_neg` above) — is the visible piece of the
broader obstruction. -/
theorem khovanskii_stylewarning_quintic :
    ∀ (T : EmlTree 5),
      ¬ T.representsGlobally
        (fun coeffs : Fin 5 → ℝ =>
          -- placeholder: the function sending (a₁,...,a₅) to a real root of
          -- f⁵ + a₁f⁴ + a₂f³ + a₃f² + a₄f + a₅, when one exists.
          0) := by
  -- Genuine proof requires monodromy theory; left as future-work formalization.
  -- The obstruction sketch is in the framework version (Sheffer/Examples/Eml.lean).
  sorry

end EML
