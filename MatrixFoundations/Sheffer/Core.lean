import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Logic.Function.Basic

/-
# Sheffer / MinimalBasis / Core — substrate-agnostic framework

The framework's core: `OperatorBasis`, `Term`, evaluation, the
`representsGlobally` predicate, `ObstructionTheory`, and the bridge lemma.

No instantiations. Substrate-specific worked examples live under `Examples/`:

- `Sheffer.Examples.Eml` — continuous-math, negative obstruction (Khovanskii axioms)
- `Sheffer.Examples.Nand` — Boolean, positive completeness (Sheffer axiom)
- `Sheffer.Examples.PolyAct` — polynomial-activation networks, negative
  obstruction (constructive, no axioms)

Lean namespace stays `MinimalBasis` for backward compatibility with prior commits;
the file/repo name "Sheffer" is for the publishing-side identity. -/

namespace MinimalBasis

/-! ## Operator basis

An `OperatorBasis α` is a finite (or arbitrarily-typed) family of operators
that compose finitarily over values of type `α`. -/

/-- An operator basis over the carrier type `α`.

`Op` is the (typically small) type of operator-symbols; `arity` gives each
operator's number of inputs; `eval` is the semantic interpretation. -/
structure OperatorBasis (α : Type*) where
  Op : Type
  arity : Op → ℕ
  eval : (op : Op) → (Fin (arity op) → α) → α

/-! ## Terms over an operator basis -/

/-- A term over an operator basis `B` with `n` input variables. Leaves are
either constants from `α` or input variables (`Fin n`); internal nodes apply
an operator from `B.Op` to its arity-many subterms. -/
inductive Term {α : Type*} (B : OperatorBasis α) (n : ℕ) : Type _ where
  | const : α → Term B n
  | var   : Fin n → Term B n
  | app   : (op : B.Op) → (Fin (B.arity op) → Term B n) → Term B n

/-- Evaluate a term at an environment. -/
def Term.eval {α : Type*} {B : OperatorBasis α} {n : ℕ} :
    Term B n → (Fin n → α) → α
  | .const c,        _   => c
  | .var i,          env => env i
  | .app op kids,    env => B.eval op (fun i => (kids i).eval env)

/-- `T` globally represents `f` iff `T`'s evaluation matches `f` at every input. -/
def Term.representsGlobally {α : Type*} {B : OperatorBasis α} {n : ℕ}
    (T : Term B n) (f : (Fin n → α) → α) : Prop :=
  ∀ env, T.eval env = f env

/-- Structural depth of a term: 0 for leaves, `1 + max child depths` for
internal nodes. Generic over basis (uses `Finset.univ.sup` for the max
over arity-many children, with `0` as the natural bottom for the empty
case). -/
def Term.depth {α : Type*} {B : OperatorBasis α} {n : ℕ} :
    Term B n → ℕ
  | .const _    => 0
  | .var _      => 0
  | .app op kids =>
    1 + (Finset.univ : Finset (Fin (B.arity op))).sup (fun i => (kids i).depth)

/-- Equation lemma for `Term.depth` on `.app`. -/
theorem Term.depth_app {α : Type*} {B : OperatorBasis α} {n : ℕ}
    (op : B.Op) (kids : Fin (B.arity op) → Term B n) :
    (Term.app op kids).depth =
      1 + (Finset.univ : Finset (Fin (B.arity op))).sup
        (fun i => (kids i).depth) := rfl

/-! ## Sanity examples -/

section Sanity

variable {α : Type*} (B : OperatorBasis α) (n : ℕ)

/-- Trivial: a `var` term represents the projection function. -/
example (i : Fin n) :
    Term.representsGlobally (B := B) (Term.var i) (fun env => env i) := by
  intro env; rfl

/-- Trivial: a `const` term represents a constant function. -/
example (c : α) :
    Term.representsGlobally (B := B) (n := n) (Term.const c) (fun _ => c) := by
  intro env; rfl

end Sanity

/-! ## ObstructionTheory — separate from `OperatorBasis` -/

/-- An obstruction theory over an operator basis `B` specifies a class of
functions closed under the basis's operators. The structural induction
`Term.eval_in_class` is then automatic.

For Path B, instantiations leave the deep semantic content of `inClass` as
opaque axioms. -/
structure ObstructionTheory {α : Type*} (B : OperatorBasis α) where
  /-- A class of functions of arity `n`, parameterized by arity. -/
  inClass : (n : ℕ) → ((Fin n → α) → α) → Prop
  /-- Constants are in the class. -/
  const_in_class : ∀ {n : ℕ} (c : α), inClass n (fun _ => c)
  /-- Variables (projections) are in the class. -/
  var_in_class : ∀ {n : ℕ} (i : Fin n), inClass n (fun env => env i)
  /-- Each operator preserves the class. -/
  app_in_class : ∀ {n : ℕ} (op : B.Op)
    (subs : Fin (B.arity op) → ((Fin n → α) → α)),
    (∀ k, inClass n (subs k)) →
    inClass n (fun env => B.eval op (fun k => subs k env))

/-! ## Structural induction — terms evaluate inside the class -/

/-- Every term over an operator basis evaluates to a function in any
obstruction class for that basis. -/
theorem Term.eval_in_class {α : Type*} {B : OperatorBasis α}
    (Th : ObstructionTheory B) {n : ℕ} :
    ∀ (T : Term B n), Th.inClass n T.eval
  | .const c     => Th.const_in_class c
  | .var i       => Th.var_in_class i
  | .app op kids => by
      have ih : ∀ k, Th.inClass n (kids k).eval :=
        fun k => Term.eval_in_class Th (kids k)
      exact Th.app_in_class op (fun k => (kids k).eval) ih

/-! ## The bridge lemma -/

/-- **Bridge lemma.** If `f` is outside `Th`'s obstruction class, no term
over `B` globally represents `f`. -/
theorem Term.not_representsGlobally_of_not_in_class
    {α : Type*} {B : OperatorBasis α} (Th : ObstructionTheory B) {n : ℕ}
    (T : Term B n) (f : (Fin n → α) → α)
    (hf : ¬ Th.inClass n f) (rep : T.representsGlobally f) :
    False :=
  hf (funext rep ▸ Term.eval_in_class Th T)

/-- **Contrapositive form.** No term in `B` represents `f` globally if
`f ∉ Th.inClass`. -/
theorem Term.no_representation_of_not_in_class
    {α : Type*} {B : OperatorBasis α} (Th : ObstructionTheory B) {n : ℕ}
    (f : (Fin n → α) → α) (hf : ¬ Th.inClass n f) :
    ¬ ∃ T : Term B n, T.representsGlobally f := by
  rintro ⟨T, hT⟩
  exact T.not_representsGlobally_of_not_in_class Th f hf hT

end MinimalBasis
