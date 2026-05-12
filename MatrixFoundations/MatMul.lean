/-
# §6.3 — Matrix multiplication = composition of linear maps

Formalization of `notes.md §6.3`. Given finite-dimensional vector spaces `V`, `W`, `U`
over a field `F` with bases `b_V`, `b_W`, `b_U`, and linear maps `T : V → W`, `S : W → U`,
the matrix of `S ∘ T` (relative to `b_V → b_U`) equals the product of the matrix of `S`
(`b_W → b_U`) times the matrix of `T` (`b_V → b_W`), entrywise:

    (A * B) i j = ∑ k, A i k * B k j

## Convention map (notes.md ↔ mathlib)

Our notation `[T]_{C ← B}` means: matrix whose `j`-th column is the coordinates of
`T(b_j)` in basis `C` (column-as-image; see `notes.md §5` and `glossary.md`). Mathlib's
`LinearMap.toMatrix b_dom b_cod T` is the same matrix:

    (LinearMap.toMatrix b_dom b_cod T) i j = (b_cod.repr (T (b_dom j))) i

So `[T]_{C ← B}  =  LinearMap.toMatrix B C T`. Argument order: domain first, codomain
second — matching the right-to-left arrow `C ← B` reads `B → C`.

The defining property `(S ∘ T)(v) = S(T(v))` is mathlib's `LinearMap.comp_apply`.
Together these give `LinearMap.toMatrix b_V b_U (S ∘ T) = M_S * M_T` (row-times-column),
which mathlib has as `LinearMap.toMatrix_comp` (`Mathlib.LinearAlgebra.Matrix.ToLin`).

Change either convention (column-as-image, or the recipient-on-left composition rule
`(S ∘ T)(v) = S(T(v))`) and the formula transposes correspondingly — but you cannot
avoid having *some* such formula. See `notes.md §6.3` final paragraph.

## Generality vs the prose

The prose in §6.3 says "field `F`". Mathlib's `LinearMap.toMatrix_comp` is stated more
generally over any commutative semiring. We restate over `Field F` here to keep the
correspondence with `notes.md` immediate; the proof itself is just an instance of
mathlib's lemma.
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

-- The §10 worked example uses `native_decide` for 2×2 rational matrix arithmetic;
-- kernel `decide` stalls on the rational reduction. native_decide trusts the Lean
-- compiler in addition to the kernel — fine for our project, but mathlib's style
-- linter forbids it inside mathlib itself.
set_option linter.style.nativeDecide false

open LinearMap Matrix Module

namespace MatrixFoundations.MatMul

/-! ## §6.3 — the theorem -/

variable {F : Type*} [Field F]
variable {ιV ιW ιU : Type*}
variable [Fintype ιV] [Fintype ιW] [Finite ιU]
variable [DecidableEq ιV] [DecidableEq ιW]
variable {V W U : Type*}
variable [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
variable [Module F V] [Module F W] [Module F U]

/-- §6.3. The matrix of the composition `S ∘ T` is the product of the matrices of
`S` and `T`. This is the row-times-column rule, derived (not stipulated) from
the column-as-image convention plus `(S ∘ T)(v) = S(T(v))`. -/
theorem toMatrix_comp_eq
    (b_V : Basis ιV F V) (b_W : Basis ιW F W) (b_U : Basis ιU F U)
    (T : V →ₗ[F] W) (S : W →ₗ[F] U) :
    LinearMap.toMatrix b_V b_U (S.comp T) =
      LinearMap.toMatrix b_W b_U S * LinearMap.toMatrix b_V b_W T :=
  LinearMap.toMatrix_comp b_V b_W b_U S T

/-- §6.3 expanded — the row-times-column entry formula. The `(i, j)` entry of the
matrix of `S ∘ T` equals `∑_k Aᵢₖ · Bₖⱼ`, exactly the formula derived in `notes.md`
by expanding `(S ∘ T)(b_j)` in the basis `b_U`. -/
theorem toMatrix_comp_apply_eq
    (b_V : Basis ιV F V) (b_W : Basis ιW F W) (b_U : Basis ιU F U)
    (T : V →ₗ[F] W) (S : W →ₗ[F] U) (i : ιU) (j : ιV) :
    LinearMap.toMatrix b_V b_U (S.comp T) i j =
      ∑ k : ιW, LinearMap.toMatrix b_W b_U S i k * LinearMap.toMatrix b_V b_W T k j := by
  rw [LinearMap.toMatrix_comp b_V b_W b_U S T]
  rfl

end MatrixFoundations.MatMul

/-! ## §6.4 — concrete 2×2 counterexample showing `A * B ≠ B * A`

The two specific 2×2 integer matrices from `notes.md §6.4`:

    A = | 0  1 |     B = | 1  0 |
        | 0  0 |         | 0  0 |

The entries below are over `ℤ` (the prose uses `ℝ`, but the same matrices over `ℤ`
witness the same non-commutativity, and `decide` works on `ℤ` matrices). -/

namespace MatrixFoundations.MatMul.NonComm

/-- The matrix `A` from §6.4. -/
def A : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- The matrix `B` from §6.4. -/
def B : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

/-- §6.4 — `A * B` is the zero matrix. -/
example : A * B = !![0, 0; 0, 0] := by
  unfold A B
  decide

/-- §6.4 — `B * A` is `A` itself (specifically). -/
example : B * A = !![0, 1; 0, 0] := by
  unfold A B
  decide

/-- §6.4 — therefore `A * B ≠ B * A`. -/
example : A * B ≠ B * A := by
  unfold A B
  decide

end MatrixFoundations.MatMul.NonComm

/-! ## §7 — Algebraic laws as corollaries of §6.3

`notes.md §7` claims the four algebraic laws of matrices are *one-line corollaries* of §6.3.
This section makes that visibly true: each law is derived through the corresponding linear-map
equation (`LinearMap.comp_assoc`, `LinearMap.comp_add`, `LinearMap.add_comp`) plus
`toMatrix_comp_eq` from §6.3 plus additivity of `LinearMap.toMatrix` (it's a `LinearEquiv`).

There is a shorter alternative for each: mathlib's `Matrix.mul_assoc`, `Matrix.mul_add`,
`Matrix.add_mul` prove the matrix versions directly from the definition of matrix
multiplication, with no detour through linear maps. The proofs below take the longer route on
purpose, so the same pedagogical chain remains visible in the formalization. -/

namespace MatrixFoundations.MatMul

variable {F : Type*} [Field F]
variable {ιV ιW ιX ιU : Type*}
variable [Fintype ιV] [Fintype ιW] [Fintype ιX] [Finite ιU]
variable [DecidableEq ιV] [DecidableEq ιW] [DecidableEq ιX]
variable {V W X U : Type*}
variable [AddCommGroup V] [AddCommGroup W] [AddCommGroup X] [AddCommGroup U]
variable [Module F V] [Module F W] [Module F X] [Module F U]

/-- §7 — identity. The identity matrix is the matrix of `LinearMap.id`. This is
`LinearMap.toMatrix_id` from mathlib; there is essentially no derivation, since
"identity matrix" was *defined* as the matrix of the identity map (column j is the
coordinates of `id(b_j) = b_j`, i.e. the j-th standard basis vector — Kronecker delta). -/
theorem toMatrix_id_eq (b : Basis ιV F V) :
    LinearMap.toMatrix b b LinearMap.id = (1 : Matrix ιV ιV F) :=
  LinearMap.toMatrix_id b

/-- §7 — associativity (prose-faithful version). The matrix equation
`(A * B) * C = A * (B * C)` for matrices arising from linear maps `R, T, S` follows from
`(S ∘ T) ∘ R = S ∘ (T ∘ R)` (`LinearMap.comp_assoc`) by four applications of §6.3.

Direct mathlib alternative: `Matrix.mul_assoc`. -/
theorem toMatrix_comp_assoc
    (b_V : Basis ιV F V) (b_W : Basis ιW F W) (b_X : Basis ιX F X) (b_U : Basis ιU F U)
    (R : V →ₗ[F] W) (T : W →ₗ[F] X) (S : X →ₗ[F] U) :
    (LinearMap.toMatrix b_X b_U S * LinearMap.toMatrix b_W b_X T) *
        LinearMap.toMatrix b_V b_W R =
      LinearMap.toMatrix b_X b_U S *
        (LinearMap.toMatrix b_W b_X T * LinearMap.toMatrix b_V b_W R) := by
  rw [← toMatrix_comp_eq b_W b_X b_U T S,
      ← toMatrix_comp_eq b_V b_W b_U R (S ∘ₗ T),
      ← toMatrix_comp_eq b_V b_W b_X R T,
      ← toMatrix_comp_eq b_V b_X b_U (T ∘ₗ R) S,
      LinearMap.comp_assoc]

/-- §7 — right-distributivity (prose-faithful version). `S ∘ (T₁ + T₂) = S ∘ T₁ + S ∘ T₂`
(`LinearMap.comp_add`) plus additivity of `toMatrix` plus §6.3 give
`A * (B₁ + B₂) = A * B₁ + A * B₂`.

Direct mathlib alternative: `Matrix.mul_add`. -/
theorem toMatrix_comp_add_right
    (b_V : Basis ιV F V) (b_W : Basis ιW F W) (b_U : Basis ιU F U)
    (T₁ T₂ : V →ₗ[F] W) (S : W →ₗ[F] U) :
    LinearMap.toMatrix b_W b_U S *
        (LinearMap.toMatrix b_V b_W T₁ + LinearMap.toMatrix b_V b_W T₂) =
      LinearMap.toMatrix b_W b_U S * LinearMap.toMatrix b_V b_W T₁ +
        LinearMap.toMatrix b_W b_U S * LinearMap.toMatrix b_V b_W T₂ := by
  rw [← map_add (LinearMap.toMatrix b_V b_W) T₁ T₂,
      ← toMatrix_comp_eq b_V b_W b_U (T₁ + T₂) S,
      LinearMap.comp_add,
      map_add,
      toMatrix_comp_eq b_V b_W b_U T₁ S,
      toMatrix_comp_eq b_V b_W b_U T₂ S]

/-- §7 — left-distributivity (prose-faithful version). `(S₁ + S₂) ∘ T = S₁ ∘ T + S₂ ∘ T`
(`LinearMap.add_comp`) plus additivity of `toMatrix` plus §6.3 give
`(A₁ + A₂) * B = A₁ * B + A₂ * B`.

Direct mathlib alternative: `Matrix.add_mul`. -/
theorem toMatrix_comp_add_left
    (b_V : Basis ιV F V) (b_W : Basis ιW F W) (b_U : Basis ιU F U)
    (T : V →ₗ[F] W) (S₁ S₂ : W →ₗ[F] U) :
    (LinearMap.toMatrix b_W b_U S₁ + LinearMap.toMatrix b_W b_U S₂) *
        LinearMap.toMatrix b_V b_W T =
      LinearMap.toMatrix b_W b_U S₁ * LinearMap.toMatrix b_V b_W T +
        LinearMap.toMatrix b_W b_U S₂ * LinearMap.toMatrix b_V b_W T := by
  rw [← map_add (LinearMap.toMatrix b_W b_U) S₁ S₂,
      ← toMatrix_comp_eq b_V b_W b_U T (S₁ + S₂),
      LinearMap.add_comp,
      map_add,
      toMatrix_comp_eq b_V b_W b_U T S₁,
      toMatrix_comp_eq b_V b_W b_U T S₂]

end MatrixFoundations.MatMul

/-! ## §10 — Change of basis

`notes.md §10` claims the change-of-basis formula `[T]_{B'} = P⁻¹ · [T]_B · P` is
*literally §6.3 used three times*: the identity `T = id ∘ T ∘ id` becomes a triple matrix
product when each `∘` is unfolded via §6.3.

The proof below makes this visible: two applications of `toMatrix_comp_eq` (reversed) plus
`LinearMap.id_comp` and `LinearMap.comp_id` to clean up. The auxiliary lemma
`toMatrix_id_mul_id` shows that `[id]_{B' ← B}` and `[id]_{B ← B'}` are mutual inverses,
justifying the `P⁻¹` notation in the prose.

Mathlib direct alternative: `Matrix.similar` machinery + `LinearMap.toMatrix_basis_change`
(or the current name). The proofs below intentionally take the §6.3 route. -/

namespace MatrixFoundations.MatMul

section ChangeOfBasis

variable {F : Type*} [Field F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The two change-of-basis matrices `[id]_{B ← B'}` and `[id]_{B' ← B}` are mutual
inverses: their product is the identity matrix. Proof: §6.3 applied to `id ∘ id = id`,
then `LinearMap.toMatrix_id`. This is why `notes.md §10` writes `P⁻¹` for the second one. -/
theorem toMatrix_id_mul_id (B B' : Basis ι F V) :
    LinearMap.toMatrix B B' LinearMap.id * LinearMap.toMatrix B' B LinearMap.id =
      (1 : Matrix ι ι F) := by
  rw [← toMatrix_comp_eq B' B B' LinearMap.id LinearMap.id,
      LinearMap.id_comp,
      LinearMap.toMatrix_id]

/-- §10 — change of basis. For `T : V →ₗ V` and bases `B, B'` of `V`,

  `[T]_{B'} = [id]_{B' ← B} · [T]_B · [id]_{B ← B'}`.

The proof unwinds the matrix product on the RHS via two applications of §6.3 (reversed) plus
`id ∘ T = T = T ∘ id`. So §10 is literally §6.3 applied twice on the identity
`T = id ∘ T ∘ id`, exactly as the prose claims. -/
theorem toMatrix_change_of_basis (B B' : Basis ι F V) (T : V →ₗ[F] V) :
    LinearMap.toMatrix B' B' T =
      LinearMap.toMatrix B B' LinearMap.id *
      LinearMap.toMatrix B B T *
      LinearMap.toMatrix B' B LinearMap.id := by
  rw [← toMatrix_comp_eq B B B' T LinearMap.id,
      LinearMap.id_comp,
      ← toMatrix_comp_eq B' B B' LinearMap.id T,
      LinearMap.comp_id]

end ChangeOfBasis

/-! ### §10 punchline — similarity invariants

`notes.md §10` lists the consequences of the change-of-basis formula: properties of a
matrix that survive `A ↦ P⁻¹ A P` (similarity) are properties of the underlying *linear
map*, not coordinate artifacts. Determinant and trace are the headline invariants;
characteristic polynomial (and hence eigenvalues) is the §11 follow-up.

These are one-line restatements of mathlib's `Matrix.det_units_conj'` /
`Matrix.trace_units_conj'`, packaged with our `_similar` naming so a future reader of
`notes.md §10` can find them. The `Units` packaging is mathlib's way of encoding "P is
invertible"; for change-of-basis matrices coming from `[id]_{B'←B}`, the unit witness
is constructed from `toMatrix_id_mul_id` plus the symmetric inverse property. -/

section Similarity

variable {F : Type*} [Field F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- §10 — determinant is a similarity invariant. -/
theorem det_similar (P : (Matrix ι ι F)ˣ) (A : Matrix ι ι F) :
    Matrix.det (P⁻¹.val * A * P.val) = Matrix.det A :=
  Matrix.det_units_conj' P A

/-- §10 — trace is a similarity invariant. -/
theorem trace_similar (P : (Matrix ι ι F)ˣ) (A : Matrix ι ι F) :
    Matrix.trace (P⁻¹.val * A * P.val) = Matrix.trace A :=
  Matrix.trace_units_conj' P A

end Similarity

end MatrixFoundations.MatMul

/-! ### §10 worked example — diagonalization in the eigenbasis

From `notes.md §10`: the map `T(x,y) = (2x+y, x+2y)` has matrix `!![2,1; 1,2]` in the
standard basis. In the eigenbasis `B' = {(1,1), (1,-1)}`, with change-of-basis matrix
`P = !![1,1; 1,-1]` (and `P⁻¹ = (1/2)·!![1,1; 1,-1]`), the same map becomes diagonal
`!![3,0; 0,1]`. Verified entry-wise over ℚ (rationals are `decide`-friendly; ℝ isn't).

This is `change-of-basis` (the prose §10 theorem) made concrete. -/

namespace MatrixFoundations.MatMul.WorkedExample

/-- The standard-basis matrix of `T(x,y) = (2x+y, x+2y)`. -/
def A_std : Matrix (Fin 2) (Fin 2) ℚ := !![2, 1; 1, 2]

/-- The change-of-basis matrix `P = [id]_{std ← eigenbasis}`. -/
def P : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 1, -1]

/-- The inverse change-of-basis matrix `P⁻¹ = (1/2) · !![1,1; 1,-1]`. -/
def Pinv : Matrix (Fin 2) (Fin 2) ℚ := !![1/2, 1/2; 1/2, -1/2]

/-- `P⁻¹ * P = 1` — sanity-check that `Pinv` really is the inverse of `P`.
Uses `native_decide` because kernel reduction stalls on rational arithmetic;
native compilation evaluates cleanly. -/
example : Pinv * P = (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  unfold Pinv P
  native_decide

/-- §10 worked example — `[T]_{B'} = P⁻¹ · [T]_B · P` reduces to the diagonal `!![3,0; 0,1]`. -/
example : Pinv * A_std * P = !![3, 0; 0, 1] := by
  unfold Pinv A_std P
  native_decide

end MatrixFoundations.MatMul.WorkedExample

