import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Complex.Basic

/-! # Standard Smooth Jacobian -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.StandardSmoothJacobian.Algebraic

noncomputable section

/-!
# Jacobians of standard smooth presentations at field-valued points

This file uses mathlib's actual algebra presentations and algebra homomorphisms.
It proves that a submersive presentation has an invertible selected Jacobian
minor at every field-valued point, hence full row rank. It makes no claim about
analytic coordinate charts or an implicit function theorem.
-/

open _root_.MvPolynomial

universe u v w t

variable {K : Type u} {S : Type v} {ι : Type w} {σ : Type t}
variable [Field K] [CommRing S] [Algebra K S]

/-- The usual relation-by-variable Jacobian of a presentation, evaluated at an
actual field-valued point of its algebra. -/
def pointJacobian (P : Algebra.Presentation K S ι σ) (x : S →ₐ[K] K) :
    Matrix σ ι K :=
  fun j i => aeval (fun k => x (P.val k)) (pderiv i (P.relation j))

/-- Every defining relation vanishes at the coordinates of an algebra point. -/
theorem point_relation_zero (P : Algebra.Presentation K S ι σ) (x : S →ₐ[K] K)
    (j : σ) : aeval (fun i => x (P.val i)) (P.relation j) = 0 := by
  rw [← MvPolynomial.comp_aeval_apply]
  simp

/-- The square minor selected by a pre-submersive presentation. -/
def pointJacobianMinor (P : Algebra.PreSubmersivePresentation K S ι σ)
    (x : S →ₐ[K] K) : Matrix σ σ K :=
  (pointJacobian P.toPresentation x).submatrix id P.map

variable [Fintype σ] [DecidableEq σ]

/-- Mathlib uses the variable-by-relation convention for its selected matrix;
the usual Jacobian convention is its transpose. -/
theorem pointJacobianMinor_eq_map_transpose
    (P : Algebra.PreSubmersivePresentation K S ι σ) (x : S →ₐ[K] K) :
    pointJacobianMinor P x =
      ((aeval (fun k => x (P.val k))).mapMatrix P.jacobiMatrix).transpose := by
  ext i j
  simp [pointJacobianMinor, pointJacobian, P.jacobiMatrix_apply]

/-- Evaluation of the algebraic Jacobian agrees with the determinant of the
selected ordinary Jacobian minor at the point. -/
theorem pointJacobianMinor_det
    (P : Algebra.PreSubmersivePresentation K S ι σ) (x : S →ₐ[K] K) :
    (pointJacobianMinor P x).det = x P.jacobian := by
  rw [pointJacobianMinor_eq_map_transpose, Matrix.det_transpose, ← AlgHom.map_det]
  rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply]
  exact (MvPolynomial.comp_aeval_apply P.val x P.jacobiMatrix.det).symm

/-- A submersive presentation has a nonzero selected Jacobian determinant at
every field-valued point. -/
theorem pointJacobianMinor_det_ne_zero
    (P : Algebra.SubmersivePresentation K S ι σ) (x : S →ₐ[K] K) :
    (pointJacobianMinor P.toPreSubmersivePresentation x).det ≠ 0 := by
  rw [pointJacobianMinor_det]
  exact (P.jacobian_isUnit.map x).ne_zero

/-- The selected square minor has full rank. -/
theorem pointJacobianMinor_rank
    (P : Algebra.SubmersivePresentation K S ι σ) (x : S →ₐ[K] K) :
    (pointJacobianMinor P.toPreSubmersivePresentation x).rank = Fintype.card σ :=
  Matrix.rank_of_det_ne_zero (pointJacobianMinor_det_ne_zero P x)

/-- The full Jacobian of all relations has full row rank, not merely the square
minor singled out in the definition of a submersive presentation. -/
theorem pointJacobian_rank [Fintype ι]
    (P : Algebra.SubmersivePresentation K S ι σ) (x : S →ₐ[K] K) :
    (pointJacobian P.toPresentation x).rank = Fintype.card σ := by
  apply le_antisymm (Matrix.rank_le_card_height _)
  calc
    Fintype.card σ =
        (pointJacobianMinor P.toPreSubmersivePresentation x).rank :=
      (pointJacobianMinor_rank P x).symm
    _ ≤ (pointJacobian P.toPresentation x).rank :=
      Matrix.rank_submatrix_le _ id P.map

/-- Standard smoothness supplies a finite polynomial presentation with full
Jacobian row rank at a given field-valued point. -/
theorem exists_pointJacobian_full_row_rank [Algebra.IsStandardSmooth K S]
    (x : S →ₐ[K] K) :
    ∃ (n m : ℕ) (P : Algebra.SubmersivePresentation K S (Fin n) (Fin m)),
      (pointJacobian P.toPresentation x).rank = m := by
  classical
  obtain ⟨ι', σ', hσ, hι, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := K) (S := S)
  let : Finite σ' := hσ
  let : Finite ι' := hι
  let : Fintype ι' := Fintype.ofFinite ι'
  let : Fintype σ' := Fintype.ofFinite σ'
  let Q := P.reindex (Fintype.equivFin ι').symm (Fintype.equivFin σ').symm
  refine ⟨Fintype.card ι', Fintype.card σ', Q, ?_⟩
  simpa using pointJacobian_rank Q x

end

end OAI.AlgebraicGeometry.Foundations.Scheme.StandardSmoothJacobian.Algebraic
