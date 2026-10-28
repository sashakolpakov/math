import OAI.RepresentationTheory.Theta.Adelic.BallNatural
import OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup
import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

/-! # Ball Group Comparison -/

namespace OAI.RepresentationTheory.Theta.Adelic.BallGroupComparison

noncomputable section

/-! The actual ball group is the same standard matrix group as the
one used by the proved ArithmeticQuotient ball geometry, with its usual topology. -/

open scoped Classical

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup

def diagonalForm (b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient b)

theorem diagonal_unitary_iff (b : ℂ) (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    g ∈ Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitarySubgroup (starRingEnd ℂ) b ↔
      g.val.conjTranspose * diagonalForm b * g.val = diagonalForm b := by
  rw [Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitary_iff_columns]
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [diagonalForm, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply, mul_comm, mul_left_comm, mul_assoc, eq_comm] using h i i
    · simpa [diagonalForm, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply, hij, mul_comm, mul_left_comm, mul_assoc, eq_comm] using h j i
  · intro h i j
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M j i) h
    by_cases hij : i = j
    · subst j
      simpa [diagonalForm, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply, mul_comm, mul_left_comm, mul_assoc, eq_comm] using he
    · simpa [diagonalForm, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply, hij, mul_comm, mul_left_comm, mul_assoc, eq_comm] using he

def diagonalUnitaryEquiv (b : ℂ) :
    SpecialUnitary.SU (diagonalForm b) ≃* Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b where
  toFun g := ⟨PrincipalSubgroup.suSpecialLinear (diagonalForm b) g, (diagonal_unitary_iff b _).mpr g.property.1⟩
  invFun g := ⟨Matrix.SpecialLinearGroup.toGL g.val, (diagonal_unitary_iff b g.val).mp g.property,
    Matrix.SpecialLinearGroup.coeToGL_det g.val⟩
  left_inv g := by apply Subtype.ext; apply Units.ext; rfl
  right_inv g := by apply Subtype.ext; rfl
  map_mul' _ _ := rfl

def diagonalUnitaryContinuousEquiv (b : ℂ) :
    SpecialUnitary.SU (diagonalForm b) ≃ₜ* Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b where
  toMulEquiv := diagonalUnitaryEquiv b
  continuous_toFun := ((Units.continuous_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    (Matrix.SpecialLinearGroup.continuous_toGL.comp continuous_subtype_val).subtype_mk _

theorem diagonalForm_neg_one : diagonalForm (-1) = BallNatural.standardForm.val := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [diagonalForm, BallNatural.standardForm, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient, Fin.ext_iff]

def specialUnitaryFormCongr {R I : Type*} [CommRing R] [StarRing R]
    [TopologicalSpace R] [Fintype I] [DecidableEq I]
    (H K : Matrix I I R) (h : H = K) : SpecialUnitary.SU H ≃ₜ* SpecialUnitary.SU K where
  toFun g := ⟨g.val, h ▸ g.property⟩
  invFun g := ⟨g.val, h.symm ▸ g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def ballGroupComparison : BallNatural.BallGroup ≃ₜ* Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (-1) :=
  (specialUnitaryFormCongr BallNatural.standardForm.val (diagonalForm (-1))
    diagonalForm_neg_one.symm).trans (diagonalUnitaryContinuousEquiv (-1))

theorem ballGroupComparison_matrix (g : BallNatural.BallGroup) : (ballGroupComparison g).val.val = g.val.val := by
  rfl

end

end OAI.RepresentationTheory.Theta.Adelic.BallGroupComparison
