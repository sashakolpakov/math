import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace

/-! # Unitary Matrix Lemmas -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UnitaryMatrixLemmas.CM

noncomputable section

/-! Small matrix lemmas used without unfolding concrete CM coefficient fields. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

theorem determinant_unit (A : (Matrix I I R)ˣ) (h : A.val.det = 1) :
    Matrix.GeneralLinearGroup.det A = 1 := by
  apply Units.ext
  exact h

theorem formValue_basis [StarRing R] (A : Matrix I I R) (i j : I) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UnitaryMatrixLemmas.CM
