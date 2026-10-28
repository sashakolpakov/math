import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Matrix Frame Basis -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MatrixFrameBasis.LinearAlgebra

noncomputable section

/-! The columns of a unit matrix give an actual basis over its coefficient ring. -/

variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]

def basisOfUnitMatrix (A : Matrix ι ι R) (h : IsUnit A) : Module.Basis ι R (ι → R) :=
  (Pi.basisFun R ι).map (LinearEquiv.ofBijective A.mulVecLin
    ⟨Matrix.mulVec_injective_of_isUnit h, Matrix.mulVec_surjective_iff_isUnit.mpr h⟩)

theorem basisOfUnitMatrix_apply (A : Matrix ι ι R) (h : IsUnit A) (i j : ι) :
    basisOfUnitMatrix A h j i = A i j := by
  change (A.mulVecLin (Pi.basisFun R ι j)) i = A i j
  simp only [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply]

end

end OAI.AlgebraicGeometry.Comparison.Betti.MatrixFrameBasis.LinearAlgebra
