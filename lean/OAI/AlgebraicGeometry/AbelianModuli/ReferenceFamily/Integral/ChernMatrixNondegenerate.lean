import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernIntegralPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.MarkingRationalBasis
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # Chern Matrix Nondegenerate -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ChernMatrixNondegenerate

noncomputable section

/-! The integral matrix of the original ample Chern form is
nondegenerate, as follows from its original rational period pairing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable {ι : Type} [Fintype ι] [DecidableEq ι] (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
  (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (b : Module.Basis ι ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A))

theorem nativeIntegralChernMatrix_map :
    (Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix A L b).map (Int.castRingHom ℚ) =
      LinearMap.BilinForm.toMatrix (MarkingRationalBasis.integralMarkingRationalBasis A b) (Intrinsic.ChernPairing.nativeChernForm A L) := by
  ext i j
  simp only [Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply]
  exact (Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix_cast A L b i j).trans
    (congrArg₂ (fun x y => Intrinsic.ChernPairing.nativeChernForm A L x y)
      (MarkingRationalBasis.integralMarkingRationalBasis_eq A b i).symm (MarkingRationalBasis.integralMarkingRationalBasis_eq A b j).symm)

theorem nativeIntegralChernMatrix_det_ne_zero (hL : L.IsAmple) :
    (Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix A L b).det ≠ 0 := by
  have hs : (Intrinsic.ChernPairing.nativeChernForm A L).SeparatingLeft :=
    Intrinsic.ChernPeriod.nativeChernForm_separating A L hL
  have hd : (LinearMap.BilinForm.toMatrix (MarkingRationalBasis.integralMarkingRationalBasis A b)
      (Intrinsic.ChernPairing.nativeChernForm A L)).det ≠ 0 :=
    Matrix.separatingLeft_iff_det_ne_zero.mp
      ((LinearMap.BilinForm.separatingLeft_toMatrix_iff (MarkingRationalBasis.integralMarkingRationalBasis A b)).mpr hs)
  intro hz
  apply hd
  rw [← nativeIntegralChernMatrix_map]
  have h := congrArg (Int.castRingHom ℚ) hz
  rw [RingHom.map_det, map_zero] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ChernMatrixNondegenerate
