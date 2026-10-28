import OAI.RepresentationTheory.Theta.Kernel.IntrinsicDualMomentum

/-! # Intrinsic Momentum Equiv -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumEquiv.Intrinsic

noncomputable section

/-! The dual momentum coordinates form an actual continuous linear
equivalence, with the proved local transpose formula as inverse. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumCoordinates.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicDualMomentum.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)

def momentumLinearEquiv : Adelic.BallGeometryData.RealPositions A ≃ₗ[ℝ] (Adelic.BallGeometryData.FrameIndex A → ℝ) where
  toFun := IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B
  invFun := IntrinsicMomentumCoordinates.Intrinsic.realMomentumComponent B
  left_inv := IntrinsicDualMomentum.Intrinsic.real_momentum_left_inverse B
  right_inv := IntrinsicDualMomentum.Intrinsic.real_momentum_right_inverse B
  map_add' p q := by
    simp only [IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum,Pi.add_apply,Matrix.mulVec_add,Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum,Pi.smul_apply,Matrix.mulVec_smul]
    exact Finset.smul_sum.symm

def momentumContinuousEquiv : Adelic.BallGeometryData.RealPositions A ≃L[ℝ] (Adelic.BallGeometryData.FrameIndex A → ℝ) :=
  (momentumLinearEquiv B).toContinuousLinearEquiv

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumEquiv.Intrinsic
