import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumCoordinates

/-! # Intrinsic Dual Momentum -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicDualMomentum.Intrinsic

noncomputable section

/-! Exact duality and inverse identities for real native momentum
coordinates, obtained from the given position equivalence. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalPositionBlocks.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumCoordinates.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem real_momentum_right_inverse (p : Adelic.BallGeometryData.FrameIndex A → ℝ) :
    IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (IntrinsicMomentumCoordinates.Intrinsic.realMomentumComponent B p) = p := by
  have he := IntrinsicMomentumCoordinates.Intrinsic.global_momentum_components B (fun i => (p i : ℂ))
  simp only [IntrinsicMomentumCoordinates.Intrinsic.real_momentum_component_cast,IntrinsicLocalJacobiPhase.Intrinsic.global_momentum_real] at he
  funext i
  exact Complex.ofReal_injective (congrFun he i)

theorem real_momentum_left_inverse (p : Adelic.BallGeometryData.RealPositions A) :
    IntrinsicMomentumCoordinates.Intrinsic.realMomentumComponent B (IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B p) = p := by
  funext v i
  have he := IntrinsicLocalPositionBlocks.Intrinsic.local_momentum_component B v (fun w j => (p w j : ℂ))
  rw [IntrinsicLocalJacobiPhase.Intrinsic.global_momentum_real,IntrinsicMomentumCoordinates.Intrinsic.real_momentum_component_cast] at he
  exact Complex.ofReal_injective (congrFun he i)

theorem real_momentum_duality (q p : Adelic.BallGeometryData.RealPositions A) :
    B.realPosition q ⬝ᵥ IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B p = ∑ v : Fin A.places, q v ⬝ᵥ p v := by
  unfold IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum
  rw [dotProduct_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Matrix.dotProduct_transpose_mulVec,IntrinsicLocalGaussianCoordinates.Intrinsic.local_position_row_apply,B.realPosition.symm_apply_apply,
    dotProduct_comm]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicDualMomentum.Intrinsic
