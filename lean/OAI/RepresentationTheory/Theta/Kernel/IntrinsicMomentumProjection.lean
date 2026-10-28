import OAI.RepresentationTheory.Theta.Kernel.IntrinsicDualMomentum
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionProjection

/-! # Intrinsic Momentum Projection -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumProjection.Intrinsic

noncomputable section

/-! Projection to a native real place transports under the momentum
equivalence by the transpose of the actual position projection. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicDualMomentum.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionProjection.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem momentum_place_projection (v : Fin A.places) (p : Adelic.BallGeometryData.RealPositions A) :
    (LinearMap.toMatrix' (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v))ᵀ.mulVec (IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B p) =
      IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (Pi.single v (p v)) := by
  have he (q : Adelic.BallGeometryData.RealPositions A) :
      B.realPosition q ⬝ᵥ (LinearMap.toMatrix' (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v))ᵀ.mulVec (IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B p) =
        B.realPosition q ⬝ᵥ IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (Pi.single v (p v)) := by
    have hS : (LinearMap.toMatrix' (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v)).mulVec (B.realPosition q) =
        B.realPosition (Pi.single v (q v)) := by
      rw [LinearMap.toMatrix'_mulVec]
      change B.realPosition (Pi.single v (B.realPosition.symm (B.realPosition q) v)) = _
      rw [B.realPosition.symm_apply_apply]
    rw [Matrix.dotProduct_transpose_mulVec,hS,dotProduct_comm (IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B p),
      IntrinsicDualMomentum.Intrinsic.real_momentum_duality,IntrinsicDualMomentum.Intrinsic.real_momentum_duality]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w = v
    · subst w
      rw [Pi.single_eq_same,Pi.single_eq_same]
    · simp [hw]
  funext i
  have hi := he (B.realPosition.symm (Pi.single i 1))
  rw [B.realPosition.apply_symm_apply,single_dotProduct,single_dotProduct,one_mul,one_mul] at hi
  exact hi

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumProjection.Intrinsic
