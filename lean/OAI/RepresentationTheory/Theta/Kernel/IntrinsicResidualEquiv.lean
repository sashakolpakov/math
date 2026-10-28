import OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualPhase
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentPairing
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumEquiv

/-! # Intrinsic Residual Equiv -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualEquiv.Intrinsic

noncomputable section

/-! The residual native coordinate change is an actual continuous
linear symplectic equivalence preserving all local positions. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentAction.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentPairing.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualPhase.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumEquiv.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)

def cotangentLinearEquiv : (Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) ≃ₗ[ℝ]
    ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℝ) where
  toFun := IntrinsicCotangentAction.Intrinsic.cotangentCoordinates B
  invFun w v := Sum.elim (B.realPosition.symm (fun i => w (.inl i)) v)
    ((IntrinsicMomentumEquiv.Intrinsic.momentumLinearEquiv B).symm (fun i => w (.inr i)) v)
  left_inv u := by
    funext v i
    cases i with
    | inl i =>
      change B.realPosition.symm (B.realPosition (fun v i => u v (.inl i))) v i = _
      rw [B.realPosition.symm_apply_apply]
    | inr i =>
      change (IntrinsicMomentumEquiv.Intrinsic.momentumLinearEquiv B).symm ((IntrinsicMomentumEquiv.Intrinsic.momentumLinearEquiv B) (fun v i => u v (.inr i))) v i = _
      rw [LinearEquiv.symm_apply_apply]
  right_inv w := by
    funext i
    cases i with
    | inl i =>
      change B.realPosition (B.realPosition.symm (fun i => w (.inl i))) i = _
      rw [B.realPosition.apply_symm_apply]
    | inr i =>
      change (IntrinsicMomentumEquiv.Intrinsic.momentumLinearEquiv B) ((IntrinsicMomentumEquiv.Intrinsic.momentumLinearEquiv B).symm (fun i => w (.inr i))) i = _
      rw [LinearEquiv.apply_symm_apply]
  map_add' u v := by
    funext i
    cases i with
    | inl i =>
      change B.realPosition ((fun w j => u w (.inl j)) + (fun w j => v w (.inl j))) i = _
      rw [map_add]
      rfl
    | inr i =>
      change (IntrinsicMomentumEquiv.Intrinsic.momentumLinearEquiv B) ((fun w j => u w (.inr j)) + (fun w j => v w (.inr j))) i = _
      rw [map_add]
      rfl
  map_smul' c u := by
    funext i
    cases i with
    | inl i =>
      change B.realPosition (c • (fun w j => u w (.inl j))) i = _
      rw [map_smul]
      rfl
    | inr i =>
      change (IntrinsicMomentumEquiv.Intrinsic.momentumLinearEquiv B) (c • (fun w j => u w (.inr j))) i = _
      rw [map_smul]
      rfl

def cotangentContinuousEquiv : (Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) ≃L[ℝ]
    ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℝ) := (cotangentLinearEquiv B).toContinuousLinearEquiv

def residualContinuousEquiv : (Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) ≃L[ℝ]
    (Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :=
  (cotangentContinuousEquiv B).trans B.realPhase.symm

theorem residual_equiv_apply (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    residualContinuousEquiv B u = IntrinsicResidualPhase.Intrinsic.residualPhase B u := rfl

theorem residual_equiv_pairing {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K}
    (hC : Adelic.DataTheta.CoordinateIdentification B P) (u v : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    (∑ w : Fin A.places, Adelic.DataTheta.standardPairing (residualContinuousEquiv B u w) (residualContinuousEquiv B v w)) =
      ∑ w : Fin A.places, Adelic.DataTheta.standardPairing (u w) (v w) := by
  rw [← hC.2.2.2.2.2.1]
  change Adelic.DataTheta.standardPairing (B.realPhase (B.realPhase.symm (IntrinsicCotangentAction.Intrinsic.cotangentCoordinates B u)))
    (B.realPhase (B.realPhase.symm (IntrinsicCotangentAction.Intrinsic.cotangentCoordinates B v))) = _
  rw [B.realPhase.apply_symm_apply,B.realPhase.apply_symm_apply,IntrinsicCotangentPairing.Intrinsic.cotangent_pairing]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualEquiv.Intrinsic
