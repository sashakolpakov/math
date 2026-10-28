import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceProjection
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement

/-! # Intrinsic Position Projection -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionProjection.Intrinsic

noncomputable section

/-! Projection to an archimedean place preserves the actual position
polarization. This follows from the complete native coordinate identity. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceProjection.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealComplexification.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)

def realPositionProjection (v : Fin A.places) : (Adelic.BallGeometryData.FrameIndex A → ℝ) →ₗ[ℝ] (Adelic.BallGeometryData.FrameIndex A → ℝ) :=
  B.realPosition.toLinearMap.comp ((IntrinsicPlaceProjection.Intrinsic.placeProjection (R := ℝ) v).comp B.realPosition.symm.toLinearMap)

variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem real_place_positions (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (v : Fin A.places) (x : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℝ) :
    IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℝ _ (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v x) = realPositionProjection B v (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℝ _ x) := by
  let u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6 := B.realPhase.symm x
  let q : Adelic.BallGeometryData.RealPositions A := fun w j => u w (.inl j)
  have hq : IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℝ _ x = B.realPosition q :=
    (congrArg (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℝ _) (B.realPhase.apply_symm_apply x)).symm.trans
      (funext (hC.2.2.2.2.1 u))
  have hinv : B.realPosition.symm (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℝ _ x) = q :=
    (congrArg B.realPosition.symm hq).trans (B.realPosition.symm_apply_apply q)
  have hlocal : (fun w j => (Pi.single v (u v) : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) w (.inl j)) =
      Pi.single v (q v) := by
    funext w j
    by_cases hw : w = v
    · subst w
      simp [q]
    · simp [hw]
  have hl := funext (hC.2.2.2.2.1 (Pi.single v (u v)))
  have hr : realPositionProjection B v (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℝ _ x) = B.realPosition (Pi.single v (q v)) :=
    congrArg (fun y : Adelic.BallGeometryData.RealPositions A => B.realPosition (Pi.single v (y v))) hinv
  exact hl.trans ((congrArg B.realPosition hlocal).trans hr.symm)

theorem complex_place_positions (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (v : Fin A.places) (x : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℂ) :
    IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ (IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v) x) =
      IntrinsicRealComplexification.Intrinsic.complexifiedLinear (realPositionProjection B v) (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ x) := by
  have he : (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _).comp (IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v)) =
      (IntrinsicRealComplexification.Intrinsic.complexifiedLinear (realPositionProjection B v)).comp (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _) := by
    apply IntrinsicRealComplexification.Intrinsic.complexLinear_ext_real
    intro y
    change IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ (IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v) (fun i => (y i : ℂ))) =
      IntrinsicRealComplexification.Intrinsic.complexifiedLinear (realPositionProjection B v) (fun i => (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℝ _ y i : ℂ))
    rw [IntrinsicRealComplexification.Intrinsic.complexifiedLinear_real,IntrinsicRealComplexification.Intrinsic.complexifiedLinear_real]
    exact congrArg (fun t => fun i => (t i : ℂ)) (real_place_positions B hC v y)
  exact LinearMap.congr_fun he x

theorem coordinate_positions_projection (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (v : Fin A.places) (w : Adelic.BallGeometryData.ComplexPhase A) :
    IntrinsicRealComplexification.Intrinsic.complexifiedLinear (realPositionProjection B v) (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ (B.complexPhase.symm w)) =
      IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ (B.complexPhase.symm (IntrinsicPlaceProjection.Intrinsic.geometricPlaceProjection A v w)) := by
  have h := IntrinsicPlaceProjection.Intrinsic.complex_place_projection B hC v (B.complexPhase.symm w)
  rw [B.complexPhase.apply_symm_apply] at h
  have he : IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v) (B.complexPhase.symm w) =
      B.complexPhase.symm (IntrinsicPlaceProjection.Intrinsic.geometricPlaceProjection A v w) :=
    (B.complexPhase.symm_apply_apply _).symm.trans (congrArg B.complexPhase.symm h)
  exact (complex_place_positions B hC v (B.complexPhase.symm w)).symm.trans
    (congrArg (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _) he)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionProjection.Intrinsic
