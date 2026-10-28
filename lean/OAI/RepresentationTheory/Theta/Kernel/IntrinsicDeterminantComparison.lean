import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology

/-! # Intrinsic Determinant Comparison -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantComparison.Intrinsic

noncomputable section

/-! The half-determinant comparison is constant on the actual ball.
Its square is computed from the fixed native coordinate change. The
constant is therefore derived from coordinate and geometry identifications. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal OAI.RepresentationTheory.Theta.Kernel.IntrinsicHodgeSplit.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicComplexTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

def frameComparison : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) →ₗ[ℂ]
    (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :=
  (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S).symm.toLinearMap.comp (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPositionChange B₁ B₂ B)

def splitFrameEnd (z : Adelic.BallNatural.Ball) : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) →ₗ[ℂ]
    (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :=
  (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S).symm.toLinearMap.comp
    ((Matrix.toLin' (IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).val).comp
      (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S).toLinearMap)

theorem frameComparison_identity
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    (frameComparison B₁ B₂ B).comp (Matrix.toLin' (B.frame z).val) = splitFrameEnd B₁ B₂ z := by
  apply LinearMap.ext
  intro a
  have h := congrArg (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _)
    (IntrinsicComplexTransport.Intrinsic.complexPhaseChange_graph B₁ B₂ B hG₁ hG₂ hG z a)
  rw [IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPhaseChange_positions B₁ B₂ B hC₁ hC₂ hC] at h
  exact congrArg (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S).symm h

theorem splitFrameEnd_det (z : Adelic.BallNatural.Ball) :
    LinearMap.det (splitFrameEnd B₁ B₂ z) = (B₁.frame z).val.det * (B₂.frame z).val.det := by
  have h := LinearMap.det_conj
    (Matrix.toLin' (IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).val)
    (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S).symm.toLinearEquiv
  change LinearMap.det (splitFrameEnd B₁ B₂ z) = _ at h
  rw [h, LinearMap.det_toLin', IntrinsicBlockSiegel.Intrinsic.blockFrame_det]

theorem determinant_comparison
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    LinearMap.det (frameComparison B₁ B₂ B) * (B.frame z).val.det =
      (B₁.frame z).val.det * (B₂.frame z).val.det := by
  have h := congrArg LinearMap.det
    (frameComparison_identity B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG z)
  simpa only [LinearMap.det_comp, LinearMap.det_toLin', splitFrameEnd_det] using h

def halfFrameRatio (z : Adelic.BallNatural.Ball) : ℂ := B.halfFrame z / (B₁.halfFrame z * B₂.halfFrame z)

theorem halfFrameRatio_nonzero (hG₁ : Adelic.DataTheta.GeometryIdentification B₁)
    (hG₂ : Adelic.DataTheta.GeometryIdentification B₂) (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    halfFrameRatio B₁ B₂ B z ≠ 0 :=
  div_ne_zero (hG.2.2.2.2.2.1 z).1
    (mul_ne_zero (hG₁.2.2.2.2.2.1 z).1 (hG₂.2.2.2.2.2.1 z).1)

theorem halfFrameRatio_square
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    halfFrameRatio B₁ B₂ B z ^ 2 = (LinearMap.det (frameComparison B₁ B₂ B))⁻¹ := by
  have hd := determinant_comparison B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG z
  rw [← (hG.2.2.2.2.2.1 z).2, ← (hG₁.2.2.2.2.2.1 z).2,
    ← (hG₂.2.2.2.2.2.1 z).2, ← mul_pow] at hd
  have he : LinearMap.det (frameComparison B₁ B₂ B) =
      (B₁.halfFrame z * B₂.halfFrame z) ^ 2 / B.halfFrame z ^ 2 :=
    (eq_div_iff (pow_ne_zero 2 (hG.2.2.2.2.2.1 z).1)).mpr hd
  rw [halfFrameRatio, div_pow, he, inv_div]

theorem halfFrameRatio_constant
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) :
    ∀ z, halfFrameRatio B₁ B₂ B z = halfFrameRatio B₁ B₂ B IntrinsicBallTopology.Intrinsic.origin := by
  apply IntrinsicBallTopology.Intrinsic.constant_of_square
  · exact (IntrinsicBallTopology.Intrinsic.holomorphic_continuous B.halfFrame hG.2.2.2.2.1).div
      ((IntrinsicBallTopology.Intrinsic.holomorphic_continuous B₁.halfFrame hG₁.2.2.2.2.1).mul
        (IntrinsicBallTopology.Intrinsic.holomorphic_continuous B₂.halfFrame hG₂.2.2.2.2.1))
      (fun z => mul_ne_zero (hG₁.2.2.2.2.2.1 z).1 (hG₂.2.2.2.2.2.1 z).1)
  · intro z
    rw [halfFrameRatio_square B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG z,
      halfFrameRatio_square B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG IntrinsicBallTopology.Intrinsic.origin]
  · exact halfFrameRatio_nonzero B₁ B₂ B hG₁ hG₂ hG IntrinsicBallTopology.Intrinsic.origin

theorem native_half_frame_constant
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) :
    ∃ c : ℂˣ, ∀ z, B.halfFrame z = (c : ℂ) * (B₁.halfFrame z * B₂.halfFrame z) := by
  let c : ℂˣ := Units.mk0 (halfFrameRatio B₁ B₂ B IntrinsicBallTopology.Intrinsic.origin)
    (halfFrameRatio_nonzero B₁ B₂ B hG₁ hG₂ hG IntrinsicBallTopology.Intrinsic.origin)
  refine ⟨c,?_⟩
  intro z
  have h := halfFrameRatio_constant B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG z
  exact (div_eq_iff (mul_ne_zero (hG₁.2.2.2.2.2.1 z).1 (hG₂.2.2.2.2.2.1 z).1)).mp h

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantComparison.Intrinsic
