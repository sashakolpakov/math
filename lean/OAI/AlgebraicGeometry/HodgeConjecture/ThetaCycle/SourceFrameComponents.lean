import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceScales
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AdaptedTotal
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFrameAction

/-! # Source Frame Components -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFrameComponents.CM

noncomputable section

/-! Component formulas for the literal total source frame after native
normalization, retaining every multiplicity and CM-place index. -/

open scoped Classical _root_.NumberField Kronecker
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]

def sourceTotalSlot (places : HeckeCycles.GeometricSource.CM.Places K) (v : Fin places.count) (i : Fin 3) (j : Fin 2) :
    PeriodTotal.CM.TotalPositions K places := if j = 0 then Sum.inl (v, i) else Sum.inr (v, i)

theorem source_paired_total_frame (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (u : PeriodTotal.CM.TotalPositions K places → ℂ)
    (v : Fin places.count) (j : Fin 2) :
    (fun i => (SourceComponents.CM.sourcePairedTensorCoordinates K places (AdaptedTotal.CM.totalNativePeriodFrame K B places d z u) v).1 (i, j),
     fun i => (SourceComponents.CM.sourcePairedTensorCoordinates K places (AdaptedTotal.CM.totalNativePeriodFrame K B places d z u) v).2 (i, j)) =
      Geometry.ComplexBall.PrescribedSignsB.placeFrame (CoefficientPeriods.CM.ballMatrix K B places) places.distinguished
        (fun v => d j (places.representative v)) z v (fun i => u (sourceTotalSlot K places v i j)) := by
  change ((fun i => (Symplectic.CM.galoisToPaired K places (Prescribed.CM.nativePeriodFrame K B places (d j) z _) v).1 i),
    (fun i => (Symplectic.CM.galoisToPaired K places (Prescribed.CM.nativePeriodFrame K B places (d j) z _) v).2 i)) = _
  simp only [Prescribed.CM.nativePeriodFrame, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rfl

variable {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)

theorem direct_source_components_fst (w : ComplexTransition.CM.TotalAmbient K) (v : Fin places.count) (ij : Fin 3 × Fin 2) :
    (SourceComponents.CM.directSourceComplexComponents K Q hμ hother w v).1 ij =
      (SourceScales.CM.sourceNativeTensorScale K places Q.delta Q.a B.b v ij : ℂ) *
        (SourceComponents.CM.sourcePairedTensorCoordinates K places w v).1 ij := by
  change (IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) v).mulVec
    (SourceComponents.CM.sourcePairedTensorCoordinates K places w v).1 ij = _
  rw [SourceScales.CM.direct_source_tensor_normalizer, Matrix.mulVec_diagonal]

theorem direct_source_components_snd (w : ComplexTransition.CM.TotalAmbient K) (v : Fin places.count) (ij : Fin 3 × Fin 2) :
    (SourceComponents.CM.directSourceComplexComponents K Q hμ hother w v).2 ij =
      (if v = places.distinguished ∧ ij.1 = 2 then (-1 : ℂ) else 1) *
        (if !(d ij.2 v) then (1 : ℂ) else -1) *
        ((SourceScales.CM.sourceNativeTensorScale K places Q.delta Q.a B.b v ij : ℂ) *
          (SourceComponents.CM.sourcePairedTensorCoordinates K places w v).2 ij) := by
  change _ * _ * ((IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) v).map star).mulVec
    (SourceComponents.CM.sourcePairedTensorCoordinates K places w v).2 ij = _
  rw [SourceScales.CM.direct_source_tensor_normalizer, Matrix.diagonal_map (star_zero _)]
  simp only [Matrix.mulVec_diagonal]
  rw [show star (SourceScales.CM.sourceNativeTensorScale K places Q.delta Q.a B.b v ij : ℂ) =
    (SourceScales.CM.sourceNativeTensorScale K places Q.delta Q.a B.b v ij : ℂ) from Complex.conj_ofReal _]
  rfl

def directSourceFrameScale (v : Fin places.count) (ij : Fin 3 × Fin 2) : ℂ :=
  if v = places.distinguished then
    if ij.1 = 0 then (SourceScales.CM.sourceNativeMultiplicityScale K places Q.delta Q.a v ij.2 : ℂ) *
      (SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ)
    else -(SourceScales.CM.sourceNativeMultiplicityScale K places Q.delta Q.a v ij.2 : ℂ)
  else if d ij.2 v then -(SourceScales.CM.sourceNativeTensorScale K places Q.delta Q.a B.b v ij : ℂ)
    else (SourceScales.CM.sourceNativeTensorScale K places Q.delta Q.a B.b v ij : ℂ)

theorem direct_source_frame_scale_ne_zero (v : Fin places.count) (ij : Fin 3 × Fin 2) :
    directSourceFrameScale K Q v ij ≠ 0 := by
  have hc : (SourceScales.CM.sourceNativeMultiplicityScale K places Q.delta Q.a v ij.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (SourceScales.CM.source_native_multiplicity_scale_pos K places
      Q.delta Q.delta_imaginary Q.delta_ne_zero Q.a
      (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q) v ij.2))
  have ht : (SourceScales.CM.sourceNativeTensorScale K places Q.delta Q.a B.b v ij : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (SourceScales.CM.source_native_tensor_scale_pos K places
      Q.delta Q.delta_imaginary Q.delta_ne_zero Q.a
      (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q) B.b B.conjugate_b
      (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) v ij))
  unfold directSourceFrameScale
  split_ifs
  · exact mul_ne_zero hc (Complex.ofReal_ne_zero.mpr (ne_of_gt (SourceIntrinsicBall.CM.source_ball_radius_pos K B)))
  · exact neg_ne_zero.mpr hc
  · exact neg_ne_zero.mpr ht
  · exact ht

def directSourceFrameCoefficients : (PeriodTotal.CM.TotalPositions K places → ℂ) →ₗ[ℂ]
    (Fin places.count × (Fin 3 × Fin 2) → ℂ) where
  toFun u i := directSourceFrameScale K Q i.1 i.2 * u (sourceTotalSlot K places i.1 i.2.1 i.2.2)
  map_add' u v := by funext i; exact mul_add _ _ _
  map_smul' c u := by funext i; exact mul_left_comm _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFrameComponents.CM
