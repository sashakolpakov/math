import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFrameComponents
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.NormalizedFrame

/-! # Source Geometric Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceGeometricFrame.CM

noncomputable section

/-! The complete two-line source frame maps to the actual native Hodge
frame by one constant diagonal coefficient change at every CM place. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.NormalizedFrame

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)

include places in
theorem source_ball_coefficient_radius : (B.b : ℂ) = -(SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ) ^ 2 := by
  have h := CMFormCoordinates.CM.source_fixed_element_eq_real K places B.b B.conjugate_b places.distinguished
  rw [HeckeCycles.ReferenceDatum.CM.embeddings_distinguished] at h
  change ((B.b : ℂ).re : ℂ) = (B.b : ℂ) at h
  rw [← h, ← Complex.ofReal_pow, SourceIntrinsicBall.CM.source_ball_radius_sq]
  simp only [Complex.ofReal_neg, neg_neg]

theorem direct_source_active_components (w : ComplexTransition.CM.TotalAmbient K) (j : Fin 2) :
    (fun i => (SourceComponents.CM.directSourceComplexComponents K Q hμ hother w places.distinguished).1 (i, j),
     fun i => (SourceComponents.CM.directSourceComplexComponents K Q hμ hother w places.distinguished).2 (i, j)) =
    CMExtraction.NormalizedFrame.normalizeWeightedPhase (SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ)
      (SourceScales.CM.sourceNativeMultiplicityScale K places Q.delta Q.a places.distinguished j : ℂ)
      (fun i => (SourceComponents.CM.sourcePairedTensorCoordinates K places w places.distinguished).1 (i, j),
       fun i => (SourceComponents.CM.sourcePairedTensorCoordinates K places w places.distinguished).2 (i, j)) := by
  apply Prod.ext <;> funext i
  · rw [SourceFrameComponents.CM.direct_source_components_fst]
    fin_cases i <;> simp [CMExtraction.NormalizedFrame.normalizeWeightedPhase, SourceScales.CM.sourceNativeTensorScale,
      SourceScales.CM.source_native_place_radius_active, Matrix.mulVec_diagonal, mul_comm]
  · rw [SourceFrameComponents.CM.direct_source_components_snd]
    fin_cases i <;> simp [CMExtraction.NormalizedFrame.normalizeWeightedPhase, SourceScales.CM.sourceNativeTensorScale,
      SourceScales.CM.source_native_place_radius_active, hμ j, Matrix.mulVec_diagonal, mul_comm]

omit Q hμ hother in
theorem source_total_active_frame_pair (d : Fin 2 → Gal(K/ℚ) → Bool)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (u : PeriodTotal.CM.TotalPositions K places → ℂ) (j : Fin 2) :
    (fun i => (SourceComponents.CM.sourcePairedTensorCoordinates K places (AdaptedTotal.CM.totalNativePeriodFrame K B places d z u)
      places.distinguished).1 (i, j),
     fun i => (SourceComponents.CM.sourcePairedTensorCoordinates K places (AdaptedTotal.CM.totalNativePeriodFrame K B places d z u)
      places.distinguished).2 (i, j)) =
    CMExtraction.UnitaryFrameAction.weightedFrame (B.b : ℂ) z (fun i => u (SourceFrameComponents.CM.sourceTotalSlot K places places.distinguished i j)) := by
  rw [SourceFrameComponents.CM.source_paired_total_frame]
  simp only [Geometry.ComplexBall.PrescribedSignsB.placeFrame, ite_true, SourceFrameAction.CM.source_local_frame_weighted, HeckeCycles.ReferenceDatum.CM.embeddings_distinguished]
  rfl

omit Q hμ hother in
theorem source_total_compact_frame_pair (d : Fin 2 → Gal(K/ℚ) → Bool)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (u : PeriodTotal.CM.TotalPositions K places → ℂ) (v : Fin places.count)
    (hv : v ≠ places.distinguished) (j : Fin 2) :
    (fun i => (SourceComponents.CM.sourcePairedTensorCoordinates K places (AdaptedTotal.CM.totalNativePeriodFrame K B places d z u) v).1 (i, j),
     fun i => (SourceComponents.CM.sourcePairedTensorCoordinates K places (AdaptedTotal.CM.totalNativePeriodFrame K B places d z u) v).2 (i, j)) =
    if d j (places.representative v) then (0, fun i => u (SourceFrameComponents.CM.sourceTotalSlot K places v i j))
      else (fun i => u (SourceFrameComponents.CM.sourceTotalSlot K places v i j), 0) := by
  rw [SourceFrameComponents.CM.source_paired_total_frame]
  simp only [Geometry.ComplexBall.PrescribedSignsB.placeFrame, ite_eq_right hv]
  split_ifs <;> rfl

omit d Q hμ hother in
theorem direct_source_geometric_frame
    (d : Fin 2 → Gal(K/ℚ) → Bool)
    (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
    (hμ : ∀ j, d j (places.representative places.distinguished) = true)
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
    (z : B.Domain) (u : PeriodTotal.CM.TotalPositions K places → ℂ) :
    SourceComponents.CM.directSourceComplexComponents K Q hμ hother (AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val u) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
        (SourceFrameComponents.CM.directSourceFrameCoefficients K Q u) := by
  refine funext (fun v : Fin places.count => ?_)
  by_cases hv : v = places.distinguished
  · subst v
    have hn (j : Fin 2) := direct_source_active_components K Q hμ hother
      (AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val u) j
    simp_rw [source_total_active_frame_pair, source_ball_coefficient_radius K (places := places),
      CMExtraction.NormalizedFrame.weightedFrame_normalized _ _
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (SourceIntrinsicBall.CM.source_ball_radius_pos K B)))] at hn
    apply Prod.ext <;> funext ⟨i, j⟩
    · exact (congrFun (congrArg Prod.fst (hn j)) i).trans (by
        simp [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, BallArithmetic.CM.directSourceBallArithmeticData, SourceFrameComponents.CM.directSourceFrameCoefficients,
          SourceFrameComponents.CM.directSourceFrameScale, CMExtraction.NormalizedFrame.lineAnnihilatorFrame, SourceIntrinsicBall.CM.sourceNativeBallPoint,
          Matrix.mulVec_diagonal, mul_comm])
    · exact (congrFun (congrArg Prod.snd (hn j)) i).trans (by
        simp [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, BallArithmetic.CM.directSourceBallArithmeticData, SourceFrameComponents.CM.directSourceFrameCoefficients,
          SourceFrameComponents.CM.directSourceFrameScale, CMExtraction.NormalizedFrame.lineAnnihilatorFrame, SourceIntrinsicBall.CM.sourceNativeBallPoint,
          Matrix.mulVec_diagonal, mul_comm])
  · have hw (j : Fin 2) := source_total_compact_frame_pair K (B := B) d z.val u v hv j
    apply Prod.ext <;> funext ⟨i, j⟩
    · refine (SourceFrameComponents.CM.direct_source_components_fst K Q hμ hother
        (AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val u) v (i, j)).trans ?_
      have hx := congrFun (congrArg Prod.fst (hw j)) i
      dsimp only at hx
      simp only [hx]
      cases hd : d j (places.representative v) <;>
        simp [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, BallArithmetic.CM.directSourceBallArithmeticData, SourceFrameComponents.CM.directSourceFrameCoefficients,
          SourceFrameComponents.CM.directSourceFrameScale, hv, hd]
    · refine (SourceFrameComponents.CM.direct_source_components_snd K Q hμ hother
        (AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val u) v (i, j)).trans ?_
      have hx := congrFun (congrArg Prod.snd (hw j)) i
      dsimp only at hx
      simp only [hx]
      cases hd : d j (places.representative v) <;>
        simp [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, BallArithmetic.CM.directSourceBallArithmeticData, SourceFrameComponents.CM.directSourceFrameCoefficients,
          SourceFrameComponents.CM.directSourceFrameScale, hv, hd]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceGeometricFrame.CM
