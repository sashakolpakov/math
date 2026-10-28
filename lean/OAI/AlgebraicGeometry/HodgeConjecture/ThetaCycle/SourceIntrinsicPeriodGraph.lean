import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicTransition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceGeometricFrame
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedGraphRelation

/-! # Source Intrinsic Period Graph -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicPeriodGraph.CM

noncomputable section

/-! Equality of the actual source and native period graphs after the
fixed rational symplectic transition, with every frame and index retained. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)

def directSourceIndexedPeriod (z : B.Domain) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (PeriodTotal.CM.TotalPositions K places) :=
  ReindexTheta.CM.siegelReindex (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm
    ((SourceComponents.CM.directSourceComparison K Q hμ hother).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))

theorem source_native_phase_graph_relation (z : B.Domain)
    (α : (PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) → ℂ)
    (a : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) → ℂ)
    (h : SourceIntrinsicTransition.CM.directSourcePhaseRealization K Q hμ hother α =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) a) :
    (directSourceIndexedPeriod K Q hμ hother z).matrix.mulVec (fun i => α (.inr i)) =
      fun i => α (.inl i) := by
  let N := SourceComponents.CM.directSourceComparison K Q hμ hother
  let t := (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).val.mulVec a
  have hgeom : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification N := RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_geometry _ _
  have hg : N.complexPhase (Sum.elim t ((N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix.mulVec t)) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) a :=
    hgeom.2.2.2.2.2.2.1 (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) a
  have hp := N.complexPhase.injective (h.trans hg.symm)
  exact IndexedGraphRelation.CM.reindexed_swapped_graph_equation (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
    (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix α t hp

omit d Q hμ hother in
theorem source_native_total_graph_relation
    (d : Fin 2 → Gal(K/ℚ) → Bool)
    (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
    (hμ : ∀ j, d j (places.representative places.distinguished) = true)
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
    (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
    (z : B.Domain) (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    let α := (SourceIntrinsicTransition.CM.sourceNativeTransitionMatrix K Q hμ hother (fun j => (L j).coordinates)).map
      (algebraMap ℚ ℂ) *ᵥ Sum.elim
        ((BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)).matrix.mulVec x) x
    (directSourceIndexedPeriod K Q hμ hother z).matrix.mulVec (fun i => α (.inr i)) =
      fun i => α (.inl i) := by
  let w := TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (L j).coordinates)
    (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) x
  let u := AdaptedTotal.CM.totalAdaptedCoordinates K places d w
  have hrec : AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val u = w :=
    AdaptedTotal.CM.total_native_frame_recovers_graph K L z.val z.property x
  have hg := SourceGeometricFrame.CM.direct_source_geometric_frame K d Q hμ hother z u
  have hf := (congrArg (SourceComponents.CM.directSourceComplexComponents K Q hμ hother) hrec).symm.trans hg
  have ht := (SourceIntrinsicTransition.CM.source_native_complex_transition K Q hμ hother (fun j => (L j).coordinates) w).trans hf
  have hp := source_native_phase_graph_relation K Q hμ hother z
    ((SourceIntrinsicTransition.CM.sourceNativeTransitionMatrix K Q hμ hother (fun j => (L j).coordinates)).map (algebraMap ℚ ℂ) *ᵥ
      ComplexTransition.CM.totalComplexCoordinates K (fun j => (L j).coordinates) w) (SourceFrameComponents.CM.directSourceFrameCoefficients K Q u) ht
  simpa only [w, TotalPeriodGraphs.CM.total_graph_coordinates] using! hp

omit d Q hμ hother in
theorem source_native_period_transform
    (d : Fin 2 → Gal(K/ℚ) → Bool)
    (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
    (hμ : ∀ j, d j (places.representative places.distinguished) = true)
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
    (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
    (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)
    (z : B.Domain) :
    directSourceIndexedPeriod K Q hμ hother z =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
        (fun j => (L j).coordinates) hL)).transformSiegel
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) := by
  apply IndexedGraphRelation.CM.symplectic_period_eq_of_graph
  intro x
  exact source_native_total_graph_relation K d Q hμ hother L z x

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicPeriodGraph.CM
