import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.KernelSumComplexTransition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonIndexedGraphs
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicPeriodGraph

/-! # Intrinsic Kernel Sum Period -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumPeriod.CM

noncomputable section

/-! The total period returned by full native ThetaKernel is the exact fixed
rational symplectic transform of the two actual source line periods. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification N)

def sumComparisonIndexedPeriod (z : B.Domain) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (PeriodTotal.CM.TotalPositions K places) :=
  ComparisonIndexedGraphs.CM.comparisonIndexedPeriod N (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)

theorem native_c38_source_geometric_frame (z : B.Domain) (u : PeriodTotal.CM.TotalPositions K places → ℂ) :
    SourceComponents.CM.directSourceComplexComponents K Q hμ B.other_place (AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val u) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
        (SourceFrameComponents.CM.directSourceFrameCoefficients K Q u) :=
  (SourceGeometricFrame.CM.direct_source_geometric_frame K d Q hμ B.other_place z u).trans
    (IntrinsicKernelSumModel.CM.native_c38_sum_geometric_frame K Q hμ (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
      (SourceFrameComponents.CM.directSourceFrameCoefficients K Q u)).symm

variable (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))

include hN hG in
theorem sum_comparison_graph_relation (z : B.Domain) (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    let α := (IntrinsicKernelSumTransition.CM.sumComparisonTransitionMatrix K Q hμ N (fun j => (L j).coordinates)).map
      (algebraMap ℚ ℂ) *ᵥ Sum.elim
        ((BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)).matrix.mulVec x) x
    (sumComparisonIndexedPeriod K d Q hμ N z).matrix.mulVec (fun i => α (.inr i)) =
      fun i => α (.inl i) := by
  let w := TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (L j).coordinates)
    (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) x
  let u := AdaptedTotal.CM.totalAdaptedCoordinates K places d w
  have hrec : AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val u = w :=
    AdaptedTotal.CM.total_native_frame_recovers_graph K L z.val z.property x
  have hf := (congrArg (SourceComponents.CM.directSourceComplexComponents K Q hμ B.other_place) hrec).symm.trans
    (native_c38_source_geometric_frame K d Q hμ z u)
  have ht := (KernelSumComplexTransition.CM.sum_comparison_complex_transition K Q hμ N hN (fun j => (L j).coordinates) w).trans hf
  have hp := ComparisonIndexedGraphs.CM.comparison_indexed_graph_equation N hG (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
    (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
    ((IntrinsicKernelSumTransition.CM.sumComparisonTransitionMatrix K Q hμ N (fun j => (L j).coordinates)).map (algebraMap ℚ ℂ) *ᵥ
      ComplexTransition.CM.totalComplexCoordinates K (fun j => (L j).coordinates) w) (SourceFrameComponents.CM.directSourceFrameCoefficients K Q u) ht
  simpa only [w, TotalPeriodGraphs.CM.total_graph_coordinates] using! hp

include hG in
theorem sum_comparison_period_transform
    (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta) (z : B.Domain) :
    sumComparisonIndexedPeriod K d Q hμ N z =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
        (fun j => (L j).coordinates) hL)).transformSiegel
          (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) := by
  apply IndexedGraphRelation.CM.symplectic_period_eq_of_graph
  intro x
  exact sum_comparison_graph_relation K d Q hμ N hN hG L z x

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumPeriod.CM
