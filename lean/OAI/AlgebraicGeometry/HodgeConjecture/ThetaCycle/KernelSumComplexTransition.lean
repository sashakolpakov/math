import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicTransition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumTransition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumComponents

/-! # Kernel Sum Complex Transition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.KernelSumComplexTransition.CM

noncomputable section

/-! The fixed rational symplectic transition complexifies to the
literal source-to-native tensor map, as checked on all rational vectors. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q))

abbrev sumComparisonPhaseRealization :
    ((PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) → ℂ) →ₗ[ℂ]
      RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) :=
  SourceIntrinsicTransition.CM.indexedSwappedPhaseMap (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
    N.complexPhase

include hN in
theorem sum_comparison_phase_rational (x : TransportNew.CM.TensorPositions K) :
    sumComparisonPhaseRealization K Q hμ N
      (fun i => (IntrinsicKernelSumTransition.CM.sumComparisonIndexedCoordinates K Q hμ N x i : ℂ)) =
      SourceComponents.CM.directSourceComplexComponents K Q hμ B.other_place (ComplexTransition.CM.totalEmbedding K x) := by
  let e := (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).sumCongr (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
  let r := IntrinsicKernelSumTrace.CM.sourceSumRationalCoordinates K Q.delta Q.delta_imaginary Q.delta_ne_zero
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) Q.a
    (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q) (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q) N
  have hinput : RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => (IntrinsicKernelSumTransition.CM.sumComparisonIndexedCoordinates K Q hμ N x (e.symm i) : ℂ)) =
      (fun i => (N.rationalPhase
        ((IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q).rational.coordinates
          (QuadraticTensor.CM.quadraticTensorPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x)) i : ℂ)) := by
    refine funext (fun i : (Fin places.count × (Fin 3 × Fin 2)) ⊕
      (Fin places.count × (Fin 3 × Fin 2)) => ?_)
    cases i with
    | inl i =>
        change ((r x (e (e.symm (.inr i))) : ℚ) : ℂ) = ((r x (.inr i) : ℚ) : ℂ)
        exact congrArg (fun j => ((r x j : ℚ) : ℂ)) (e.apply_symm_apply (.inr i))
    | inr i =>
        change ((r x (e (e.symm (.inl i))) : ℚ) : ℂ) = ((r x (.inl i) : ℚ) : ℂ)
        exact congrArg (fun j => ((r x j : ℚ) : ℂ)) (e.apply_symm_apply (.inl i))
  change N.complexPhase
    (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => (IntrinsicKernelSumTransition.CM.sumComparisonIndexedCoordinates K Q hμ N x (e.symm i) : ℂ))) = _
  refine (congrArg N.complexPhase hinput).trans ?_
  exact IntrinsicKernelSumComponents.CM.native_c38_sum_complex_phase_rational K Q hμ N hN x

variable (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)

theorem sum_comparison_transition_complex_rational (x : TransportNew.CM.TensorPositions K) :
    (IntrinsicKernelSumTransition.CM.sumComparisonTransitionMatrix K Q hμ N C).map (algebraMap ℚ ℂ) *ᵥ
      (fun i => (PeriodTotal.CM.totalSymplecticCoordinates K C x i : ℂ)) =
      fun i => (IntrinsicKernelSumTransition.CM.sumComparisonIndexedCoordinates K Q hμ N x i : ℂ) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap ℚ ℂ) (IntrinsicKernelSumTransition.CM.sumComparisonTransitionMatrix K Q hμ N C)
    (PeriodTotal.CM.totalSymplecticCoordinates K C x) i).symm.trans
    (congrArg (algebraMap ℚ ℂ) (congrFun (IntrinsicKernelSumTransition.CM.sum_comparison_transition_apply K Q hμ N C x) i))

include hN in
theorem sum_comparison_complex_transition (w : ComplexTransition.CM.TotalAmbient K) :
    sumComparisonPhaseRealization K Q hμ N
      ((IntrinsicKernelSumTransition.CM.sumComparisonTransitionMatrix K Q hμ N C).map (algebraMap ℚ ℂ) *ᵥ
        ComplexTransition.CM.totalComplexCoordinates K C w) = SourceComponents.CM.directSourceComplexComponents K Q hμ B.other_place w := by
  let f := (sumComparisonPhaseRealization K Q hμ N).comp
    ((Matrix.toLin' ((IntrinsicKernelSumTransition.CM.sumComparisonTransitionMatrix K Q hμ N C).map (algebraMap ℚ ℂ))).comp
      (ComplexTransition.CM.totalComplexCoordinates K C).toLinearMap)
  have he : f = SourceComponents.CM.directSourceComplexComponents K Q hμ B.other_place := by
    apply ComplexTransition.CM.linear_maps_eq_of_rational_coordinates (PeriodTotal.CM.totalSymplecticCoordinates K C)
      (ComplexTransition.CM.totalComplexCoordinates K C) (ComplexTransition.CM.totalEmbedding K) (ComplexTransition.CM.total_complex_coordinates_embedding K C)
    intro x
    change sumComparisonPhaseRealization K Q hμ N
      ((IntrinsicKernelSumTransition.CM.sumComparisonTransitionMatrix K Q hμ N C).map (algebraMap ℚ ℂ) *ᵥ
        ComplexTransition.CM.totalComplexCoordinates K C (ComplexTransition.CM.totalEmbedding K x)) = _
    rw [ComplexTransition.CM.total_complex_coordinates_embedding, sum_comparison_transition_complex_rational,
      sum_comparison_phase_rational K Q hμ N hN]
    rfl
  exact LinearMap.congr_fun he w

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.KernelSumComplexTransition.CM
