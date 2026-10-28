import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicTransition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumTrace

/-! # Intrinsic Kernel Sum Transition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumTransition.CM

noncomputable section

/-! The original total rational coordinates and the native ThetaKernel sum
coordinates are related by one fixed rational symplectic matrix. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q))

def sumComparisonIndexedCoordinates :
    TransportNew.CM.TensorPositions K ≃ₗ[ℚ] ((PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) → ℚ) :=
  (IntrinsicKernelSumTrace.CM.sourceSumRationalCoordinates K Q.delta Q.delta_imaginary Q.delta_ne_zero
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) Q.a
    (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q)
    (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q) N).trans
      (LinearEquiv.funCongrLeft ℚ ℚ ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).sumCongr (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)))

include hN in
theorem sum_comparison_indexed_pairing (x y : TransportNew.CM.TensorPositions K) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (sumComparisonIndexedCoordinates K Q hμ N x)
      (sumComparisonIndexedCoordinates K Q hμ N y) =
      Algebra.trace ℚ K (Q.delta * TransportNew.CM.tensorHermitian K B.b Q.a x y) := by
  let r := IntrinsicKernelSumTrace.CM.sourceSumRationalCoordinates K Q.delta Q.delta_imaginary Q.delta_ne_zero
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) Q.a
    (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q) (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q) N
  change RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (fun i => r x (((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).sumCongr
    (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)) i)) (fun i => r y (((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).sumCongr
    (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)) i)) = _
  refine (SourceIntrinsicTransition.CM.source_total_index_pairing K places (r x) (r y)).trans ?_
  exact IntrinsicKernelSumTrace.CM.source_sum_rational_coordinates_pairing K Q.delta Q.delta_imaginary Q.delta_ne_zero
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) Q.a
    (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q)
    (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q) N hN x y

variable (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)

def sumComparisonTransitionLinear :
    ((PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) → ℚ) ≃ₗ[ℚ]
      ((PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) → ℚ) :=
  (PeriodTotal.CM.totalSymplecticCoordinates K C).symm.trans (sumComparisonIndexedCoordinates K Q hμ N)

def sumComparisonTransitionMatrix :
    Matrix (PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places)
      (PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) ℚ :=
  LinearMap.toMatrix' (sumComparisonTransitionLinear K Q hμ N C).toLinearMap

theorem sum_comparison_transition_apply (x : TransportNew.CM.TensorPositions K) :
    (sumComparisonTransitionMatrix K Q hμ N C).mulVec (PeriodTotal.CM.totalSymplecticCoordinates K C x) =
      sumComparisonIndexedCoordinates K Q hμ N x := by
  rw [sumComparisonTransitionMatrix, LinearMap.toMatrix'_mulVec]
  change sumComparisonIndexedCoordinates K Q hμ N
    ((PeriodTotal.CM.totalSymplecticCoordinates K C).symm (PeriodTotal.CM.totalSymplecticCoordinates K C x)) = _
  rw [LinearEquiv.symm_apply_apply]

include hN in
theorem sum_comparison_transition_symplectic
    (hC : ∀ j, (C j).a = Q.a j ∧ (C j).delta = Q.delta) :
    sumComparisonTransitionMatrix K Q hμ N C ∈ Matrix.symplecticGroup (PeriodTotal.CM.TotalPositions K places) ℚ := by
  apply RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization.preserving_coordinatePairing_symplectic
  intro x y
  obtain ⟨u, rfl⟩ := (PeriodTotal.CM.totalSymplecticCoordinates K C).surjective x
  obtain ⟨v, rfl⟩ := (PeriodTotal.CM.totalSymplecticCoordinates K C).surjective y
  rw [sum_comparison_transition_apply, sum_comparison_transition_apply,
    sum_comparison_indexed_pairing K Q hμ N hN, PeriodTotal.CM.total_symplectic_coordinates_pairing K C Q.delta Q.a hC]

def sumComparisonSymplecticTransition
    (hC : ∀ j, (C j).a = Q.a j ∧ (C j).delta = Q.delta) :
    Matrix.symplecticGroup (PeriodTotal.CM.TotalPositions K places) ℚ :=
  ⟨sumComparisonTransitionMatrix K Q hμ N C, sum_comparison_transition_symplectic K Q hμ N hN C hC⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumTransition.CM
