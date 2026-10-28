import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AdaptedTotal
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TransportedGraphFrame

/-! # Intrinsic Frame Transition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicFrameTransition.CM

noncomputable section

/-! ThetaCycle: the actual graph projector induces a constant transition
between the old and new native adapted frames. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)

def approximationNativeFrameTransition (z : HeckeCycles.GeometricSource.CM.BallChart) :
    (PeriodTotal.CM.TotalPositions K D.places → ℂ) →ₗ[ℂ] (PeriodTotal.CM.TotalPositions K D.places → ℂ) :=
  (AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.newThetaSigns K v)).comp
    ((CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm.toLinearMap.comp
      (AdaptedTotal.CM.totalNativePeriodFrame K D.ball D.places (FourSplittings.CM.initialThetaSigns K v) z))

theorem approximation_native_frame_transition_constant (z t : HeckeCycles.GeometricSource.CM.BallChart) :
    approximationNativeFrameTransition K D A z = approximationNativeFrameTransition K D A t := by
  apply LinearMap.ext
  intro x
  funext p
  have h (i : Fin 2) := AdaptedTotal.CM.adapted_inverse_basis_native_constant K D.ball D.places
    (FourSplittings.CM.newThetaSigns K v) (FourSplittings.CM.initialThetaSigns K v) A.basis
    (fun k p => x (if k = 0 then Sum.inl p else Sum.inr p)) z t i
  cases p with
  | inl p => exact congrFun (h 0) p
  | inr p => exact congrFun (h 1) p

theorem approximation_native_frame_transition_graph (z : HeckeCycles.GeometricSource.CM.BallChart)
    (hq : (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ ParameterHalfDet.CM.parameterGraphDomain K D)
    (x : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    approximationNativeFrameTransition K D A 0
        (AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.initialThetaSigns K v)
          (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (D.initialPeriods i).coordinates) (PeriodLimit.CM.initialTotalPeriod K D z) x)) =
      AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.newThetaSigns K v)
        (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (A.periods i).coordinates)
          (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z))
          (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator
            (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z)).matrix)⁻¹ *ᵥ
            (ParameterHalfDet.CM.parameterGraphBottom K D (ApproximationSequence.CM.newCompactPeriods K D A, z) *ᵥ x))) := by
  rw [approximation_native_frame_transition_constant K D A 0 z]
  change AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.newThetaSigns K v)
    ((CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm
      (AdaptedTotal.CM.totalNativePeriodFrame K D.ball D.places (FourSplittings.CM.initialThetaSigns K v) z
        (AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.initialThetaSigns K v)
          (TotalPeriodGraphs.CM.totalGraphInAmbient K _ (PeriodLimit.CM.initialTotalPeriod K D z) x)))) = _
  have hnat : AdaptedTotal.CM.totalNativePeriodFrame K D.ball D.places (FourSplittings.CM.initialThetaSigns K v) z
      (AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.initialThetaSigns K v)
        (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (D.initialPeriods i).coordinates) (PeriodLimit.CM.initialTotalPeriod K D z) x)) =
      TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (D.initialPeriods i).coordinates) (PeriodLimit.CM.initialTotalPeriod K D z) x := by
    exact AdaptedTotal.CM.total_native_frame_recovers_graph K D.initialPeriods z hq.1 x
  rw [hnat]
  let y := TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (D.initialPeriods i).coordinates) (PeriodLimit.CM.initialTotalPeriod K D z) x
  let J := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator
    (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z)).matrix
  let b := ParameterHalfDet.CM.parameterGraphBottom K D (ApproximationSequence.CM.newCompactPeriods K D A, z) *ᵥ x
  have hJ : J *ᵥ (J⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).denominator_det_isUnit _), Matrix.one_mulVec]
  have hgraph := MovingTotalPeriod.CM.approximation_total_graph K D A z (J⁻¹ *ᵥ b)
  dsimp only at hgraph
  change TotalPeriodGraphs.CM.totalGraphInAmbient K _ (MovingTotalPeriod.CM.approximationTotalPeriod K D A z) (J *ᵥ (J⁻¹ *ᵥ b)) = _ at hgraph
  rw [hJ] at hgraph
  have hp := TransportedGraphFrame.CM.approximation_projector_reference_graph K D A z hq x
  have he : (CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm (TotalProjector.CM.approximationProjector K D A z y) =
      TotalProjector.CM.totalSourceProjector K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z
        ((CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm y) := by
    change (CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm (CompactComplex.CM.complexTensorBasisEquiv K A.basis _) = _
    exact (CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm_apply_apply _
  calc
    _ = AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.newThetaSigns K v)
        (TotalProjector.CM.totalSourceProjector K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z
          ((CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm y)) :=
      (AdaptedTotal.CM.total_adapted_source_projector K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z _).symm
    _ = AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.newThetaSigns K v)
        ((CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm (TotalProjector.CM.approximationProjector K D A z y)) := by rw [he]
    _ = _ := by
      change AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.newThetaSigns K v)
        ((CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm (TotalProjector.CM.approximationProjector K D A z
          (TotalPeriodGraphs.CM.totalGraphInAmbient K _ (PeriodLimit.CM.initialTotalPeriod K D z) x))) = _
      rw [hp, hgraph]
      change AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.newThetaSigns K v)
        ((CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm (CompactComplex.CM.complexTensorBasisEquiv K A.basis _)) = _
      rw [LinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicFrameTransition.CM
