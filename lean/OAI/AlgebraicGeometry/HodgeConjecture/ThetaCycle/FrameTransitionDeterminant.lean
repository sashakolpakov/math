import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicFrameTransition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitCoefficientCovariance

/-! # Frame Transition Determinant -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FrameTransitionDeterminant.CM

noncomputable section

/-! ThetaCycle: the determinant of the constant native-frame transition
identifies the squares of the geometric and oscillator scalar factors. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)

theorem approximation_native_frame_transition_det (z : HeckeCycles.GeometricSource.CM.BallChart)
    (hq : (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ ParameterHalfDet.CM.parameterGraphDomain K D) :
    LinearMap.det (IntrinsicFrameTransition.CM.approximationNativeFrameTransition K D A 0) *
        (((D.initialPeriods 0).halfDet z : ℂ) * ((D.initialPeriods 1).halfDet z : ℂ)) ^ 2 =
      (((A.periods 0).halfDet z : ℂ) * ((A.periods 1).halfDet z : ℂ)) ^ 2 *
        ApproximationCovariance.CM.approximationThetaMultiplier K D A z ^ 2 * (ParameterHalfDet.CM.parameterGraphBottom K D (ApproximationSequence.CM.newCompactPeriods K D A, z)).det := by
  let G₀ := (AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.initialThetaSigns K v)).comp
    (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (D.initialPeriods i).coordinates) (PeriodLimit.CM.initialTotalPeriod K D z))
  let G₁ := (AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.newThetaSigns K v)).comp
    (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (A.periods i).coordinates)
      (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z)))
  let J := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator
    (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z)).matrix
  have he : (IntrinsicFrameTransition.CM.approximationNativeFrameTransition K D A 0).comp G₀ =
      (G₁.comp (Matrix.toLin' J⁻¹)).comp
        (Matrix.toLin' (ParameterHalfDet.CM.parameterGraphBottom K D (ApproximationSequence.CM.newCompactPeriods K D A, z))) := by
    apply LinearMap.ext
    intro x
    exact IntrinsicFrameTransition.CM.approximation_native_frame_transition_graph K D A z hq x
  have h := congrArg LinearMap.det he
  rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_comp,
    LinearMap.det_toLin', LinearMap.det_toLin', Matrix.det_nonsing_inv, Ring.inverse_eq_inv] at h
  have h₀ : LinearMap.det G₀ =
      (((D.initialPeriods 0).halfDet z : ℂ) * ((D.initialPeriods 1).halfDet z : ℂ)) ^ 2 :=
    AdaptedTotal.CM.total_adapted_graph_det K D.initialPeriods z hq.1
  have h₁ : LinearMap.det G₁ =
      (((A.periods 0).halfDet z : ℂ) * ((A.periods 1).halfDet z : ℂ)) ^ 2 :=
    AdaptedTotal.CM.total_adapted_graph_det K A.periods z hq.1
  rw [h₀, h₁] at h
  rw [ApproximationCovariance.CM.approximation_theta_multiplier_square]
  exact h

theorem approximation_native_frame_transition_det_ne_zero (z : HeckeCycles.GeometricSource.CM.BallChart)
    (hq : (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ ParameterHalfDet.CM.parameterGraphDomain K D) :
    LinearMap.det (IntrinsicFrameTransition.CM.approximationNativeFrameTransition K D A 0) ≠ 0 := by
  have h := approximation_native_frame_transition_det K D A z hq
  have hr : (((A.periods 0).halfDet z : ℂ) * ((A.periods 1).halfDet z : ℂ)) ^ 2 *
      ApproximationCovariance.CM.approximationThetaMultiplier K D A z ^ 2 * (ParameterHalfDet.CM.parameterGraphBottom K D (ApproximationSequence.CM.newCompactPeriods K D A, z)).det ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)))
      (pow_ne_zero _ (ApproximationCovariance.CM.approximation_theta_multiplier_ne_zero K D A z))) hq.2
  rw [← h] at hr
  exact (mul_ne_zero_iff.mp hr).1

theorem approximation_split_factor_square (z : HeckeCycles.GeometricSource.CM.BallChart)
    (hq : (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ ParameterHalfDet.CM.parameterHalfDetDomain K D) :
    SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor K D A z ^ 2 *
        LinearMap.det (IntrinsicFrameTransition.CM.approximationNativeFrameTransition K D A 0) =
      (GraphSlotTransition.CM.approximationMultiplicityMatrix K D A).det ^ 2 := by
  have h := approximation_native_frame_transition_det K D A z hq.1
  unfold SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor
  rw [div_pow, mul_pow, ParameterHalfDet.CM.parameter_half_det_square]
  field_simp [ApproximationCovariance.CM.approximation_theta_multiplier_ne_zero K D A z, Units.ne_zero, hq.1.2]
  linear_combination (GraphSlotTransition.CM.approximationMultiplicityMatrix K D A).det ^ 2 * h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FrameTransitionDeterminant.CM
