import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FrameTransitionDeterminant

/-! # Split Factor Constant -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitFactorConstant.CM

noncomputable section

/-! ThetaCycle: the exact split-coefficient scalar is holomorphic and constant
on every connected comparison domain. No equality of geometric and
oscillator frames is assumed. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)

theorem approximation_theta_multiplier_holomorphic :
    DifferentiableOn ℂ (ApproximationCovariance.CM.approximationThetaMultiplier K D A) D.ball.domain := by
  let : Nonempty (PeriodTotal.CM.TotalPositions K D.places) := ⟨Sum.inl (D.places.distinguished, 0)⟩
  exact IndexedCovariance.CM.indexed_theta_multiplier_holomorphic (PeriodTotal.CM.approximationSymplecticMatrix K D A)⁻¹
    (MovingTotalPeriod.CM.approximationTotalPeriod K D A) (MovingTotalPeriod.CM.approximation_total_period_holomorphic K D A)

theorem approximation_split_factor_ne_zero (z : HeckeCycles.GeometricSource.CM.BallChart)
    (hq : (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ ParameterHalfDet.CM.parameterHalfDetDomain K D) :
    SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor K D A z ≠ 0 :=
  div_ne_zero (mul_ne_zero (ParameterHalfDet.CM.parameter_half_det_ne_zero K D _ hq)
    (GraphSlotTransition.CM.approximation_multiplicity_matrix_det_ne_zero K D A))
    (mul_ne_zero (mul_ne_zero (ApproximationCovariance.CM.approximation_theta_multiplier_ne_zero K D A z) (Units.ne_zero _))
      (Units.ne_zero _))

theorem approximation_split_factor_holomorphic {s : Set HeckeCycles.GeometricSource.CM.BallChart}
    (hs : ∀ z ∈ s, (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ ParameterHalfDet.CM.parameterHalfDetDomain K D) :
    DifferentiableOn ℂ (SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor K D A) s := by
  have hB : s ⊆ D.ball.domain := fun z hz => (hs z hz).1.1
  have hp : DifferentiableOn ℂ
      (fun z => ParameterHalfDet.CM.parameterHalfDet K D (ApproximationSequence.CM.newCompactPeriods K D A, z)) s :=
    (ParameterHalfDet.CM.parameter_half_det_holomorphic K D).comp
      ((differentiableOn_const _).prodMk differentiableOn_id) hs
  have hm := (approximation_theta_multiplier_holomorphic K D A).mono hB
  have hd₀ := (A.periods 0).halfDet_holomorphic.mono hB
  have hd₁ := (A.periods 1).halfDet_holomorphic.mono hB
  have hn : ∀ z ∈ s, ApproximationCovariance.CM.approximationThetaMultiplier K D A z *
      ((A.periods 0).halfDet z : ℂ) * ((A.periods 1).halfDet z : ℂ) ≠ 0 :=
    fun z _ => mul_ne_zero (mul_ne_zero (ApproximationCovariance.CM.approximation_theta_multiplier_ne_zero K D A z)
      (Units.ne_zero _)) (Units.ne_zero _)
  simpa only [SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply]
    using! (hp.mul (differentiableOn_const _)).mul (((hm.mul hd₀).mul hd₁).inv hn)

theorem approximation_split_factor_constant {s : Set HeckeCycles.GeometricSource.CM.BallChart} (hconn : IsPreconnected s)
    (hs : ∀ z ∈ s, (ApproximationSequence.CM.newCompactPeriods K D A, z) ∈ ParameterHalfDet.CM.parameterHalfDetDomain K D)
    (z₀ : HeckeCycles.GeometricSource.CM.BallChart) (hz₀ : z₀ ∈ s) :
    ∀ z ∈ s, SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor K D A z =
      SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor K D A z₀ := by
  have hdet := FrameTransitionDeterminant.CM.approximation_native_frame_transition_det_ne_zero K D A z₀ (hs z₀ hz₀).1
  have hsq : Set.EqOn ((SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor K D A) ^ 2)
      ((fun _ : HeckeCycles.GeometricSource.CM.BallChart => SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor K D A z₀) ^ 2) s := by
    intro z hz
    exact mul_right_cancel₀ hdet ((FrameTransitionDeterminant.CM.approximation_split_factor_square K D A z (hs z hz)).trans
      (FrameTransitionDeterminant.CM.approximation_split_factor_square K D A z₀ (hs z₀ hz₀)).symm)
  exact hconn.eq_of_sq_eq (approximation_split_factor_holomorphic K D A hs).continuousOn
    continuousOn_const hsq (fun {_} _ => approximation_split_factor_ne_zero K D A z₀ (hs z₀ hz₀)) hz₀ rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitFactorConstant.CM
