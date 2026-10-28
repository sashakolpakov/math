import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitFactorConstant

/-! # Compact Ball Neighborhood -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactBallNeighborhood.CM

noncomputable section

section

/-! ThetaCycle: every compact subset of the actual ball is contained in a
connected open neighborhood of the origin with compact closure inside
the ball. These domains fix the sign of the frame comparison uniformly. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

def ballEuclideanCoordinates : HeckeCycles.GeometricSource.CM.BallChart ≃L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => ℂ)).symm

theorem ball_euclidean_norm_square (z : HeckeCycles.GeometricSource.CM.BallChart) :
    ‖ballEuclideanCoordinates z‖ ^ 2 = Complex.normSq (z 0) + Complex.normSq (z 1) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  exact congrArg₂ (fun a b : ℝ => a + b) (Complex.normSq_eq_norm_sq (z 0)).symm
    (Complex.normSq_eq_norm_sq (z 1)).symm

theorem ball_domain_euclidean {K : IntermediateField ℚ ℂ}
    [NumberField K] [NumberField.IsCMField K] (B : HeckeCycles.GeometricSource.CM.BallDatum K) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    z ∈ B.domain ↔ ‖ballEuclideanCoordinates z‖ < Real.sqrt (-(B.b : ℂ).re) := by
  have hR : 0 < -(B.b : ℂ).re := neg_pos.mpr B.negative
  rw [← sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), Real.sq_sqrt hR.le,
    ball_euclidean_norm_square]
  rfl

theorem exists_compact_connected_ball_neighborhood {K : IntermediateField ℚ ℂ}
    [NumberField K] [NumberField.IsCMField K] (B : HeckeCycles.GeometricSource.CM.BallDatum K)
    (S : Set HeckeCycles.GeometricSource.CM.BallChart) (hS : IsCompact S) (hSB : S ⊆ B.domain) :
    ∃ U T : Set HeckeCycles.GeometricSource.CM.BallChart, IsOpen U ∧ IsPreconnected U ∧ 0 ∈ U ∧ S ⊆ U ∧ U ⊆ T ∧
      IsCompact T ∧ T ⊆ B.domain := by
  have hz : (0 : HeckeCycles.GeometricSource.CM.BallChart) ∈ B.domain := by simpa [HeckeCycles.GeometricSource.CM.BallDatum.domain] using B.negative
  have hSB' : insert 0 S ⊆ B.domain := Set.insert_subset hz hSB
  obtain ⟨x, hx, hmax⟩ := (hS.insert 0).exists_isMaxOn (Set.insert_nonempty 0 S)
    ballEuclideanCoordinates.continuous.norm.continuousOn
  let R := Real.sqrt (-(B.b : ℂ).re)
  have hxR : ‖ballEuclideanCoordinates x‖ < R := (ball_domain_euclidean B x).mp (hSB' hx)
  let r := (‖ballEuclideanCoordinates x‖ + R) / 2
  have hxr : ‖ballEuclideanCoordinates x‖ < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) hxr
  let U := ballEuclideanCoordinates ⁻¹' Metric.ball 0 r
  let T := ballEuclideanCoordinates ⁻¹' Metric.closedBall 0 r
  have hU : IsOpen U := Metric.isOpen_ball.preimage ballEuclideanCoordinates.continuous
  let f : HeckeCycles.GeometricSource.CM.BallChart →ₗ[ℝ] EuclideanSpace ℂ (Fin 2) :=
    ballEuclideanCoordinates.toLinearEquiv.toLinearMap.restrictScalars ℝ
  have hconv : Convex ℝ U := by
    exact (convex_ball (0 : EuclideanSpace ℂ (Fin 2)) r).linear_preimage f
  refine ⟨U, T, hU, hconv.isPreconnected, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [U, Set.mem_preimage, map_zero, Metric.mem_ball, dist_self] using hr
  · intro y hy
    have hymax : ‖ballEuclideanCoordinates y‖ ≤ ‖ballEuclideanCoordinates x‖ :=
      hmax (Set.mem_insert_of_mem 0 hy)
    simpa only [U, Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hymax.trans_lt hxr
  · exact Set.preimage_mono Metric.ball_subset_closedBall
  · exact ballEuclideanCoordinates.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall 0 r)
  · intro y hy
    apply (ball_domain_euclidean B y).mpr
    exact (show ‖ballEuclideanCoordinates y‖ ≤ r by simpa only [T, Set.mem_preimage,
      Metric.mem_closedBall, dist_zero_right] using hy).trans_lt hrR

end

/-! ThetaCycle: all compact real derivatives of the actual split theta top
coefficients converge after one scalar normalization per rational splitting.
The original total finite input remains fixed throughout the sequence. -/

open scoped Classical _root_.Matrix _root_.Topology ContDiff _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM Filter

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)
  (Φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (PeriodTotal.CM.TotalPositions K D.places))

def normalizedSplitThetaCoefficient (n : ℕ) (z : HeckeCycles.GeometricSource.CM.BallChart) : ℂ :=
  SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor K D (ApproximationSequence.CM.approximationSequence K D n) 0 *
    InitialTensor.CM.splitThetaTopCoefficient K ((ApproximationSequence.CM.approximationSequence K D n).periods 0)
      ((ApproximationSequence.CM.approximationSequence K D n).periods 1)
      (ApproximationCovariance.CM.approximationSplitFiniteInput K D (ApproximationSequence.CM.approximationSequence K D n) Φ) z

theorem eventually_normalized_split_coefficient_locally_eq
    (S : Set HeckeCycles.GeometricSource.CM.BallChart) (hS : IsCompact S) (hSB : S ⊆ D.ball.domain) :
    ∀ᶠ n in atTop, ∀ z ∈ S,
      normalizedSplitThetaCoefficient K D Φ n =ᶠ[𝓝 z]
        ApproximationCoefficient.CM.approximationProjectedCoefficient K D Φ (ApproximationSequence.CM.approximationSequence K D n) := by
  obtain ⟨U, T, hU, hc, hz₀, hSU, hUT, hT, hTB⟩ :=
    exists_compact_connected_ball_neighborhood D.ball S hS hSB
  have htube := CompactFiber.CM.eventually_compact_fiber_mem
    (fun n => ApproximationSequence.CM.newCompactPeriods K D (ApproximationSequence.CM.approximationSequence K D n)) (ApproximationSequence.CM.oldCompactPeriods K D)
    (ApproximationSequence.CM.sequence_compact_periods_tendsto K D) T hT (ParameterHalfDet.CM.parameterHalfDetDomain K D)
    (ParameterHalfDet.CM.parameter_half_det_domain_open K D) (fun z hz => ParameterHalfDet.CM.parameter_half_det_domain_original K D z (hTB hz))
  filter_upwards [htube] with n hn
  intro z hz
  have hconst := SplitFactorConstant.CM.approximation_split_factor_constant K D (ApproximationSequence.CM.approximationSequence K D n) hc
    (fun y hy => hn y (hUT hy)) 0 hz₀
  filter_upwards [hU.mem_nhds (hSU hz)] with y hy
  rw [SplitCoefficientCovariance.CM.approximation_split_coefficient_covariance, hconst y hy]
  rfl

theorem normalized_split_coefficient_uniform_derivatives (m : ℕ)
    (S : Set HeckeCycles.GeometricSource.CM.BallChart) (hS : IsCompact S) (hSB : S ⊆ D.ball.domain) :
    TendstoUniformlyOn
      (fun n z => iteratedFDeriv ℝ m (normalizedSplitThetaCoefficient K D Φ n) z)
      (fun z => iteratedFDeriv ℝ m
        (InitialTensor.CM.splitThetaTopCoefficient K (D.initialPeriods 0) (D.initialPeriods 1) Φ) z) atTop S := by
  have hlim := ApproximationCoefficient.CM.approximation_projected_coefficient_uniform_derivatives K D Φ m S hS hSB
  have he := eventually_normalized_split_coefficient_locally_eq K D Φ S hS hSB
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  filter_upwards [hlim ε hε, he] with n hn hen
  intro z hz
  rw [((hen z hz).iteratedFDeriv ℝ m).self_of_nhds]
  exact hn z hz

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactBallNeighborhood.CM
