import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationCoefficientAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallTopFormInvariance
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSplitBallForms

/-! # Concrete Ball Invariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteBallInvariance.CM

noncomputable section

/-! One original finite input gives principal invariance of every actual
normalized split form and of its initial limit. The latter follows from
the proved compact smooth convergence, with no new automorphy premise. -/

open scoped Classical _root_.NumberField _root_.Manifold ContDiff _root_.Topology _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM Filter
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places))

theorem normalized_split_coefficient_tendsto (z : D.ball.Domain) :
    Tendsto (fun n => CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D φ n z.val) atTop
      (𝓝 (InitialTensor.CM.splitThetaTopCoefficient K (D.initialPeriods 0) (D.initialPeriods 1) φ z.val)) := by
  have hS : ({z.val} : Set HeckeCycles.GeometricSource.CM.BallChart) ⊆ D.ball.domain := by
    intro y hy
    exact (Set.mem_singleton_iff.mp hy) ▸ z.property
  have h := (CompactBallNeighborhood.CM.normalized_split_coefficient_uniform_derivatives K D φ 0 {z.val}
    isCompact_singleton hS).tendsto_at (Set.mem_singleton z.val)
  have hc := ((continuousMultilinearCurryFin0 ℝ HeckeCycles.GeometricSource.CM.BallChart ℂ).continuous.tendsto _).comp h
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply] using! hc

variable (hid : ∀ i, (v i).val 1 = true)
  (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : D.ball.principalLevel N g)
  (hcov : ConcreteApproximationLevel.CM.ActualApproximationThetaCovariant K D hid φ N g hg)

include hcov

theorem normalized_split_coefficient_covariant (n : ℕ) (z : D.ball.Domain) :
    CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D φ n (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) *
      LinearMap.det (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val).toLinearMap =
      CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D φ n z.val := by
  unfold CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient
  rw [mul_assoc]
  exact congrArg (fun c : ℂ => SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor K D (ApproximationSequence.CM.approximationSequence K D n) 0 * c)
    (ConcreteApproximationCoefficientAction.CM.approximation_source_coefficient_covariant K D (ApproximationSequence.CM.approximationSequence K D n) hid N g hg φ hcov z)

theorem initial_coefficient_covariant_of_approximation (z : D.ball.Domain) :
    InitialTensor.CM.splitThetaTopCoefficient K (D.initialPeriods 0) (D.initialPeriods 1) φ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) *
      LinearMap.det (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val).toLinearMap =
      InitialTensor.CM.splitThetaTopCoefficient K (D.initialPeriods 0) (D.initialPeriods 1) φ z.val := by
  have hl := (normalized_split_coefficient_tendsto K D φ (BallLineAction.CM.ballPrincipalAction K D.ball g hg.1 z)).mul_const
    (LinearMap.det (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val).toLinearMap)
  have hr := normalized_split_coefficient_tendsto K D φ z
  have he : (fun n => CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D φ n (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) *
      LinearMap.det (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val).toLinearMap) =
      (fun n => CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D φ n z.val) :=
    funext (fun n => normalized_split_coefficient_covariant K D φ hid N g hg hcov n z)
  change Tendsto (fun n => CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D φ n (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) *
    LinearMap.det (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val).toLinearMap) atTop _ at hl
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

theorem normalized_split_ball_form_invariant (n : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2)
    (hp : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2 0 form.val)
    (hf : ∀ (e : OpenPartialHomeomorph D.ball.Domain HeckeCycles.GeometricSource.CM.BallChart), e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain →
      ∀ z ∈ D.ball.domain, form.val.inChart e z (Pi.basisFun ℂ (Fin 2)) = CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D φ n z) :
    form.val.pullback (BallLineAction.CM.ballPrincipalAction K D.ball g hg.1) = form.val :=
  BallTopFormInvariance.CM.ball_top_pullback_of_coefficient K D.ball g hg.1 form hp (CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D φ n) hf
    (normalized_split_coefficient_covariant K D φ hid N g hg hcov n)

theorem initial_ball_form_invariant (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2)
    (hp : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2 0 form.val)
    (hf : ∀ (e : OpenPartialHomeomorph D.ball.Domain HeckeCycles.GeometricSource.CM.BallChart), e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain →
      ∀ z ∈ D.ball.domain, form.val.inChart e z (Pi.basisFun ℂ (Fin 2)) =
        InitialTensor.CM.splitThetaTopCoefficient K (D.initialPeriods 0) (D.initialPeriods 1) φ z) :
    form.val.pullback (BallLineAction.CM.ballPrincipalAction K D.ball g hg.1) = form.val :=
  BallTopFormInvariance.CM.ball_top_pullback_of_coefficient K D.ball g hg.1 form hp
    (InitialTensor.CM.splitThetaTopCoefficient K (D.initialPeriods 0) (D.initialPeriods 1) φ) hf
    (initial_coefficient_covariant_of_approximation K D φ hid N g hg hcov)

include hid

omit N g hg hcov φ in
theorem exists_actual_ball_theta_invariant_level (T : InitialSetup.CM.InitialBallTheta K D) :
    ∃ L : ℕ, 0 < L ∧ ∀ N : ℕ, L ∣ N →
      ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : D.ball.principalLevel N g),
        T.form.val.pullback (BallLineAction.CM.ballPrincipalAction K D.ball g hg.1) = T.form.val ∧
        ∀ (n : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2),
          Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2 0 form.val →
          (∀ (e : OpenPartialHomeomorph D.ball.Domain HeckeCycles.GeometricSource.CM.BallChart), e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain →
            ∀ z ∈ D.ball.domain, form.val.inChart e z (Pi.basisFun ℂ (Fin 2)) =
              CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D T.input n z) →
          form.val.pullback (BallLineAction.CM.ballPrincipalAction K D.ball g hg.1) = form.val := by
  have hlevel := ConcreteApproximationLevel.CM.exists_original_input_approximation_theta_level K D hid T.input
  refine ⟨hlevel.choose, hlevel.choose_spec.1, ?_⟩
  intro N hN g hg
  have hc := (hlevel.choose_spec.2 N hN g hg).2
  refine ⟨initial_ball_form_invariant K D T.input hid N g hg hc T.form T.pure T.coefficient, ?_⟩
  intro n form hp hf
  exact normalized_split_ball_form_invariant K D T.input hid N g hg hc n form hp hf

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteBallInvariance.CM
