import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactBallNeighborhood
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.InitialSetup
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PureTopCoefficient

/-! # Concrete Split Ball Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSplitBallForms.CM

noncomputable section

/-! ThetaCycle: actual smooth closed pure split theta forms, with the single
normalization per splitting and convergence in the full manifold C-infinity
topology. The finite input is the original fixed total Schwartz function. -/

open scoped Classical _root_.Manifold _root_.Topology ContDiff _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM Filter

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)

theorem exists_normalized_split_ball_forms
    (Φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (PeriodTotal.CM.TotalPositions K D.places)) :
    ∃ forms : ℕ → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2, ∀ n,
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2 0 (forms n).val ∧
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (forms n) = 0 ∧
      ∀ (e : OpenPartialHomeomorph D.ball.Domain HeckeCycles.GeometricSource.CM.BallChart), e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain →
        ∀ z ∈ D.ball.domain, (forms n).val.inChart e z (Pi.basisFun ℂ (Fin 2)) =
          CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D Φ n z := by
  have h (n : ℕ) := TotalBallForms.CM.exists_total_ball_top_form K ((ApproximationSequence.CM.approximationSequence K D n).periods 0)
    ((ApproximationSequence.CM.approximationSequence K D n).periods 1)
    (ApproximationCovariance.CM.approximationSplitFiniteInput K D (ApproximationSequence.CM.approximationSequence K D n) Φ)
  choose forms hp hc he using h
  let c := fun n => SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor K D (ApproximationSequence.CM.approximationSequence K D n) 0
  refine ⟨fun n => c n • forms n, fun n => ⟨(hp n).const_smul (c n), ?_, ?_⟩⟩
  · rw [map_smul, hc n, smul_zero]
  · intro e he' z hz
    change (c n • (forms n).val).inChart e z _ = _
    rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul]
    change c n * (forms n).val.inChart e z (Pi.basisFun ℂ (Fin 2)) = _
    rw [he n e he' z hz]
    rfl

theorem exists_actual_split_ball_forms_converging (T : InitialSetup.CM.InitialBallTheta K D) :
    ∃ forms : ℕ → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2,
      (∀ n, Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2 0 (forms n).val ∧
        Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (forms n) = 0 ∧
        ∀ (e : OpenPartialHomeomorph D.ball.Domain HeckeCycles.GeometricSource.CM.BallChart), e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain →
          ∀ z ∈ D.ball.domain, (forms n).val.inChart e z (Pi.basisFun ℂ (Fin 2)) =
            CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D T.input n z) ∧
      (let _ := SmoothTopology.CM.smoothFormTopology HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2
       Tendsto forms atTop (𝓝 T.form)) := by
  obtain ⟨forms, hf⟩ := exists_normalized_split_ball_forms K D T.input
  refine ⟨forms, hf, ?_⟩
  apply (SmoothConvergence.CM.tendsto_smooth_iff_compact_derivatives atTop forms T.form).mpr
  intro e m C hC
  let S : Set HeckeCycles.GeometricSource.CM.BallChart := Subtype.val '' C
  have hS : IsCompact S := hC.image continuous_subtype_val
  have htarget : e.val.target = D.ball.domain := by
    simpa only using! Analysis.DifferentialForms.Manifold.OpenEquivalence.openChart_target (U := D.ball.domainOpen) e.val e.property
  have hSB : S ⊆ D.ball.domain := by
    rintro z ⟨y, _, rfl⟩
    exact htarget ▸ y.property
  have hS_target : S ⊆ e.val.target := by simpa only [htarget] using hSB
  have hlim := PureTopCoefficient.CM.pure_top_chart_jet_convergence atTop forms T.form (fun n => (hf n).1) T.pure e
    (CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D T.input)
    (InitialTensor.CM.splitThetaTopCoefficient K (D.initialPeriods 0) (D.initialPeriods 1) T.input)
    (fun n z hz => (hf n).2.2 e e.property z (htarget ▸ hz))
    (fun z hz => T.coefficient e e.property z (htarget ▸ hz)) m S hS_target
    (CompactBallNeighborhood.CM.normalized_split_coefficient_uniform_derivatives K D T.input m S hS hSB)
  exact (hlim.comp Subtype.val).mono (fun y hy => ⟨y, hy, rfl⟩)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSplitBallForms.CM
