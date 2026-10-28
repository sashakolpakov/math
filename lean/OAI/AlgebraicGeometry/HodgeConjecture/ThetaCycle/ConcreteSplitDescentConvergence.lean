import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSplitBallForms
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverChartSections

/-! # Concrete Split Descent Convergence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSplitDescentConvergence.CM

noncomputable section

section

/-! ThetaCycle: the actual normalized split forms have the local smooth
parameter formulas required for convergence after common-cover descent. -/

open Set Filter OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open scoped Classical _root_.Manifold ContDiff _root_.Topology _root_.Matrix.Norms.Elementwise

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) (T : InitialSetup.CM.InitialBallTheta K D)

def parameterBallTopCovector (q : ParameterProjectorAnalytic.CM.CompactParameters K D.places) (z : HeckeCycles.GeometricSource.CM.BallChart) : Analysis.DifferentialForms.Manifold.Basic.FormValue HeckeCycles.GeometricSource.CM.BallChart 2 :=
  PureTopCoefficient.CM.ballAreaCoefficient (ProjectedCoefficient.CM.parameterProjectedCoefficient K D T.input (q, z))

theorem normalized_split_forms_local_parameters
    (forms : ℕ → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2)
    (hpure : ∀ n, Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2 0 (forms n).val)
    (hcoeff : ∀ n (e : SmoothTopology.CM.SmoothAtlasChart HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain) z,
      z ∈ D.ball.domain → (forms n).val.inChart e.val z (Pi.basisFun ℂ (Fin 2)) =
        CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D T.input n z)
    (e : SmoothTopology.CM.SmoothAtlasChart HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain) (x : HeckeCycles.GeometricSource.CM.BallChart) (hx : x ∈ e.val.target) :
    ∃ U : Set HeckeCycles.GeometricSource.CM.BallChart, IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, ContDiffAt ℝ ∞ (Function.uncurry (parameterBallTopCovector K D T))
        (ApproximationSequence.CM.oldCompactPeriods K D, y)) ∧
      (∀ᶠ n in atTop, ∀ y ∈ U, (forms n).val.inChart e.val y =
        parameterBallTopCovector K D T (ApproximationSequence.CM.newCompactPeriods K D (ApproximationSequence.CM.approximationSequence K D n)) y) ∧
      (∀ y ∈ U, T.form.val.inChart e.val y = parameterBallTopCovector K D T (ApproximationSequence.CM.oldCompactPeriods K D) y) := by
  have htarget : e.val.target = D.ball.domain := by
    simpa only using! Analysis.DifferentialForms.Manifold.OpenEquivalence.openChart_target (U := D.ball.domainOpen) e.val e.property
  have hxB : x ∈ D.ball.domain := htarget ▸ hx
  obtain ⟨U, C, hU, _, _, hxU, hUC, hC, hCB⟩ :=
    CompactBallNeighborhood.CM.exists_compact_connected_ball_neighborhood D.ball {x} isCompact_singleton (singleton_subset_iff.mpr hxB)
  have hUB : U ⊆ D.ball.domain := hUC.trans hCB
  have hn := CompactBallNeighborhood.CM.eventually_normalized_split_coefficient_locally_eq K D T.input C hC hCB
  have htube := CompactFiber.CM.eventually_compact_fiber_mem
    (fun n => ApproximationSequence.CM.newCompactPeriods K D (ApproximationSequence.CM.approximationSequence K D n)) (ApproximationSequence.CM.oldCompactPeriods K D)
    (ApproximationSequence.CM.sequence_compact_periods_tendsto K D) C hC (ParameterHalfDet.CM.parameterGraphDomain K D)
    (ParameterHalfDet.CM.parameter_graph_domain_open K D) (fun y hy => ParameterHalfDet.CM.parameter_graph_domain_original K D y (hCB hy))
  refine ⟨U, hU, hxU (mem_singleton x), ?_, ?_, ?_⟩
  · intro y hy
    exact PureTopCoefficient.CM.ballAreaCoefficient.contDiff.contDiffAt.comp (ApproximationSequence.CM.oldCompactPeriods K D, y)
      (ProjectedCoefficient.CM.parameter_projected_coefficient_smoothAt_original K D T.input y (hUB hy))
  · filter_upwards [hn, htube] with n hnorm hgraph
    intro y hy
    have hyt : y ∈ e.val.target := htarget.symm ▸ hUB hy
    rw [PureTopCoefficient.CM.pure_top_chart_from_coefficient (forms n) (hpure n) e y hyt,
      hcoeff n e y (hUB hy), (hnorm y (hUC hy)).eq_of_nhds,
      ← ApproximationCoefficient.CM.parameter_projected_coefficient_approximation K D T.input (ApproximationSequence.CM.approximationSequence K D n) y
        (hgraph y (hUC hy))]
    rfl
  · intro y hy
    have hyt : y ∈ e.val.target := htarget.symm ▸ hUB hy
    rw [PureTopCoefficient.CM.pure_top_chart_from_coefficient T.form T.pure e y hyt,
      T.coefficient e e.property y (hUB hy),
      ← ProjectedCoefficient.CM.parameter_projected_coefficient_original K D T.input y (hUB hy)]
    rfl

end

/-! ThetaCycle: actual normalized split theta forms converge in the full
smooth topology after descent to any one common principal ball surface. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM Filter
open scoped Classical _root_.Manifold ContDiff _root_.Topology _root_.Matrix.Norms.Elementwise

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) (T : InitialSetup.CM.InitialBallTheta K D)

theorem actual_normalized_split_descents_converge
    (forms : ℕ → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2)
    (hpure : ∀ n, Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2 0 (forms n).val)
    (hcoeff : ∀ n (e : SmoothTopology.CM.SmoothAtlasChart HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain) z,
      z ∈ D.ball.domain → (forms n).val.inChart e.val z (Pi.basisFun ℂ (Fin 2)) =
        CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D T.input n z)
    (N : ℕ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : D.ball.Domain → X.analyticSpace)
    (hπ : D.ball.IsBallCover N X π)
    (descents : ℕ → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm X.analyticModel X.analyticSpace 2)
    (initial : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm X.analyticModel X.analyticSpace 2)
    (hdesc : ∀ n, CoverPullback.CM.ballCoverPullback K D.ball N X π hπ 2 (descents n) = forms n)
    (hinitial : CoverPullback.CM.ballCoverPullback K D.ball N X π hπ 2 initial = T.form) :
    let _ := SmoothTopology.CM.smoothFormTopology X.analyticModel X.analyticSpace 2
    Tendsto descents atTop (𝓝 initial) := by
  apply CoverChartSections.CM.parametric_cover_forms_converge π hπ.2.1
    (CoverLocalM.CM.ball_cover_real_local_diffeomorph K D.ball N X π hπ)
    (fun n => ApproximationSequence.CM.newCompactPeriods K D (ApproximationSequence.CM.approximationSequence K D n)) (ApproximationSequence.CM.oldCompactPeriods K D)
    (ApproximationSequence.CM.sequence_compact_periods_tendsto K D) 2 descents initial
  intro e x hx
  obtain ⟨U, hU, hxU, hg, hn, h₀⟩ :=
    normalized_split_forms_local_parameters K D T forms hpure hcoeff e x hx
  refine ⟨U, hU, hxU, parameterBallTopCovector K D T, hg, ?_, ?_⟩
  · filter_upwards [hn] with n hnorm
    intro y hy
    have he : (descents n).val.pullback (E := HeckeCycles.GeometricSource.CM.BallChart) π = (forms n).val :=
      congrArg Subtype.val (hdesc n)
    rw [he]
    exact hnorm y hy
  · intro y hy
    have he : initial.val.pullback (E := HeckeCycles.GeometricSource.CM.BallChart) π = T.form.val :=
      congrArg Subtype.val hinitial
    rw [he]
    exact h₀ y hy

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSplitDescentConvergence.CM
