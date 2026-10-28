import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GlobalPeriodComparison
import OAI.RepresentationTheory.Theta.Geometric.Period.TestDensity
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms

/-! # Period Tests -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.PeriodTests

noncomputable section

/-! A holomorphic map into an actual projective variety supplies a
period test with its exact point germ and its exact smooth-form comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open Filter
open scoped _root_.Topology _root_.Manifold ContDiff

theorem exists_projectivePeriodTest (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (c : Ω → X.analyticSpace)
    (hc : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) ∞ c) (x : Ω) :
    ∃ p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x.val) ⟶ X.toOver,
      (∀ᶠ y in 𝓝 x.val, ∀ hy : y ∈ Ω, Period.TestDensity.periodEvaluationPoint x.val y ≫ p = c ⟨y, hy⟩) ∧
      ∀ (form : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X.toOver) (u : LinearTheta.BallCoordinates),
        let : IsIntegral X.toOver.left := X.property
        let : Smooth X.toOver.hom := X.presentation.smooth
        let : X.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated X
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback c (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm X.toOver form)).val.inChart
            (chartAt LinearTheta.BallCoordinates x) x.val (fun _ => u) = DifferentialNaturality.formInPeriodCoordinates x.val p form u := by
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : X.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated X
  obtain ⟨U, hU, a, ha⟩ := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X.toOver (c x)
  have hxU : c x ∈ AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X.toOver U := by
    change c x ∈ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (U : Set X.toOver.left)
    rw [← AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap X.toOver U hU]
    exact ⟨a, ha⟩
  let y : AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodCharts.periodNeighborhood X.toOver U Ω c hc := ⟨x, hxU⟩
  exact ⟨AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodCharts.localPeriodTest X.toOver U hU Ω c hc y,
    AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodCharts.localPeriodTest_germ X.toOver U hU Ω c hc y,
    AlgebraicGeometry.HodgeConjecture.CMExtraction.GlobalPeriodComparison.globalPeriodTest_pullback X.toOver U hU Ω c hc y⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.PeriodTests
