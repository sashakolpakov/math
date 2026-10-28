import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodPullback
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OpenPurity

/-! # Global Period Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GlobalPeriodComparison

noncomputable section

/-! Global smooth forms and the directly constructed local period tests have the same pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [X.left.IsSeparated]
  (U : X.left.Opens) (hU : IsAffineOpen U)
  (Ω : Opens RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (c : Ω → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  (hc : ContMDiff 𝓘(ℂ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) 𝓘(ℂ, Comparison.Betti.RegularSmoothness.NativeModel X) ∞ c)

theorem globalPeriodTest_pullback (x : PeriodCharts.periodNeighborhood X U Ω c hc)
    (form : AbelianScheme.TateComparison.FormConstants.OneForms X) (u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) :
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback c (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
      (KaehlerGluing.globalSmoothForm X form)).val.inChart
        (chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x.val) x.val.val (fun _ => u) =
      RepresentationTheory.Theta.Geometric.DifferentialNaturality.formInPeriodCoordinates x.val.val (PeriodCharts.localPeriodTest X U hU Ω c hc x) form u := by
  let α := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback c (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
    (KaehlerGluing.globalSmoothForm X form)
  have heq : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (PeriodCharts.periodNeighborhoodMap X U Ω c hc)
      (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (PeriodCharts.periodNeighborhoodMap_smooth X U Ω c hc))
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1
        (Kaehler.affineSmoothForm X U hU form)) =
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates (PeriodCharts.periodNeighborhood X U Ω c hc) 1
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (PeriodCharts.periodNeighborhood X U Ω c hc) α) := by
    rw [← KaehlerGluing.globalSmoothForm_onAffine X form U hU,
      Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_onOpen, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_onOpen]
    change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback _ _ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback _ _ _) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback _ _ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback _ _ _)
    rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp, ← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp]
    rfl
  have h := PeriodPullback.localPeriodTest_smooth_pullback X U hU Ω c hc x form u
  rw [heq] at h
  have hi := OpenPurity.Kaehler.onOpen_intrinsic_chart (PeriodCharts.periodNeighborhood X U Ω c hc) 1 α x
  exact (congrArg (fun f => f (fun _ => u)) hi).symm.trans h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GlobalPeriodComparison
