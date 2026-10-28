import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodCharts
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodSmoothComparison
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormNaturality
import OAI.Analysis.DifferentialForms.Manifold.Holomorphic

/-! # Period Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodPullback

noncomputable section

/-! The directly constructed period test computes the actual smooth pullback on its neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.Analysis.DifferentialForms.Manifold.Holomorphic OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormNaturality
open scoped _root_.Manifold ContDiff

attribute [local instance] Comparison.Betti.Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (U : X.left.Opens) (hU : IsAffineOpen U)
  (Ω : Opens RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (c : Ω → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  (hc : ContMDiff 𝓘(ℂ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) 𝓘(ℂ, Comparison.Betti.RegularSmoothness.NativeModel X) ∞ c)

def periodSectionEvaluation : Γ(X.left, U) →ₐ[ℂ] C(PeriodCharts.periodNeighborhood X U Ω c hc, ℂ) :=
  (ContinuousMap.compRightAlgHom ℂ ℂ
    ⟨PeriodCharts.periodNeighborhoodMap X U Ω c hc, (PeriodCharts.periodNeighborhoodMap_smooth X U Ω c hc).continuous⟩).comp
      (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U)

theorem periodSectionEvaluation_smoothC (a : Γ(X.left, U)) :
    ContMDiff 𝓘(ℂ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) 𝓘(ℂ, ℂ) ∞ (periodSectionEvaluation X U Ω c hc a) :=
  (HolomorphicSections.Kaehler.sectionEvaluationOn_holomorphic X U a).comp
    (PeriodCharts.periodNeighborhoodMap_smooth X U Ω c hc)

theorem periodSectionEvaluation_smooth (a : Γ(X.left, U)) :
    ContMDiff 𝓘(ℝ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) 𝓘(ℝ, ℂ) ∞ (periodSectionEvaluation X U Ω c hc a) :=
  Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (periodSectionEvaluation_smoothC X U Ω c hc a)

theorem localPeriodTest_smooth_pullback (x : PeriodCharts.periodNeighborhood X U Ω c hc)
    (form : AbelianScheme.TateComparison.FormConstants.OneForms X) (u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) :
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (PeriodCharts.periodNeighborhoodMap X U Ω c hc)
      (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (PeriodCharts.periodNeighborhoodMap_smooth X U Ω c hc))
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1
        (Kaehler.affineSmoothForm X U hU form))).val.inChart
          (chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x) x.val.val (fun _ => u) =
      RepresentationTheory.Theta.Geometric.DifferentialNaturality.formInPeriodCoordinates x.val.val (PeriodCharts.localPeriodTest X U hU Ω c hc x) form u := by
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  let φ := periodSectionEvaluation X U Ω c hc
  let hr := periodSectionEvaluation_smooth X U Ω c hc
  let hC := periodSectionEvaluation_smoothC X U Ω c hc
  let e := chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x
  have he : e ∈ atlas RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates (PeriodCharts.periodNeighborhood X U Ω c hc) := chart_mem_atlas _ x
  have hx : x.val.val ∈ e.target := e.map_source (mem_chart_source _ x)
  have hopen : Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1
      (Kaehler.affineSmoothForm X U hU form) =
    Comparison.Betti.Smooth.FormRealization.oneFormMap (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U)
      (Kaehler.affineForm X U hU form) := by
    change (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1)
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1).symm
        (Comparison.Betti.Smooth.CochainMap.smoothFormMap (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U) 1
          (Kaehler.affineForm X U hU form))) = _
    rw [LinearEquiv.apply_symm_apply, Comparison.Betti.Smooth.CochainMap.smoothFormMap_one]
  have hn := Comparison.Betti.Smooth.FormNaturality.oneFormMap_naturality φ hr
    (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U) (AlgHom.id ℂ A)
    (PeriodCharts.periodNeighborhoodMap X U Ω c hc)
    (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (PeriodCharts.periodNeighborhoodMap_smooth X U Ω c hc))
    (fun _ _ => rfl) (Kaehler.affineForm X U hU form)
  have hid : Comparison.Betti.Algebraic.Forms.pullback (AlgHom.id ℂ A) 1 (Kaehler.affineForm X U hU form) =
      Kaehler.affineForm X U hU form :=
    congrArg (fun f : Comparison.Betti.Algebraic.Forms.Form A 1 →ₗ[ℂ] Comparison.Betti.Algebraic.Forms.Form A 1 =>
      f (Kaehler.affineForm X U hU form)) (Comparison.Betti.Algebraic.Forms.pullback_id (A := A) 1)
  have hn' := (congrArg (Comparison.Betti.Smooth.FormRealization.oneFormMap φ hr) hid).symm.trans hn
  have hEq := (congrArg (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (PeriodCharts.periodNeighborhoodMap X U Ω c hc)
    (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (PeriodCharts.periodNeighborhoodMap_smooth X U Ω c hc))) hopen).trans hn'.symm
  refine (congrArg (fun a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates (PeriodCharts.periodNeighborhood X U Ω c hc) 1 =>
    a.val.inChart (chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x) x.val.val (fun _ => u)) hEq).trans ?_
  let w := form.val A (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU)
  have hs := PeriodSmoothComparison.smoothKaehler_inChart A φ hr hC e he x.val.val hx w u
  have hHom : PeriodSmoothComparison.coordinateFunctionHom A φ hC e he x.val.val hx =
      PeriodFamilies.coordinateFamilyHom A x.val.val (PeriodCharts.affineCoordinateFamily X U hU Ω c hc x)
        (PeriodCharts.affineCoordinateFamily_differentiable X U hU Ω c hc x) := by
    ext a y
    exact (AffineEvaluation.Kaehler.affineOpenCharacter_evaluation X U hU _ a).symm
  have hd := congrArg (fun f : A →ₐ[ℂ] RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x.val.val =>
    RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential x.val.val (AbelianScheme.TateComparison.FormConstants.differentialMap (CommAlgCat.ofHom f) w) u) hHom
  have ht := congrArg (fun L : RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent => L u)
    (PeriodFamilies.familyTest_differential A x.val.val (PeriodCharts.affineCoordinateFamily X U hU Ω c hc x)
      (PeriodCharts.affineCoordinateFamily_differentiable X U hU Ω c hc x)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) form)
  exact hs.trans (hd.trans ht.symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodPullback
