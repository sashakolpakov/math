import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GlobalPeriodComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold

/-! # Period Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms

noncomputable section

/-! GeometricTheta's canonical period covectors are the actual pullback of the closed native theta forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open Filter
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def thetaOnPeriodVariety (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (j : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) :
    D.sphericalInputs →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm X.analyticModel X.analyticSpace 1 := by
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : X.toOver.left.IsSeparated := IntrinsicForms.integralProjective_separated X
  exact (KaehlerGluing.globalSmoothForm X.toOver).comp
    ((AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)).comp
      ((D.pel.albanesePullback hg).comp Θ))

theorem thetaOnPeriodVariety_closed (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (j : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) (φ : D.sphericalInputs) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (thetaOnPeriodVariety D hg Θ j X component φ) = 0 :=
  ClosedForms.projectiveKaehlerForm_closed X _

theorem thetaOnPeriodVariety_native (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (j : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) (φ : D.sphericalInputs) :
    thetaOnPeriodVariety D hg Θ j X component φ =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
        (show X.toOver ⟶ (D.componentVariety hg j).toOver from component.hom))
        (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map
          (V := X) (W := D.componentVariety hg j) component.hom ∞)
        (IntrinsicForms.thetaSmoothComponent D hg Θ j φ) := by
  let V := D.componentVariety hg j
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : X.toOver.left.IsSeparated := IntrinsicForms.integralProjective_separated X
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : V.toOver.left.IsSeparated := IntrinsicForms.integralProjective_separated V
  let f : X.toOver ⟶ V.toOver := component.hom
  let : IsIso f := inferInstanceAs (IsIso component.hom)
  let : IsIso f.left := inferInstanceAs (IsIso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map f))
  let form := D.pel.albanesePullback hg (Θ φ)
  have he := congrArg (KaehlerGluing.globalSmoothForm X.toOver)
    (congrArg (fun L => L form) (AbelianScheme.TateComparison.FormConstants.formsPullback_comp component.hom (D.componentComplexInclusion j)))
  exact he.trans (KaehlerNaturality.globalSmoothForm_pullback f
    (AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion j) form))

theorem thetaOnPeriodVariety_covector (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (j : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)
    (hΘ : D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ)
    (φ : D.sphericalInputs) (x : D.domain) (u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) :
    let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback cover (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
      (thetaOnPeriodVariety D hg Θ j X component φ)).val.inChart
        (chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x) x.val (fun _ => u) = D.thetaUniversal φ.val x.val u := by
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : X.toOver.left.IsSeparated := IntrinsicForms.integralProjective_separated X
  let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
  obtain ⟨U, hU, a, ha⟩ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X.toOver (cover x)
  have hxU : cover x ∈ Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X.toOver U := by
    change cover x ∈ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (U : Set X.toOver.left)
    rw [← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap X.toOver U hU]
    exact ⟨a, ha⟩
  let y : PeriodCharts.periodNeighborhood X.toOver U D.domain cover hc := ⟨x, hxU⟩
  let p := PeriodCharts.localPeriodTest X.toOver U hU D.domain cover hc y
  let m := component.hom ≫ D.componentComplexInclusion j
  have hp : D.IsPeriodChartAt (D.totalPeriodMap j X component cover) x (p ≫ m) := by
    have h := PeriodCharts.localPeriodTest_germ X.toOver U hU D.domain cover hc y
    filter_upwards [h] with z hz
    intro hzD
    exact (Category.assoc _ p m).symm.trans (congrArg (· ≫ m) (hz hzD))
  have hperiod := congrArg (fun L : RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent => L u) (hΘ.2.1 φ x (p ≫ m) hp)
  exact (GlobalPeriodComparison.globalPeriodTest_pullback X.toOver U hU D.domain cover hc y
    (AbelianScheme.TateComparison.FormConstants.formsPullback m (D.pel.albanesePullback hg (Θ φ))) u).trans hperiod

/-- The component chosen by GeometricTheta carries the very same integration-defined
Betti class as the native component, transported by its actual scheme isomorphism. -/
theorem thetaOnPeriodVariety_betti (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (j : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) (φ : D.sphericalInputs) :
    KaehlerClasses.Intrinsic.kaehlerBettiClass X
      (AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
        (D.pel.albanesePullback hg (Θ φ))) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 component.hom
        (ClosedForms.thetaBettiComponent D hg Θ j φ) := by
  let V := D.componentVariety hg j
  let f : X.toOver ⟶ V.toOver := component.hom
  let : IsIso f := inferInstanceAs (IsIso component.hom)
  let : IsIso f.left := inferInstanceAs (IsIso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map f))
  let form := D.pel.albanesePullback hg (Θ φ)
  have he := congrArg (KaehlerClasses.Intrinsic.kaehlerBettiClass X)
    (congrArg (fun L => L form) (AbelianScheme.TateComparison.FormConstants.formsPullback_comp component.hom (D.componentComplexInclusion j)))
  exact he.trans (KaehlerClasses.Intrinsic.kaehlerBettiClass_pullback f
    (AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion j) form))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms
