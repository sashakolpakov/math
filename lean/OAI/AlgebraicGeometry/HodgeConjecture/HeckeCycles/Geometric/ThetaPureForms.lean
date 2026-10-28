import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KaehlerPureRepresentative
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms

/-! # Theta Pure Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaPureForms.CM

noncomputable section

/-! Actual pure closed forms and rational-complexified classes of the
canonical GeometricTheta lift on its chosen projective component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
  (j : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (component : X.toOver ≅ D.componentComplex j)

def algebraic : D.sphericalInputs →ₗ[ℂ] AbelianScheme.TateComparison.FormConstants.OneForms X.toOver :=
  (AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)).comp
    ((D.pel.albanesePullback hg).comp Θ)

def representative : D.sphericalInputs →ₗ[ℂ]
    AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0 :=
  (KaehlerPureRepresentative.CM.pure X).comp (algebraic D hg Θ j X component)

def betti : D.sphericalInputs →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1) :=
  (CMExtraction.KaehlerClasses.Intrinsic.kaehlerComplexifiedClass X).comp (algebraic D hg Θ j X component)

theorem smooth (φ : D.sphericalInputs) :
    (representative D hg Θ j X component φ).val.val = CMExtraction.Intrinsic.PeriodForms.thetaOnPeriodVariety D hg Θ j X component φ := rfl

theorem betti_represents (φ : D.sphericalInputs) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1 (betti D hg Θ j X component φ) =
      (X.deRhamBettiIso 1).hom (X.deRhamClass 1 (representative D hg Θ j X component φ).val) :=
  KaehlerPureRepresentative.CM.complexification X (algebraic D hg Θ j X component φ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaPureForms.CM
