import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses

/-! # Kaehler Pure Representative -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KaehlerPureRepresentative.CM

noncomputable section

/-! The native algebraic one-form has an actual pure closed manifold
representative and its original rational-complexified Betti class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic

def pure (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    AbelianScheme.TateComparison.FormConstants.OneForms X.toOver →ₗ[ℂ] AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0 := by
  refine (CMExtraction.KaehlerClasses.Intrinsic.closedKaehlerRealization X).codRestrict _ ?_
  intro α
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : X.toOver.left.IsSeparated := CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated X
  exact CMExtraction.OpenPurity.Kaehler.globalSmoothForm_pure X.toOver α

theorem closed (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (α : AbelianScheme.TateComparison.FormConstants.OneForms X.toOver) :
    (pure X α).val = CMExtraction.KaehlerClasses.Intrinsic.closedKaehlerRealization X α := rfl

theorem betti (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (α : AbelianScheme.TateComparison.FormConstants.OneForms X.toOver) :
    (X.deRhamBettiIso 1).hom (X.deRhamClass 1 (pure X α).val) = CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass X α := rfl

theorem complexification (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (α : AbelianScheme.TateComparison.FormConstants.OneForms X.toOver) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1 (CMExtraction.KaehlerClasses.Intrinsic.kaehlerComplexifiedClass X α) =
      (X.deRhamBettiIso 1).hom (X.deRhamClass 1 (pure X α).val) :=
  (CMExtraction.Mem.bettiComplexification X.presentation 1).apply_symm_apply (CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass X α)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KaehlerPureRepresentative.CM
