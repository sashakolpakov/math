import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GlobalFormFaithfulness
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive

/-! # Projective Form Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ProjectiveFormFaithfulness

noncomputable section

/-! Actual Betti classes faithfully detect algebraic one-forms on a smooth
integral projective complex variety. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic

theorem kaehlerBettiClass_eq_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (form : FormConstants.OneForms V.toOver) (hform : HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass V form = 0) : form = 0 := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : V.toOver.left.IsSeparated := HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated V
  have hc : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass V.analyticModel V.analyticSpace 1
      (HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.closedKaehlerRealization V form) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (V.deRhamBettiIso 1).hom).1
    exact hform.trans (map_zero (V.deRhamBettiIso 1).hom.hom).symm
  have hz := ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.holomorphic_oneForm_eq_zero_of_class_eq_zero
    (HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.closedKaehlerRealization V form)
    (HodgeConjecture.CMExtraction.OpenPurity.Kaehler.globalSmoothForm_pure V.toOver form) hc
  exact GlobalFormFaithfulness.globalSmoothForm_eq_zero V.toOver form (congrArg Subtype.val hz)

theorem kaehlerBettiClass_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Function.Injective (HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass V) := by
  intro form other h
  apply sub_eq_zero.mp
  apply kaehlerBettiClass_eq_zero V (form - other)
  rw [map_sub, h, sub_self]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ProjectiveFormFaithfulness
