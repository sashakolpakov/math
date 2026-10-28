import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedModuleLocalization

/-! # Iterated Localization Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedLocalizationRestriction.GradedModules

noncomputable section

/-! The actual iterated-localization equivalence commutes with principal-chart restriction. -/

universe u v

variable {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]

theorem iteratedAwayModuleEquiv_restriction (a b c t : A) (h : c = b * t)
    (x : Presentations.Module.Fractions.GradedModules.AwayModule b (Presentations.Module.Fractions.GradedModules.AwayModule a M)) :
    IteratedModuleLocalization.GradedModules.iteratedAwayModuleEquiv M a c (Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction (Presentations.Module.Fractions.GradedModules.AwayModule a M) b c t h x) =
    Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M (a * b) (a * c) t (by rw [h, mul_assoc])
      (IteratedModuleLocalization.GradedModules.iteratedAwayModuleEquiv M a b x) := by
  obtain ⟨k, m, rfl⟩ := IteratedModuleFractions.GradedModules.iteratedModuleFraction_surj M a b x
  change IteratedModuleLocalization.GradedModules.iteratedAwayToProduct M a c
    ((Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction (Presentations.Module.Fractions.GradedModules.AwayModule a M) b c t h).restrictScalars A
      (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) b k (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a k m))) =
    (Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M (a * b) (a * c) t (by rw [h, mul_assoc])).restrictScalars A
      (IteratedModuleLocalization.GradedModules.iteratedAwayToProduct M a b (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) b k (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a k m)))
  rw [LocalizationScalarRestriction.GradedModules.awayModuleRestriction_fractionMap, ← Presentations.Module.RestrictionTorsion.GradedModules.moduleFractionMap_scalar_apply,
    IteratedModuleLocalization.GradedModules.iteratedAwayToProduct_double_fraction, IteratedModuleLocalization.GradedModules.iteratedAwayToProduct_double_fraction,
    LocalizationScalarRestriction.GradedModules.awayModuleRestriction_fractionMap]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedLocalizationRestriction.GradedModules
