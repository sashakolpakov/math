import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationDenominatorImage
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.ModuleRestriction

/-! # Localization Scalar Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationScalarRestriction.GradedModules

noncomputable section

/-! Localization comparisons between scalar algebras commute with principal-chart restriction. -/

universe u v w t

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {B : Type w} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable (M : Type t) [AddCommGroup M] [Module R M] [Module A M] [Module B M]
  [IsScalarTower R A M] [IsScalarTower R B M] [IsScalarTower A B M]

theorem awayModuleRestriction_fractionMap (a b c : A) (h : b = a * c) (k : ℕ) (m : M) :
    (Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M a b c h).restrictScalars R (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m) =
      Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) b k (c ^ k • m) := by
  rw [Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply, Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply]
  exact Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction_fraction M a b c h k m

theorem awayModuleScalarEquivOfEq_restriction
    (a b c : A) (h : b = a * c) (a' b' c' : B) (h' : b' = a' * c')
    (ha : algebraMap A B a = a') (hb : algebraMap A B b = b') (hc : algebraMap A B c = c')
    (x : Presentations.Module.Fractions.GradedModules.AwayModule a M) :
    LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq (R := R) M b b' hb (Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M a b c h x) =
      Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M a' b' c' h' (LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq (R := R) M a a' ha x) := by
  obtain ⟨k, m, rfl⟩ := Presentations.Module.Fractions.GradedModules.moduleFractionMap_surj (R := R) a x
  change LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq (R := R) M b b' hb
    ((Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M a b c h).restrictScalars R (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m)) = _
  rw [awayModuleRestriction_fractionMap, LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq_fraction,
    LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq_fraction]
  change Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) b' k (c ^ k • m) =
    (Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M a' b' c' h').restrictScalars R (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a' k m)
  rw [awayModuleRestriction_fractionMap]
  congr 1
  rw [← algebraMap_smul B, map_pow, hc]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationScalarRestriction.GradedModules
