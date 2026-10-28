import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedModuleFractions

/-! # Iterated Module Localization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedModuleLocalization.GradedModules

noncomputable section

/-! Two successive principal module localizations are the actual localization at the product denominator. -/

universe u v

variable {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]

def iteratedAwayToProduct (a b : A) : Presentations.Module.Fractions.GradedModules.AwayModule b (Presentations.Module.Fractions.GradedModules.AwayModule a M) →ₗ[A] Presentations.Module.Fractions.GradedModules.AwayModule (a * b) M :=
  LocalizedModule.lift (Submonoid.powers b) (Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M a (a * b) b rfl)
    (fun s => by
      obtain ⟨k, hk⟩ := s.property
      change IsUnit (algebraMap A (Module.End A (Presentations.Module.Fractions.GradedModules.AwayModule (a * b) M)) s.val)
      rw [← hk, map_pow]
      exact (Presentations.Module.ModuleRestriction.GradedModules.awayModuleFactor_isUnit M b (a * b) a (mul_comm a b)).pow k)

theorem iteratedAwayToProduct_mk_one (a b : A) (x : Presentations.Module.Fractions.GradedModules.AwayModule a M) :
    iteratedAwayToProduct M a b (LocalizedModule.mk x 1) = Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M a (a * b) b rfl x :=
  LocalizedModule.lift_mk_one _ _ _ x

theorem iteratedAwayToProduct_double_fraction (a b : A) (k : ℕ) (m : M) :
    iteratedAwayToProduct M a b
      (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) b k (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a k m)) =
    Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) (a * b) k m := by
  have hu := (Presentations.Module.ModuleRestriction.GradedModules.awayModuleFactor_isUnit M b (a * b) a (mul_comm a b)).pow k
  rw [← map_pow] at hu
  apply ((Module.End.isUnit_iff _).mp hu).injective
  change b ^ k • iteratedAwayToProduct M a b
    (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) b k (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a k m)) =
    b ^ k • Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) (a * b) k m
  rw [← map_smul, IteratedModuleFractions.GradedModules.moduleFractionMap_cancel]
  rw [Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply b 0]
  rw [show Presentations.Module.Fractions.GradedModules.moduleDenominator b 0 = 1 from Subtype.ext (pow_zero b)]
  change iteratedAwayToProduct M a b (LocalizedModule.mk (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a k m) 1) = _
  rw [iteratedAwayToProduct_mk_one]
  change (Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M a (a * b) b rfl).restrictScalars A
    (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a k m) = _
  rw [LocalizationScalarRestriction.GradedModules.awayModuleRestriction_fractionMap, Presentations.Module.RestrictionTorsion.GradedModules.moduleFractionMap_scalar_apply]

theorem iteratedAwayToProduct_bijective (a b : A) : Function.Bijective (iteratedAwayToProduct M a b) := by
  have hz (x : Presentations.Module.Fractions.GradedModules.AwayModule b (Presentations.Module.Fractions.GradedModules.AwayModule a M)) (hx : iteratedAwayToProduct M a b x = 0) : x = 0 := by
    obtain ⟨k, m, rfl⟩ := IteratedModuleFractions.GradedModules.iteratedModuleFraction_surj M a b x
    rw [iteratedAwayToProduct_double_fraction, Presentations.Module.Fractions.GradedModules.moduleFractionMap_eq_zero] at hx
    obtain ⟨t, ht⟩ := hx
    rw [Presentations.Module.Fractions.GradedModules.moduleFractionMap_eq_zero]
    refine ⟨t, ?_⟩
    rw [← Presentations.Module.RestrictionTorsion.GradedModules.moduleFractionMap_scalar_apply, Presentations.Module.Fractions.GradedModules.moduleFractionMap_eq_zero]
    exact ⟨t, by simpa only [mul_pow, mul_smul] using ht⟩
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hz (x - y)
    rw [map_sub, hxy, sub_self]
  · intro x
    obtain ⟨k, m, rfl⟩ := Presentations.Module.Fractions.GradedModules.moduleFractionMap_surj (R := A) (a * b) x
    exact ⟨Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) b k (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a k m),
      iteratedAwayToProduct_double_fraction M a b k m⟩

def iteratedAwayModuleEquiv (a b : A) : Presentations.Module.Fractions.GradedModules.AwayModule b (Presentations.Module.Fractions.GradedModules.AwayModule a M) ≃ₗ[A] Presentations.Module.Fractions.GradedModules.AwayModule (a * b) M :=
  LinearEquiv.ofBijective (iteratedAwayToProduct M a b) (iteratedAwayToProduct_bijective M a b)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedModuleLocalization.GradedModules
