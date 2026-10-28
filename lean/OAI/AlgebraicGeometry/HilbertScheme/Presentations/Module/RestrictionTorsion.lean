import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationScalarRestriction

/-! # Restriction Torsion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.RestrictionTorsion.GradedModules

noncomputable section

/-! Cokernels and kernels of a principal-chart restriction are killed elementwise by the added denominator. -/

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

theorem moduleFractionMap_scalar_apply (a : A) (k : ℕ) (c : A) (m : M) :
    Fractions.GradedModules.moduleFractionMap (R := R) a k (c • m) = c • Fractions.GradedModules.moduleFractionMap (R := R) a k m := by
  rw [Fractions.GradedModules.moduleFractionMap_apply, Fractions.GradedModules.moduleFractionMap_apply, LocalizedModule.smul'_mk]

theorem awayModuleRestriction_power_preimage (a b c : A) (h : b = a * c) (x : Fractions.GradedModules.AwayModule b M) :
    ∃ (k : ℕ) (y : Fractions.GradedModules.AwayModule a M), ModuleRestriction.GradedModules.awayModuleRestriction M a b c h y = c ^ k • x := by
  obtain ⟨k, m, rfl⟩ := Fractions.GradedModules.moduleFractionMap_surj (R := A) b x
  refine ⟨k, Fractions.GradedModules.moduleFractionMap (R := A) a k m, ?_⟩
  change (ModuleRestriction.GradedModules.awayModuleRestriction M a b c h).restrictScalars A (Fractions.GradedModules.moduleFractionMap (R := A) a k m) = _
  rw [LocalizationScalarRestriction.GradedModules.awayModuleRestriction_fractionMap, moduleFractionMap_scalar_apply]

theorem awayModuleRestriction_kernel_power (a b c : A) (h : b = a * c)
    (x : Fractions.GradedModules.AwayModule a M) (hx : ModuleRestriction.GradedModules.awayModuleRestriction M a b c h x = 0) :
    ∃ k : ℕ, c ^ k • x = 0 := by
  obtain ⟨k, m, rfl⟩ := Fractions.GradedModules.moduleFractionMap_surj (R := A) a x
  change (ModuleRestriction.GradedModules.awayModuleRestriction M a b c h).restrictScalars A (Fractions.GradedModules.moduleFractionMap (R := A) a k m) = 0 at hx
  rw [LocalizationScalarRestriction.GradedModules.awayModuleRestriction_fractionMap, Fractions.GradedModules.moduleFractionMap_eq_zero] at hx
  obtain ⟨l, hl⟩ := hx
  refine ⟨l + k, ?_⟩
  rw [← moduleFractionMap_scalar_apply, Fractions.GradedModules.moduleFractionMap_eq_zero]
  refine ⟨l, ?_⟩
  rw [h, mul_pow, mul_smul, smul_smul (c ^ l) (c ^ k), ← pow_add] at hl
  exact hl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.RestrictionTorsion.GradedModules
