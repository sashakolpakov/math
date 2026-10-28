import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.Fractions

/-! # Zero Scalar Localization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ZeroScalarLocalization.GradedModules

/-! A localization vanishes when its denominator acts as zero. -/

universe u v w

variable {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]

theorem awayModule_subsingleton_of_scalar_zero (a : A) (ha : ∀ m : M, a • m = 0) :
    Subsingleton (Presentations.Module.Fractions.GradedModules.AwayModule a M) := by
  apply (IsLocalizedModule.subsingleton_iff (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)).mpr
  intro m
  exact ⟨a, ⟨1, pow_one a⟩, ha m⟩

variable {B : Type w} [CommRing B] [Algebra A B] [Module B M] [IsScalarTower A B M]

theorem awayModule_subsingleton_of_algebraMap_zero (a : A) (ha : algebraMap A B a = 0) :
    Subsingleton (Presentations.Module.Fractions.GradedModules.AwayModule a M) := by
  apply awayModule_subsingleton_of_scalar_zero M a
  intro m
  rw [← algebraMap_smul B, ha, zero_smul]

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ZeroScalarLocalization.GradedModules
