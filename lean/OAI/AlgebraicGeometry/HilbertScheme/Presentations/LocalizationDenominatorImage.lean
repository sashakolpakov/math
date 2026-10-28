import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.LocalizationScalars

/-! # Localization Denominator Image -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationDenominatorImage.GradedModules

noncomputable section

/-! Localization comparisons with an explicitly identified image denominator. -/

universe u v w t

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {B : Type w} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable (M : Type t) [AddCommGroup M] [Module R M] [Module A M] [Module B M]
  [IsScalarTower R A M] [IsScalarTower R B M] [IsScalarTower A B M]

def awayModuleScalarEquivOfEq (a : A) (b : B) (h : algebraMap A B a = b) :
    Presentations.Module.Fractions.GradedModules.AwayModule a M ≃ₗ[R] Presentations.Module.Fractions.GradedModules.AwayModule b M := by
  subst b
  exact Presentations.Module.LocalizationScalars.GradedModules.awayModuleScalarEquiv (R := R) (B := B) M a

theorem awayModuleScalarEquivOfEq_fraction (a : A) (b : B) (h : algebraMap A B a = b)
    (k : ℕ) (m : M) :
    awayModuleScalarEquivOfEq (R := R) M a b h (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m) =
      Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) b k m := by
  subst b
  exact Presentations.Module.LocalizationScalars.GradedModules.awayModuleScalarEquiv_fraction M a k m

theorem awayModuleScalarEquivOfEq_degree (ℳ : ℤ → Submodule R M)
    (a : A) (b : B) (h : algebraMap A B a = b) (e d : ℤ) :
    (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a e d).map (awayModuleScalarEquivOfEq (R := R) M a b h).toLinearMap =
      Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ b e d := by
  subst b
  exact Presentations.Module.LocalizationScalars.GradedModules.awayModuleScalarEquiv_degree M ℳ a e d

def awayModuleScalarDegreeEquivOfEq (ℳ : ℤ → Submodule R M)
    (a : A) (b : B) (h : algebraMap A B a = b) (e d : ℤ) :
    Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a e d ≃ₗ[R] Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ b e d :=
  (awayModuleScalarEquivOfEq (R := R) M a b h).ofSubmodules _ _
    (awayModuleScalarEquivOfEq_degree M ℳ a b h e d)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationDenominatorImage.GradedModules
