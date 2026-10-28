import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.Fractions
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Ring Localization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.RingLocalization.GradedModules

noncomputable section

/-! Actual module localization of an algebra agrees with localization of its ring. -/

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (B : Type w) [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

theorem algebraMapSubmonoid_powers (a : A) :
    Algebra.algebraMapSubmonoid B (Submonoid.powers a) =
      Submonoid.powers (algebraMap A B a) :=
  Submonoid.map_powers (algebraMap A B) a

instance awayRingIsLocalization (a : A) :
    IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
      (Localization.Away (algebraMap A B a)) := by
  rw [algebraMapSubmonoid_powers]
  infer_instance

def moduleRingLocalizationEquiv (a : A) :
    Fractions.GradedModules.AwayModule a B ≃ₗ[R] Localization.Away (algebraMap A B a) :=
  (IsLocalizedModule.iso (Submonoid.powers a)
    (IsScalarTower.toAlgHom A B (Localization.Away (algebraMap A B a))).toLinearMap).restrictScalars R

theorem moduleRingLocalizationEquiv_fraction (a : A) (k : ℕ) (b : B) :
    moduleRingLocalizationEquiv (R := R) B a (Fractions.GradedModules.moduleFractionMap (R := R) a k b) =
      Localization.mk b (Fractions.GradedModules.moduleDenominator (algebraMap A B a) k) := by
  rw [Fractions.GradedModules.moduleFractionMap_apply, Localization.mk_eq_mk']
  change IsLocalizedModule.mk'
    (IsScalarTower.toAlgHom A B (Localization.Away (algebraMap A B a))).toLinearMap
    b (Fractions.GradedModules.moduleDenominator a k) = _
  rw [← IsLocalization.mk'_algebraMap_eq_mk']
  apply (IsLocalization.mk'_eq_iff_eq_mul).mpr
  simp only [Fractions.GradedModules.moduleDenominator, map_pow]
  simpa only [Fractions.GradedModules.moduleDenominator, map_pow] using
    (IsLocalization.mk'_spec (Localization.Away (algebraMap A B a))
      b (Fractions.GradedModules.moduleDenominator (algebraMap A B a) k)).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.RingLocalization.GradedModules
