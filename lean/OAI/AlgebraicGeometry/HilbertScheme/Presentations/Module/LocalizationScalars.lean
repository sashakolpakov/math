import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreePieces
import Mathlib.LinearAlgebra.Span.Basic

/-! # Localization Scalars -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.LocalizationScalars.GradedModules

noncomputable section

/-! Module localization and its homogeneous degree pieces are compatible with restriction of the coefficient algebra. -/

universe u v w t

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {B : Type w} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable (M : Type t) [AddCommGroup M] [Module R M] [Module A M] [Module B M]
  [IsScalarTower R A M] [IsScalarTower R B M] [IsScalarTower A B M]

def awayModuleScalarEquiv (a : A) :
    Fractions.GradedModules.AwayModule a M ≃ₗ[R] Fractions.GradedModules.AwayModule (algebraMap A B a) M := by
  let f := (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B a)) M).restrictScalars A
  let : IsLocalizedModule (Submonoid.powers a) f :=
    IsLocalizedModule.restrictScalars_powers a (LocalizedModule.mkLinearMap _ M)
  exact (IsLocalizedModule.iso (Submonoid.powers a) f).restrictScalars R

theorem awayModuleScalarEquiv_fraction (a : A) (k : ℕ) (m : M) :
    awayModuleScalarEquiv (R := R) (B := B) M a (Fractions.GradedModules.moduleFractionMap (R := R) a k m) =
      Fractions.GradedModules.moduleFractionMap (R := R) (algebraMap A B a) k m := by
  let f := (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B a)) M).restrictScalars A
  let : IsLocalizedModule (Submonoid.powers a) f :=
    IsLocalizedModule.restrictScalars_powers a (LocalizedModule.mkLinearMap _ M)
  rw [Fractions.GradedModules.moduleFractionMap_apply, Fractions.GradedModules.moduleFractionMap_apply]
  change IsLocalizedModule.mk' f m (Fractions.GradedModules.moduleDenominator a k) = _
  rw [← IsLocalizedModule.smul_inj f (Fractions.GradedModules.moduleDenominator a k), IsLocalizedModule.mk'_cancel']
  change LocalizedModule.mk m 1 = a ^ k • LocalizedModule.mk m (Fractions.GradedModules.moduleDenominator (algebraMap A B a) k)
  rw [← algebraMap_smul B, map_pow, LocalizedModule.smul'_mk]
  exact (LocalizedModule.mk_cancel (Fractions.GradedModules.moduleDenominator (algebraMap A B a) k) m).symm

theorem awayModuleScalarEquiv_degree (ℳ : ℤ → Submodule R M) (a : A) (e d : ℤ) :
    (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a e d).map (awayModuleScalarEquiv (R := R) (B := B) M a).toLinearMap =
      Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (algebraMap A B a) e d := by
  rw [Localized.DegreePieces.GradedModules.localizedDegreePiece, Localized.DegreePieces.GradedModules.localizedDegreePiece, Submodule.map_iSup]
  apply iSup_congr
  intro k
  rw [Localized.DegreePieces.GradedModules.localizedDegreeStage, Localized.DegreePieces.GradedModules.localizedDegreeStage, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro m
  exact awayModuleScalarEquiv_fraction M a k m

def awayModuleScalarDegreeEquiv (ℳ : ℤ → Submodule R M) (a : A) (e d : ℤ) :
    Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a e d ≃ₗ[R] Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (algebraMap A B a) e d :=
  (awayModuleScalarEquiv (R := R) (B := B) M a).ofSubmodules _ _ (awayModuleScalarEquiv_degree M ℳ a e d)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.LocalizationScalars.GradedModules
