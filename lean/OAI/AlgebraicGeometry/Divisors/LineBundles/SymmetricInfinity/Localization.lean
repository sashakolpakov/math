import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Naturality
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ModuleLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealPullbackIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Bundle
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Base

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Localization.BundleCycles

noncomputable section

/-! The actual infinity ideal pulls back to the infinity ideal
under principal localization of a module and its coefficients. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S N]
    [IsScalarTower R S N] (r : R) [IsLocalization.Away r S]
    (f : M →ₗ[R] N) [IsLocalizedModule (Submonoid.powers r) f]

theorem symmetricInfinity_localization_square :
    Inclusion.BundleCycles.symmetricInfinityInclusion S N ≫
      SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) (Augmented.ModuleLocalization.BundleCycles.augmentedModuleLocalizationMap f) =
      SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) f ≫ Inclusion.BundleCycles.symmetricInfinityInclusion R M := by
  unfold SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap
  simp only [Augmented.ModuleLocalization.BundleCycles.augmentedModuleLocalizationMap_semilinear]
  exact Naturality.BundleCycles.symmetricInfinityInclusion_naturality (algebraMap R S) (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear f)
    (SymmetricProjective.Localization.BundleCycles.localizedModule_span_range (S := S) (Submonoid.powers r) f)

theorem symmetricInfinity_localization_isPullback :
    IsPullback (Inclusion.BundleCycles.symmetricInfinityInclusion S N)
      (SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) f)
      (SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) (Augmented.ModuleLocalization.BundleCycles.augmentedModuleLocalizationMap f))
      (Inclusion.BundleCycles.symmetricInfinityInclusion R M) := by
  have houter : IsPullback
      (Inclusion.BundleCycles.symmetricInfinityInclusion S N ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S (S × N))
      (SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) f)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Inclusion.BundleCycles.symmetricInfinityInclusion R M ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) := by
    have hS : Inclusion.BundleCycles.symmetricInfinityInclusion S N ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S (S × N) =
        SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S N := SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over (LinearMap.snd S S N) _
    have hR : Inclusion.BundleCycles.symmetricInfinityInclusion R M ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) =
        SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M := SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over (LinearMap.snd R R M) _
    rw [hS, hR]
    exact SymmetricProjective.ProjectivePullback.BundleCycles.symmetricProjective_principal_isPullback (S := S) r f
  have hinner : IsPullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S (S × N))
      (SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) (Augmented.ModuleLocalization.BundleCycles.augmentedModuleLocalizationMap f))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) :=
    Augmented.ModuleLocalization.BundleCycles.symmetricAugmentedProjective_principal_isPullback r f
  exact IsPullback.of_right (h₁₁ := Inclusion.BundleCycles.symmetricInfinityInclusion S N)
    (h₁₂ := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S (S × N)) (h₂₁ := Inclusion.BundleCycles.symmetricInfinityInclusion R M)
    (h₂₂ := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) houter
    (symmetricInfinity_localization_square r f) hinner

def symmetricInfinity_localization_idealIso :
    ((Bundle.Cycles.symmetricInfinityIdealLineBundle R M).pullback
      (SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) (Augmented.ModuleLocalization.BundleCycles.augmentedModuleLocalizationMap f))).sheaf ≅
      (Bundle.Cycles.symmetricInfinityIdealLineBundle S N).sheaf :=
  Cartier.IdealPullbackIso.BundleCycles.cartierIdealPullbackIso (Inclusion.BundleCycles.symmetricInfinityInclusion R M) (Inclusion.BundleCycles.symmetricInfinityInclusion S N)
    _ _ (symmetricInfinity_localization_isPullback r f)
    (Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals R M) (Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals S N)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Localization.BundleCycles
