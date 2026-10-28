import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SemilinearMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ProjectivePullback
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-! # Module Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ModuleLocalization.BundleCycles

noncomputable section

section

/-! Localizing a module together with its distinguished coefficient
summand gives the actual augmented localization map. -/

variable {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S N]
    [IsScalarTower R S N] (D : Submonoid R) [IsLocalization D S]
    (f : M →ₗ[R] N) [IsLocalizedModule D f]

def augmentedModuleLocalizationMap : R × M →ₗ[R] S × N :=
  (Algebra.linearMap R S).prodMap f

instance augmentedModuleLocalizationMap_isLocalizedModule :
    IsLocalizedModule D (augmentedModuleLocalizationMap (S := S) f) := by
  unfold augmentedModuleLocalizationMap
  infer_instance

theorem augmentedModuleLocalizationMap_semilinear :
    Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear (S := S) (augmentedModuleLocalizationMap (S := S) f) =
      SemilinearMap.BundleCycles.augmentedSemilinearMap (algebraMap R S) (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear f) := by
  ext v <;> rfl

include D in
theorem augmentedModuleLocalizationMap_span :
    Submodule.span S (Set.range
      (SemilinearMap.BundleCycles.augmentedSemilinearMap (algebraMap R S) (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear f))) = ⊤ :=
  SemilinearMap.BundleCycles.augmentedSemilinearMap_span _ _ (SymmetricProjective.Localization.BundleCycles.localizedModule_span_range (S := S) D f)

end

/-! The augmented symmetric projective spectrum has its actual
principal-localization pullback square. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S N]
    [IsScalarTower R S N] (r : R) [IsLocalization.Away r S]
    (f : M →ₗ[R] N) [IsLocalizedModule (Submonoid.powers r) f]

theorem symmetricAugmentedProjective_principal_isPullback :
    IsPullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S (S × N))
      (SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) (augmentedModuleLocalizationMap f))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) :=
  SymmetricProjective.ProjectivePullback.BundleCycles.symmetricProjective_principal_isPullback (R := R) (M := R × M) (S := S) (N := S × N) r
    (augmentedModuleLocalizationMap f)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ModuleLocalization.BundleCycles
