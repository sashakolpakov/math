import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarGrading
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationMap
import Mathlib.RingTheory.Localization.Module

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Localization.BundleCycles

noncomputable section

/-! Localizing a module gives the native projective-spectrum restriction
map, because its actual image spans the localized module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S N]
    [IsScalarTower R S N] (D : Submonoid R) [IsLocalization D S]
    (f : M →ₗ[R] N) [IsLocalizedModule D f]

include D in
theorem localizedModule_span_range : Submodule.span S (Set.range (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear (S := S) f)) = ⊤ := by
  have h := span_eq_top_of_isLocalizedModule S D f (v := Set.univ) (by simp : Submodule.span R (Set.univ : Set M) = ⊤)
  rw [Set.image_univ] at h
  exact h

def localizedSymmetricProjectiveMap : Scheme.BundleCycles.symmetricProjectiveScheme S N ⟶ Scheme.BundleCycles.symmetricProjectiveScheme R M :=
  Symmetric.ScalarGrading.BundleCycles.symmetricScalarProjectiveMap (algebraMap R S) (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear f) (localizedModule_span_range D f)

theorem localizedSymmetricProjectiveMap_preimage (x : SymmetricAlgebra R M) :
    localizedSymmetricProjectiveMap D f ⁻¹ᵁ Proj.basicOpen (Symmetric.Grading.BundleCycles.symmetricGrading R M) x =
      Proj.basicOpen (Symmetric.Grading.BundleCycles.symmetricGrading S N) (Symmetric.LocalizationMap.BundleCycles.symmetricModuleMap (S := S) f x) := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Localization.BundleCycles
