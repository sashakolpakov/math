import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ConormalRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ModuleLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.QuotientLocalization

/-! # Conormal Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ConormalLocalization.BundleCycles

noncomputable section

/-! The augmented conormal restriction is the actual localized-module
map over the localized quotient coefficient ring. -/

variable {R : Type} [CommRing R] (I : Ideal R) (S : Type) [CommRing S] [Algebra R S]

attribute [local instance] Conormal.QuotientLocalization.BundleCycles.conormalQuotientAlgebra Conormal.QuotientLocalization.BundleCycles.conormalQuotientModule

theorem augmentedConormalGradedRestriction_localization :
    ConormalRestriction.BundleCycles.augmentedConormalGradedRestriction I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map =
      Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)))
        (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear (S := S ⧸ I.map (algebraMap R S))
          (ModuleLocalization.BundleCycles.augmentedModuleLocalizationMap (S := S ⧸ I.map (algebraMap R S))
            (Conormal.QuotientLocalization.BundleCycles.conormalQuotientLocalizationMap I S))) := by
  rfl

variable (D : Submonoid R) [IsLocalization D S]

include D in
theorem cotangentCoefficientMap_localization_span :
    Submodule.span (S ⧸ I.map (algebraMap R S))
      (Set.range (Conormal.ConormalRestriction.BundleCycles.cotangentCoefficientMap I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) = ⊤ := by
  let : IsLocalization (D.map (Ideal.Quotient.mk I)) (S ⧸ I.map (algebraMap R S)) :=
    QuotientLocalization.BundleCycles.quotientLocalizationMap_isLocalization D S I
  exact SymmetricProjective.Localization.BundleCycles.localizedModule_span_range (S := S ⧸ I.map (algebraMap R S))
    (D.map (Ideal.Quotient.mk I)) (Conormal.QuotientLocalization.BundleCycles.conormalQuotientLocalizationMap I S)

include D in
theorem cotangentCoefficientMap_span (J : Ideal S) (hJ : I.map (algebraMap R S) = J)
    (hIJ : I ≤ J.comap (algebraMap R S)) :
    Submodule.span (S ⧸ J) (Set.range (Conormal.ConormalRestriction.BundleCycles.cotangentCoefficientMap I J (algebraMap R S) hIJ)) = ⊤ := by
  subst J
  exact cotangentCoefficientMap_localization_span I S D

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ConormalLocalization.BundleCycles
