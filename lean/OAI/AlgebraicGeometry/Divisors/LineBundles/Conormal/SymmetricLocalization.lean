import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.QuotientLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ConormalRestriction

/-! # Symmetric Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SymmetricLocalization.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual conormal symmetric algebra commutes with localization -/

variable {R : Type} [CommRing R] (I : Ideal R) (S : Type) [CommRing S] [Algebra R S]

attribute [local instance] QuotientLocalization.BundleCycles.conormalQuotientAlgebra QuotientLocalization.BundleCycles.conormalQuotientModule

theorem conormalSymmetricRestriction_eq_moduleMap :
    ConormalRestriction.BundleCycles.conormalSymmetricRestriction I (I.map (algebraMap R S)) (algebraMap R S)
      Ideal.le_comap_map =
    Symmetric.LocalizationMap.BundleCycles.symmetricModuleMap (S := S ⧸ I.map (algebraMap R S)) (QuotientLocalization.BundleCycles.conormalQuotientLocalizationMap I S) := by
  apply Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext
  · intro r
    rw [ConormalRestriction.BundleCycles.conormalSymmetricRestriction_algebraMap, Symmetric.LocalizationMap.BundleCycles.symmetricModuleMap_algebraMap]
    rfl
  · intro a
    obtain ⟨a, rfl⟩ := I.toCotangent_surjective a
    rw [ConormalRestriction.BundleCycles.conormalSymmetricRestriction_generator, Symmetric.LocalizationMap.BundleCycles.symmetricModuleMap_generator,
      QuotientLocalization.BundleCycles.conormalQuotientLocalizationMap_toCotangent]

def conormalSymmetricDenominators (D : Submonoid R) :
    Submonoid (SymmetricAlgebra (R ⧸ I) I.Cotangent) :=
  (D.map (Ideal.Quotient.mk I)).map (algebraMap (R ⧸ I) (SymmetricAlgebra (R ⧸ I) I.Cotangent))

variable (D : Submonoid R) [IsLocalization D S]

theorem conormalSymmetricBase_isLocalization :
    letI := (ConormalRestriction.BundleCycles.conormalSymmetricRestriction I (I.map (algebraMap R S)) (algebraMap R S)
      Ideal.le_comap_map).toAlgebra
    IsLocalization (conormalSymmetricDenominators I D)
      (SymmetricAlgebra (S ⧸ I.map (algebraMap R S)) (I.map (algebraMap R S)).Cotangent) := by
  have : IsLocalization (D.map (Ideal.Quotient.mk I)) (S ⧸ I.map (algebraMap R S)) :=
    QuotientLocalization.BundleCycles.quotientLocalizationMap_isLocalization D S I
  have h := Symmetric.LocalizationEquiv.BundleCycles.symmetricModuleMap_isLocalization I.Cotangent (D.map (Ideal.Quotient.mk I))
    (S ⧸ I.map (algebraMap R S)) (QuotientLocalization.BundleCycles.conormalQuotientLocalizationMap I S)
  rw [← conormalSymmetricRestriction_eq_moduleMap I S] at h
  exact h

theorem conormalSymmetricRestriction_isLocalization (J : Ideal S)
    (hJ : I.map (algebraMap R S) = J) (hIJ : I ≤ J.comap (algebraMap R S)) :
    letI := (ConormalRestriction.BundleCycles.conormalSymmetricRestriction I J (algebraMap R S) hIJ).toAlgebra
    IsLocalization (conormalSymmetricDenominators I D) (SymmetricAlgebra (S ⧸ J) J.Cotangent) := by
  subst J
  exact conormalSymmetricBase_isLocalization I S D

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SymmetricLocalization.BundleCycles
