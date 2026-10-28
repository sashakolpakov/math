import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.Localization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.NormalConeEquiv

/-! # Localized Section Normal Cone -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSectionNormalCone.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual localizations of a smooth section have symmetric normal cone -/

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] (p : Ideal A) [p.IsPrime]

abbrev localizedSectionBaseAlgebra :
    Algebra (Localization.AtPrime p) (Localization.AtPrime (p.comap (algebraMap B A))) :=
  (Section.Localization.BundleCycles.localizedSectionLift A B p).toAlgebra

abbrev localizedSectionQuotientAlgebra :
    Algebra (Localization.AtPrime (p.comap (algebraMap B A))) (Localization.AtPrime p) :=
  (Section.Localization.BundleCycles.localizedSectionQuotient A B p).toAlgebra

attribute [local instance] localizedSectionBaseAlgebra localizedSectionQuotientAlgebra

instance localizedSectionRetract_tower :
    IsScalarTower (Localization.AtPrime p) (Localization.AtPrime (p.comap (algebraMap B A)))
      (Localization.AtPrime p) :=
  IsScalarTower.of_algebraMap_eq fun a => (DFunLike.congr_fun (Section.Localization.BundleCycles.localizedSection_retraction A B p) a).symm

instance localizedSectionBase_tower :
    IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime (p.comap (algebraMap B A))) :=
  IsScalarTower.of_algebraMap_eq fun a =>
    (IsScalarTower.algebraMap_apply A B (Localization.AtPrime (p.comap (algebraMap B A))) a).trans
      (Section.Localization.BundleCycles.localizedSectionLift_algebraMap A B p a).symm

instance localizedSection_formallySmooth [Algebra.FormallySmooth A B] :
    Algebra.FormallySmooth (Localization.AtPrime p) (Localization.AtPrime (p.comap (algebraMap B A))) := by
  have : Algebra.FormallySmooth A (Localization.AtPrime (p.comap (algebraMap B A))) :=
    Algebra.FormallySmooth.comp A B _
  exact Algebra.FormallySmooth.of_restrictScalars (R := A) (A := Localization.AtPrime p)
    (B := Localization.AtPrime (p.comap (algebraMap B A)))

instance localizedSection_essFiniteType [Algebra.EssFiniteType A B] :
    Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime (p.comap (algebraMap B A))) := by
  have : Algebra.EssFiniteType A (Localization.AtPrime (p.comap (algebraMap B A))) :=
    Algebra.EssFiniteType.comp A B _
  exact Algebra.EssFiniteType.of_comp A _ _

theorem localizedSection_normalConeSymmetricMap_bijective
    [Algebra.FormallySmooth A B] [Algebra.EssFiniteType A B] :
    Function.Bijective (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap
      ((RingHom.ker (algebraMap B A)).map (algebraMap B (Localization.AtPrime (p.comap (algebraMap B A)))))) := by
  rw [← Section.Localization.BundleCycles.localizedSectionQuotient_ker A B p]
  exact Section.NormalConeEquiv.BundleCycles.sectionNormalConeSymmetricMap_bijective (Localization.AtPrime p)
    (Localization.AtPrime (p.comap (algebraMap B A)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSectionNormalCone.BundleCycles
