import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalSectionDeformationSmooth
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSectionNormalCone

/-! # Localized Section Deformation Smooth -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSectionDeformationSmooth.BundleCycles

noncomputable section

/-! Localizing a genuine section at a point of its center gives a
deformation formally smooth over the original base coefficient ring. -/

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] [Algebra.FormallySmooth A B] [Algebra.EssFiniteType A B]
    [IsNoetherianRing A] [IsNoetherianRing B] (p : Ideal A) [p.IsPrime]

attribute [local instance] LocalizedSectionNormalCone.BundleCycles.localizedSectionBaseAlgebra LocalizedSectionNormalCone.BundleCycles.localizedSectionQuotientAlgebra

theorem localizedSection_deformation_formallySmooth :
    Algebra.FormallySmooth A
      (Deformation.Iff.BundleCycles.deformationAlgebra ((RingHom.ker (algebraMap B A)).map
        (algebraMap B (Localization.AtPrime (p.comap (algebraMap B A)))))) := by
  let A' := Localization.AtPrime p
  let B' := Localization.AtPrime (p.comap (algebraMap B A))
  let : IsNoetherianRing A' := IsLocalization.isNoetherianRing p.primeCompl A' inferInstance
  let : IsNoetherianRing B' :=
    IsLocalization.isNoetherianRing (p.comap (algebraMap B A)).primeCompl B' inferInstance
  let : Nontrivial A' := IsLocalization.AtPrime.nontrivial A' p
  let : Algebra.FormallySmooth A A' := Algebra.FormallySmooth.of_isLocalization p.primeCompl
  let : Algebra.FormallySmooth A' (Deformation.Iff.BundleCycles.deformationAlgebra (RingHom.ker (algebraMap B' A'))) :=
    LocalSectionDeformationSmooth.BundleCycles.localSection_deformation_formallySmooth A' B'
  have h : Algebra.FormallySmooth A (Deformation.Iff.BundleCycles.deformationAlgebra (RingHom.ker (algebraMap B' A'))) :=
    Algebra.FormallySmooth.comp A A' _
  have hI : RingHom.ker (algebraMap B' A') =
      (RingHom.ker (algebraMap B A)).map (algebraMap B B') := Section.Localization.BundleCycles.localizedSectionQuotient_ker A B p
  exact hI ▸ h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSectionDeformationSmooth.BundleCycles
