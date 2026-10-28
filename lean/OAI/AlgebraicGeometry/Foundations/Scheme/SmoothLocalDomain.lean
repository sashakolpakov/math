import OAI.AlgebraicGeometry.Foundations.Scheme.EtaleLocalDomain
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! # Smooth Local Domain -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SmoothLocalDomain

noncomputable section

/-!
# Local rings of smooth algebras over fields are domains

At a smooth prime, mathlib supplies a principal neighborhood which is standard
étale over a polynomial algebra. The polynomial algebra is an integrally
closed domain. The prime localization is an actual further localization of
that neighborhood, so the proved étale local-domain theorem applies.

Neither normality nor the local-domain conclusion is included as an extra
hypothesis on the smooth algebra.
-/

universe u v w

/-- Smoothness at a prime of a finitely presented algebra over a field makes
the corresponding local ring a domain. -/
theorem isDomain_localizationAtPrime_of_isSmoothAt
    (K : Type u) (S : Type v) [Field K] [CommRing S] [Algebra K S]
    [Algebra.FinitePresentation K S] (p : Ideal S) [p.IsPrime]
    [Algebra.IsSmoothAt K p] : IsDomain (Localization.AtPrime p) := by
  obtain ⟨f, hfp, n, hPB, _, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let P := MvPolynomial (Fin n) K
  let B := Localization.Away f
  let A := Localization.AtPrime p
  let : Algebra P B := hPB
  let : Algebra.IsStandardEtale P B := hEtale
  have hle : Submonoid.powers f ≤ p.primeCompl := Submonoid.powers_le.mpr hfp
  let : Algebra B A := IsLocalization.localizationAlgebraOfSubmonoidLe
    B A (Submonoid.powers f) p.primeCompl hle
  let : IsScalarTower S B A := IsLocalization.localization_isScalarTower_of_submonoid_le
    B A (Submonoid.powers f) p.primeCompl hle
  let : IsLocalization (p.primeCompl.map (algebraMap S B)) A :=
    IsLocalization.isLocalization_of_submonoid_le
      B A (Submonoid.powers f) p.primeCompl hle
  let : Algebra P A := ((algebraMap B A).comp (algebraMap P B)).toAlgebra
  let : IsScalarTower P B A := IsScalarTower.of_algebraMap_eq' rfl
  exact EtaleLocalDomain.isDomain_of_localization_of_etale P B A
    (p.primeCompl.map (algebraMap S B))

/-- Every prime localization of a smooth algebra over a field is a domain. -/
theorem isDomain_localizationAtPrime_of_smooth
    (K : Type u) (S : Type v) [Field K] [CommRing S] [Algebra K S]
    [Algebra.Smooth K S] (p : Ideal S) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) :=
  isDomain_localizationAtPrime_of_isSmoothAt K S p

/-- The same local-domain conclusion holds for any ring realizing the prime
localization, including actual stalks of an affine smooth scheme. -/
theorem isDomain_of_isLocalizationAtPrime_of_smooth
    (K : Type u) (S : Type v) (A : Type w)
    [Field K] [CommRing S] [Algebra K S] [Algebra.Smooth K S]
    [CommRing A] [Algebra S A] (p : Ideal S) [p.IsPrime]
    [IsLocalization.AtPrime A p] : IsDomain A := by
  let : IsDomain (Localization.AtPrime p) := isDomain_localizationAtPrime_of_smooth K S p
  let e : A ≃ₐ[S] Localization.AtPrime p :=
    IsLocalization.algEquiv p.primeCompl A (Localization.AtPrime p)
  exact e.injective.isDomain e.toRingHom

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SmoothLocalDomain
