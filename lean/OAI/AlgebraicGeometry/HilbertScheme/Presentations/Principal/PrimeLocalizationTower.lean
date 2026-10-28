import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.PrimeLocalization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.AlgebraicGeometry.Stalk

/-! # Prime Localization Tower -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.PrimeLocalizationTower

noncomputable section

/-! The map from a principal neighborhood to a prime localization is
itself a localization, and the prime is the image of its closed point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]

theorem principalToPrimeMap_comp_algebraMap (s : A) (hs : s ∉ p) :
    (PrimeLocalization.principalToPrimeMap p s hs).comp (algebraMap A (Localization.Away s)) =
      algebraMap A (Localization.AtPrime p) :=
  RingHom.ext (PrimeLocalization.principalToPrimeMap_algebraMap p s hs)

theorem principalToPrime_isLocalization (s : A) (hs : s ∉ p) :
    letI : Algebra (Localization.Away s) (Localization.AtPrime p) := (PrimeLocalization.principalToPrimeMap p s hs).toAlgebra
    IsLocalization (p.primeCompl.map (algebraMap A (Localization.Away s))) (Localization.AtPrime p) := by
  let : Algebra (Localization.Away s) (Localization.AtPrime p) := (PrimeLocalization.principalToPrimeMap p s hs).toAlgebra
  let : IsScalarTower A (Localization.Away s) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq (fun a => (PrimeLocalization.principalToPrimeMap_algebraMap p s hs a).symm)
  exact IsLocalization.isLocalization_of_submonoid_le (Localization.Away s) (Localization.AtPrime p)
    (Submonoid.powers s) p.primeCompl (Submonoid.powers_le.mpr hs)

theorem spec_primeLocalization_closedPoint (p : PrimeSpectrum A) :
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime p.asIdeal)))
      (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)) = p := by
  apply PrimeSpectrum.ext
  exact Localization.AtPrime.under_maximalIdeal

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.PrimeLocalizationTower
