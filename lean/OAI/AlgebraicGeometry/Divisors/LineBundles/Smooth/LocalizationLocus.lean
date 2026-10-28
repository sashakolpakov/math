import Mathlib.RingTheory.Smooth.Locus

/-! # Localization Locus -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.LocalizationLocus.BundleCycles

noncomputable section

/-! The actual smooth locus pulls back along any localization,
because the corresponding local rings are canonically identical. -/

variable (R A S : Type) [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
    (M : Submonoid A) [IsLocalization M S]

include M in
theorem smoothLocus_comap_localization :
    PrimeSpectrum.comap (algebraMap A S) ⁻¹' Algebra.smoothLocus R A = Algebra.smoothLocus R S := by
  ext q
  let p := PrimeSpectrum.comap (algebraMap A S) q
  let : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ q.asIdeal
  exact Algebra.FormallySmooth.iff_of_equiv
    ((IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)).restrictScalars R)

include M in
theorem isSmoothAt_of_localization [Algebra.FormallySmooth R S] (q : PrimeSpectrum S) :
    Algebra.IsSmoothAt R (q.comap (algebraMap A S)).asIdeal := by
  change q ∈ PrimeSpectrum.comap (algebraMap A S) ⁻¹' Algebra.smoothLocus R A
  rw [smoothLocus_comap_localization R A S M]
  exact inferInstanceAs (Algebra.FormallySmooth R (Localization.AtPrime q.asIdeal))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.LocalizationLocus.BundleCycles
