import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EtaleRegular
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Smooth Regular -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRegular.Construction

noncomputable section

/-! Regularity of smooth algebras for the Openness fiber dimension argument. -/

/-- A regular localization gives regular local rings at the primes it meets. -/
theorem isRegularLocalRing_atPrime_of_regular_localization
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    (M : Submonoid R) [IsLocalization M B] [IsRegularRing B]
    (p : Ideal R) [p.IsPrime] (hp : Disjoint (M : Set R) (p : Set R)) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  let q := p.map (algebraMap R B)
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ _ ‹_› hp
  have : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
    exact (IsLocalization.under_map_of_isPrime_disjoint M _ ‹_› hp).symm
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime q) (Localization.AtPrime p)).toRingEquiv

/-- Smooth algebras over regular rings are regular. The standard smooth local
structure gives an etale algebra over a polynomial ring near each prime. -/
theorem isRegularRing_of_smooth
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [IsRegularRing R] [Algebra.Smooth R B] : IsRegularRing B := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  apply isRegularRing_iff.mpr
  intro p hp
  obtain ⟨f, hfp, n, _, _, hf⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
  have : Algebra.IsStandardEtale (MvPolynomial (Fin n) R) (Localization.Away f) := hf
  have : IsRegularRing (Localization.Away f) :=
    EtaleRegular.Construction.isRegularRing_of_etale (MvPolynomial (Fin n) R) (Localization.Away f)
  apply isRegularLocalRing_atPrime_of_regular_localization B (Localization.Away f)
    (Submonoid.powers f) p
  exact Set.disjoint_left.mpr fun x hx hxp ↦
    (Submonoid.powers_le.mpr hfp : Submonoid.powers f ≤ p.primeCompl) hx hxp

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRegular.Construction
