import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrincipalPrimes
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SurfaceReciprocity

/-! # Canonical Surface Reciprocity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity

noncomputable section

/-! Local reciprocity indexed by all height-one components of the actual
principal divisors. Fixed finite supports allow subtraction of numerator
and denominator formulas. -/

open _root_.CategoryTheory IsLocalRing
open scoped Classical

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

def primes (f : R) (hf : f ≠ 0) : Finset (PrimeSpectrum R) :=
  (ProjectionFormula.Finite.PrincipalPrimes.finite R f hf).toFinset

theorem mem_primes (f : R) (hf : f ≠ 0) (p : PrimeSpectrum R) :
    p ∈ primes R f hf ↔ p.asIdeal.height = 1 ∧ f ∈ p.asIdeal :=
  Set.Finite.mem_toFinset _

def weight (p : PrimeSpectrum R) (f : R) : ℚ :=
  (Ring.ord (Localization.AtPrime p.asIdeal)
    (algebraMap R (Localization.AtPrime p.asIdeal) f)).toNat

def restrictedOrder (p : PrimeSpectrum R) (f : R) : ℚ :=
  (Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal f)).toNat

theorem weight_eq_zero (f : R) (hf : f ≠ 0) (p : PrimeSpectrum R)
    (hp : p.asIdeal.height = 1) (hout : p ∉ primes R f hf) : weight R p f = 0 := by
  have hfp : f ∉ p.asIdeal := fun h => hout ((mem_primes R f hf p).mpr ⟨hp, h⟩)
  have hu : IsUnit (algebraMap R (Localization.AtPrime p.asIdeal) f) :=
    IsLocalization.map_units (Localization.AtPrime p.asIdeal) (⟨f, hfp⟩ : p.asIdeal.primeCompl)
  simp only [weight, Ring.ord_of_isUnit hu, ENat.toNat_zero, Nat.cast_zero]

variable [IsLocalRing R]

theorem euler_eq_sum (hdim : (maximalIdeal R).height = 2)
    (f g : R) (hf : f ≠ 0) (hg : g ≠ 0)
    (havoid : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → f ∈ p → g ∉ p) :
    Tor.Euler.euler R (.of R (QuotSMulTop f R)) (.of R (QuotSMulTop g R)) 1 =
      ∑ p ∈ primes R f hf, weight R p f * restrictedOrder R p g := by
  obtain ⟨S, hS, hout, he⟩ := Local.SurfaceReciprocity.exists_euler_sum R hdim f g hf hg havoid
  apply he.trans
  have hsub : S ⊆ primes R f hf := fun p hp => (mem_primes R f hf p).mpr (hS p hp)
  apply Finset.sum_subset hsub
  intro p hp hpS
  have hz := hout p ((mem_primes R f hf p).mp hp).1 hpS
  simp only [hz, ENat.toNat_zero, Nat.cast_zero, zero_mul]

theorem order_sums_eq (hdim : (maximalIdeal R).height = 2)
    (f g : R) (hf : f ≠ 0) (hg : g ≠ 0)
    (havoid : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → f ∈ p → g ∉ p) :
    (∑ p ∈ primes R f hf, weight R p f * restrictedOrder R p g) =
      ∑ p ∈ primes R g hg, weight R p g * restrictedOrder R p f := by
  rw [← euler_eq_sum R hdim f g hf hg havoid,
    Tor.EulerTransport.comm R (.of R (QuotSMulTop f R)) (.of R (QuotSMulTop g R)) 1]
  exact euler_eq_sum R hdim g f hg hf (fun p _ hp hgp hfp => havoid p hp hfp hgp)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity
