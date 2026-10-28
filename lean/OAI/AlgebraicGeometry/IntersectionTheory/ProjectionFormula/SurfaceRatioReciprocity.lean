import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity

/-! # Surface Ratio Reciprocity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfaceRatioReciprocity

noncomputable section

/-! Numerator-minus-denominator reciprocity on a possibly nonnormal
local surface, with one finite support for both sides. -/

open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

theorem order_sums_eq (hdim : (IsLocalRing.maximalIdeal R).height = 2)
    (f a b : R) (hf : f ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfa : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → f ∈ p → a ∉ p)
    (hfb : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → f ∈ p → b ∉ p) :
    (∑ p ∈ CanonicalSurfaceReciprocity.primes R f hf, CanonicalSurfaceReciprocity.weight R p f * (CanonicalSurfaceReciprocity.restrictedOrder R p a - CanonicalSurfaceReciprocity.restrictedOrder R p b)) =
      ∑ p ∈ CanonicalSurfaceReciprocity.primes R a ha ∪ CanonicalSurfaceReciprocity.primes R b hb,
        (CanonicalSurfaceReciprocity.weight R p a - CanonicalSurfaceReciprocity.weight R p b) * CanonicalSurfaceReciprocity.restrictedOrder R p f := by
  let T := CanonicalSurfaceReciprocity.primes R a ha ∪ CanonicalSurfaceReciprocity.primes R b hb
  have hT (p : PrimeSpectrum R) (hp : p ∈ T) : p.asIdeal.height = 1 := by
    rcases Finset.mem_union.mp hp with h | h
    · exact ((CanonicalSurfaceReciprocity.mem_primes R a ha p).mp h).1
    · exact ((CanonicalSurfaceReciprocity.mem_primes R b hb p).mp h).1
  have heA : (∑ p ∈ CanonicalSurfaceReciprocity.primes R f hf, CanonicalSurfaceReciprocity.weight R p f * CanonicalSurfaceReciprocity.restrictedOrder R p a) =
      ∑ p ∈ T, CanonicalSurfaceReciprocity.weight R p a * CanonicalSurfaceReciprocity.restrictedOrder R p f := by
    apply (CanonicalSurfaceReciprocity.order_sums_eq R hdim f a hf ha hfa).trans
    apply Finset.sum_subset Finset.subset_union_left
    intro p hp hn
    rw [CanonicalSurfaceReciprocity.weight_eq_zero R a ha p (hT p hp) hn, zero_mul]
  have heB : (∑ p ∈ CanonicalSurfaceReciprocity.primes R f hf, CanonicalSurfaceReciprocity.weight R p f * CanonicalSurfaceReciprocity.restrictedOrder R p b) =
      ∑ p ∈ T, CanonicalSurfaceReciprocity.weight R p b * CanonicalSurfaceReciprocity.restrictedOrder R p f := by
    apply (CanonicalSurfaceReciprocity.order_sums_eq R hdim f b hf hb hfb).trans
    apply Finset.sum_subset Finset.subset_union_right
    intro p hp hn
    rw [CanonicalSurfaceReciprocity.weight_eq_zero R b hb p (hT p hp) hn, zero_mul]
  calc
    _ = (∑ p ∈ CanonicalSurfaceReciprocity.primes R f hf, CanonicalSurfaceReciprocity.weight R p f * CanonicalSurfaceReciprocity.restrictedOrder R p a) -
        ∑ p ∈ CanonicalSurfaceReciprocity.primes R f hf, CanonicalSurfaceReciprocity.weight R p f * CanonicalSurfaceReciprocity.restrictedOrder R p b := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      exact mul_sub _ _ _
    _ = (∑ p ∈ T, CanonicalSurfaceReciprocity.weight R p a * CanonicalSurfaceReciprocity.restrictedOrder R p f) -
        ∑ p ∈ T, CanonicalSurfaceReciprocity.weight R p b * CanonicalSurfaceReciprocity.restrictedOrder R p f := by rw [heA, heB]
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      exact (sub_mul _ _ _).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfaceRatioReciprocity
