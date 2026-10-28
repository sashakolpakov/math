import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalIntersectionFiniteness
import Mathlib.RingTheory.Ideal.Height

/-! # Surface Prime Factors -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SurfacePrimeFactors.BundleCycles

noncomputable section

/-!
# LineBundleCycles: prime factors on a local surface

In a local domain of dimension at most two, a prime containing a nonzero
equation is either minimal over that equation or the maximal ideal.
The latter factors have finite length and contribute zero to the
multiplication Euler length.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 2 R]

theorem surfacePrime_minimal_or_maximal (b : R) (hb : b ≠ 0)
    (J : Ideal R) [J.IsPrime] (hbJ : b ∈ J) :
    J ∈ (Ideal.span {b}).minimalPrimes ∨ J = IsLocalRing.maximalIdeal R := by
  by_cases hmin : J ∈ (Ideal.span {b}).minimalPrimes
  · exact Or.inl hmin
  right
  obtain ⟨K, hK, hKJ⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {b} ≤ J from Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbJ))
  let : K.IsPrime := hK.isPrime
  have hKne : K ≠ J := fun he => hmin (he ▸ hK)
  have hKb : b ∈ K := hK.le (Ideal.subset_span (Set.mem_singleton b))
  have hKbot : K ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hKb
    exact hb hKb
  have hKheight : (1 : ℕ∞) ≤ K.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hKbot)
  have hJheight : (2 : ℕ∞) ≤ J.height :=
    (add_le_add hKheight (le_refl (1 : ℕ∞))).trans
      (Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hKJ hKne))
  have hJm : J ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top'
  apply le_antisymm hJm
  by_contra hn
  have hjlt : J < IsLocalRing.maximalIdeal R := lt_of_le_not_ge hJm hn
  have h3 : (3 : ℕ∞) ≤ (IsLocalRing.maximalIdeal R).height :=
    (add_le_add hJheight (le_refl (1 : ℕ∞))).trans (Ideal.height_add_one_le_of_lt_of_isPrime hjlt)
  have h2 : (IsLocalRing.maximalIdeal R).height ≤ (2 : ℕ∞) :=
    WithBot.coe_le_coe.mp (Ideal.height_le_ringKrullDim_of_isPrime.trans
      (Ring.krullDimLE_iff.mp ‹Ring.KrullDimLE 2 R›))
  exact (by norm_num : ¬ (3 : ℕ∞) ≤ 2) (h3.trans h2)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SurfacePrimeFactors.BundleCycles
