import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # DVR Maximal Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DVRMaximalSquare.BundleCycles

noncomputable section

/-! # LineBundleCycles: the first-order ideal criterion for a genuine DVR uniformizer -/

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem dvr_irreducible_not_mem_maximal_square {π : R} (hπ : Irreducible π) :
    π ∉ maximalIdeal R ^ 2 := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨b, hb⟩
  have h : 1 = π * b := by
    apply mul_left_cancel₀ hπ.ne_zero
    simpa only [mul_one, pow_two, mul_assoc] using hb
  exact hπ.not_isUnit (isUnit_of_dvd_one ⟨b, h⟩)

theorem dvr_irreducible_iff_maximal_not_square (a : R) :
    Irreducible a ↔ a ∈ maximalIdeal R ∧ a ∉ maximalIdeal R ^ 2 := by
  constructor
  · intro ha
    exact ⟨(IsLocalRing.mem_maximalIdeal a).mpr ha.not_isUnit,
      dvr_irreducible_not_mem_maximal_square ha⟩
  · rintro ⟨ha, ha2⟩
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hdiv : π ∣ a := by
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
      exact ha
    obtain ⟨b, rfl⟩ := hdiv
    have hb : IsUnit b := by
      by_contra hb
      have hbm : b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal b).mpr hb
      have hπm : π ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit
      exact ha2 (by simpa only [pow_two] using Ideal.mul_mem_mul hπm hbm)
    exact (irreducible_mul_isUnit hb).mpr hπ

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DVRMaximalSquare.BundleCycles
