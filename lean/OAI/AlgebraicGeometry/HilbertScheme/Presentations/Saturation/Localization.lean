import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.MonomialBasis
import Mathlib.RingTheory.Localization.Ideal

/-! # Localization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-!
Homogeneous saturation can be checked one projective coordinate chart at
a time. Powers of the individual variables suffice, by the pigeonhole
bound on monomials of a fixed degree.
-/

open _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

theorem Saturation.Localization.GradedHilbert.monomial_degree_pigeonhole (k : Fin (n + 1) → ℕ)
    (a : Fin (n + 1) →₀ ℕ) (ha : a.degree = ∑ i, k i) : ∃ i, k i ≤ a i := by
  classical
  by_contra! h
  have hlt : (∑ i, a i) < ∑ i, k i := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (h i).le
    · exact ⟨0, Finset.mem_univ 0, h 0⟩
  rw [← Finsupp.degree_eq_sum, ha] at hlt
  exact lt_irrefl _ hlt

theorem Hilbert.Polynomial.GradedHilbert.IsSaturated.mem_of_variable_powers {I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)}
    (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (d : ℕ) (hf : f.IsHomogeneous d)
    (hpow : ∀ i : Fin (n + 1), ∃ k : ℕ, X i ^ k * f ∈ I) : f ∈ I := by
  classical
  choose k hk using hpow
  apply hI f d hf
  refine ⟨∑ i, k i, fun g hg => ?_⟩
  rw [← g.support_sum_monomial_coeff, Finset.sum_mul]
  apply I.sum_mem
  intro a ha
  have had : a.degree = ∑ i, k i := (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support g _).mp hg a ha
  obtain ⟨i, hi⟩ := Saturation.Localization.GradedHilbert.monomial_degree_pigeonhole k a had
  have hei : Finsupp.single i (k i) ≤ a := Finsupp.single_le_iff.mpr hi
  have hterm : monomial a (g.coeff a) * f =
      monomial (a - Finsupp.single i (k i)) (g.coeff a) * (X i ^ k i * f) := by
    rw [← mul_assoc, X_pow_eq_monomial, monomial_mul_monomial, mul_one, tsub_add_cancel_of_le hei]
  rw [hterm]
  exact I.mul_mem_left _ (hk i)

theorem Saturation.Localization.GradedHilbert.saturated_eq_of_variable_power_membership
    (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (hJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal)
    (hIJ : ∀ (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (d : ℕ), f.IsHomogeneous d → f ∈ I.toIdeal →
      ∀ i : Fin (n + 1), ∃ k : ℕ, X i ^ k * f ∈ J.toIdeal)
    (hJI : ∀ (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (d : ℕ), f.IsHomogeneous d → f ∈ J.toIdeal →
      ∀ i : Fin (n + 1), ∃ k : ℕ, X i ^ k * f ∈ I.toIdeal) : I = J := by
  apply HomogeneousIdeal.ext'
  intro d f hf
  exact ⟨fun h => hJ.mem_of_variable_powers f d hf (hIJ f d hf h),
    fun h => hI.mem_of_variable_powers f d hf (hJI f d hf h)⟩

theorem Saturation.Localization.GradedHilbert.saturated_eq_of_coordinate_localizations
    (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (hJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal)
    (hlocal : ∀ i : Fin (n + 1),
      I.toIdeal.map (algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Localization.Away (X (R := R) i))) =
        J.toIdeal.map (algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Localization.Away (X (R := R) i)))) : I = J := by
  apply Saturation.Localization.GradedHilbert.saturated_eq_of_variable_power_membership I J hI hJ
  · intro f _ _ hf i
    have hmem := Ideal.mem_map_of_mem
      (algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Localization.Away (X (R := R) i))) hf
    rw [hlocal i] at hmem
    obtain ⟨s, hsmem, hs⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers (X i)) (Localization.Away (X (R := R) i)) J.toIdeal f).mp hmem
    obtain ⟨k, hk⟩ := hsmem
    rw [← hk] at hs
    exact ⟨k, hs⟩
  · intro f _ _ hf i
    have hmem := Ideal.mem_map_of_mem
      (algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Localization.Away (X (R := R) i))) hf
    rw [← hlocal i] at hmem
    obtain ⟨s, hsmem, hs⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers (X i)) (Localization.Away (X (R := R) i)) I.toIdeal f).mp hmem
    obtain ⟨k, hk⟩ := hsmem
    rw [← hk] at hs
    exact ⟨k, hs⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations
