import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialLeadingCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.LocalizationNumerator
import Mathlib.RingTheory.Localization.FractionRing

/-! # Integral Polynomial Leading Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegralPolynomialLeadingCover.GradedHilbert

noncomputable section

/-! A finite leading-term cover over the fraction field can be chosen
with numerators in the original polynomial ideal. -/

open _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] [IsDomain R] {n : ℕ}

theorem exists_integral_polynomial_leading_cover
    (m : MonomialOrder (Fin (n + 1))) (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) :
    ∃ B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n),
      (∀ b ∈ B, b ∈ I ∧ b ≠ 0) ∧
      ∀ g ∈ I.map (MvPolynomial.map (algebraMap R (FractionRing R))), g ≠ 0 →
        ∃ b ∈ B, m.degree (MvPolynomial.map (algebraMap R (FractionRing R)) b) ≤ m.degree g := by
  classical
  let K := FractionRing R
  let J := I.map (MvPolynomial.map (algebraMap R K))
  obtain ⟨G, hG, hcover⟩ := Finite.PolynomialLeadingCover.GradedHilbert.exists_finite_polynomial_leading_cover m J
  have hnum (g : G) : ∃ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n, f ∈ I ∧ ∃ s : nonZeroDivisors R,
      MvPolynomial.map (algebraMap R K) f = g.val * C (algebraMap R K s.val) :=
    Polynomial.LocalizationNumerator.polynomial_ideal_localization_numerator (nonZeroDivisors R) K I g.val (hG g.val g.property).1
  choose f hf s hs using hnum
  have hmap0 (g : G) : MvPolynomial.map (algebraMap R K) (f g) ≠ 0 := by
    rw [hs g]
    apply mul_ne_zero (hG g.val g.property).2
    apply C_ne_zero.mpr
    intro hzero
    exact mem_nonZeroDivisors_iff_ne_zero.mp (s g).property
      (IsFractionRing.injective R K (hzero.trans (map_zero _).symm))
  have hdeg (g : G) : m.degree (MvPolynomial.map (algebraMap R K) (f g)) = m.degree g.val := by
    rw [hs g, m.degree_mul (hG g.val g.property).2]
    · rw [m.degree_C, add_zero]
    · apply C_ne_zero.mpr
      intro hzero
      exact mem_nonZeroDivisors_iff_ne_zero.mp (s g).property
        (IsFractionRing.injective R K (hzero.trans (map_zero _).symm))
  let B := Finset.univ.image f
  refine ⟨B, ?_, ?_⟩
  · intro b hb
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨hf g, fun h => hmap0 g (h ▸ map_zero _)⟩
  · intro g hg hg0
    obtain ⟨b, hb, hbg⟩ := hcover g hg hg0
    refine ⟨f ⟨b, hb⟩, Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [hdeg]
    exact hbg

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegralPolynomialLeadingCover.GradedHilbert
