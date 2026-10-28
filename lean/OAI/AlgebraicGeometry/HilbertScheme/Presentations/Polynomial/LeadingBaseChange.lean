import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-! # Leading Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.LeadingBaseChange

noncomputable section

/-! Injective coefficient maps preserve polynomial leading degrees and
leading coefficients. -/

open _root_.MvPolynomial

universe u v w
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {σ : Type w}

theorem polynomial_leading_degree_map (m : MonomialOrder σ)
    (φ : R →+* S) (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.degree (MvPolynomial.map φ f) = m.degree f := by
  unfold MonomialOrder.degree
  rw [MvPolynomial.support_map_of_injective f hφ]

theorem polynomial_leading_coefficient_map (m : MonomialOrder σ)
    (φ : R →+* S) (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.leadingCoeff (MvPolynomial.map φ f) = φ (m.leadingCoeff f) := by
  rw [MonomialOrder.leadingCoeff, polynomial_leading_degree_map m φ hφ, MvPolynomial.coeff_map]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.LeadingBaseChange
