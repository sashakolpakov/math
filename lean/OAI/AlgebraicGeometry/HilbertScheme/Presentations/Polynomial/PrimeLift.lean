import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.PrimeLocalization
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Prime Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.PrimeLift

noncomputable section

/-! Polynomial algebra maps into a prime localization lift, with their
coefficient map preserved, to one principal neighborhood. -/

open _root_.MvPolynomial

universe u v w
variable {B : Type u} [CommRing B] {A : Type v} [CommRing A] [Algebra B A]
variable (p : Ideal A) [p.IsPrime] {κ : Type w} [Fintype κ]

theorem polynomial_prime_localization_lift (f : MvPolynomial κ B →+* Localization.AtPrime p)
    (hf : ∀ b, f (C b) = algebraMap A (Localization.AtPrime p) (algebraMap B A b)) :
    ∃ (s : A) (hs : s ∉ p) (g : MvPolynomial κ B →+* Localization.Away s),
      (∀ b, g (C b) = algebraMap A (Localization.Away s) (algebraMap B A b)) ∧
      (Principal.PrimeLocalization.principalToPrimeMap p s hs).comp g = f := by
  obtain ⟨s, hs, x, hx⟩ := Principal.PrimeLocalization.finite_primeLocalization_lift p (fun i => f (X i))
  let g := MvPolynomial.eval₂Hom ((algebraMap A (Localization.Away s)).comp (algebraMap B A)) x
  refine ⟨s, hs, g, fun b => ?_, ?_⟩
  · exact MvPolynomial.eval₂_C _ _ _
  · apply MvPolynomial.ringHom_ext
    · intro b
      change Principal.PrimeLocalization.principalToPrimeMap p s hs (g (C b)) = f (C b)
      rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Principal.PrimeLocalization.principalToPrimeMap_algebraMap, hf b]
    · intro i
      change Principal.PrimeLocalization.principalToPrimeMap p s hs (g (X i)) = f (X i)
      simpa only [g, MvPolynomial.eval₂Hom_X'] using hx i

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.PrimeLift
