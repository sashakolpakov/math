import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.PrimeLift
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.LocalizationZeroDescent
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Presentation Prime Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PresentationPrimeLift

noncomputable section

/-! Maps from finitely presented algebras into a prime localization
extend to a principal neighborhood, including their coefficient compatibility. -/

open _root_.MvPolynomial

universe u v w
variable {B : Type u} [CommRing B] {A : Type v} [CommRing A] [Algebra B A]
variable (S : Type w) [CommRing S] [Algebra B S] [Algebra.FinitePresentation B S]
variable (p : Ideal A) [p.IsPrime]

theorem finitePresentation_prime_localization_lift (f : S →+* Localization.AtPrime p)
    (hf : ∀ b, f (algebraMap B S b) = algebraMap A (Localization.AtPrime p) (algebraMap B A b)) :
    ∃ (s : A) (hs : s ∉ p) (g : S →+* Localization.Away s),
      (∀ b, g (algebraMap B S b) = algebraMap A (Localization.Away s) (algebraMap B A b)) ∧
      (Principal.PrimeLocalization.principalToPrimeMap p s hs).comp g = f := by
  classical
  obtain ⟨n, q, hq, rel, hrel⟩ := Algebra.FinitePresentation.out (R := B) (A := S)
  have hqC (b : B) : q (C b) = algebraMap B S b := q.commutes b
  obtain ⟨s, hs, e, heB, he⟩ := Polynomial.PrimeLift.polynomial_prime_localization_lift p (f.comp q.toRingHom)
    (fun b => by change f (q (C b)) = _; rw [hqC]; exact hf b)
  have hz (r : rel) : Principal.PrimeLocalization.principalToPrimeMap p s hs (e r.val) = 0 := by
    have hr : q r.val = 0 := (show r.val ∈ RingHom.ker q.toRingHom from by
      rw [← hrel]
      exact Ideal.subset_span r.property)
    have h := RingHom.congr_fun he r.val
    exact h.trans ((congrArg f hr).trans (map_zero f))
  obtain ⟨t, ht, hzero⟩ := Principal.LocalizationZeroDescent.finite_principalLocalization_zero_descent p s hs (fun r : rel => e r.val) hz
  let e' := (Principal.LocalizationZeroDescent.principalRefinementMap s t).comp e
  have hker : RingHom.ker q.toRingHom ≤ RingHom.ker e' := by
    rw [← hrel]
    apply Ideal.span_le.mpr
    intro r hr
    exact hzero ⟨r, hr⟩
  let g : S →+* Localization.Away (s * t) := q.toRingHom.liftOfSurjective hq ⟨e', hker⟩
  have hst : s * t ∉ p := p.primeCompl.mul_mem hs ht
  have he' : (Principal.PrimeLocalization.principalToPrimeMap p (s * t) hst).comp e' = f.comp q.toRingHom := by
    dsimp only [e']
    rw [← RingHom.comp_assoc, Principal.LocalizationZeroDescent.principalRefinementMap_toPrime p s t hs ht]
    exact he
  refine ⟨s * t, hst, g, fun b => ?_, ?_⟩
  · rw [← hqC b]
    change q.toRingHom.liftOfSurjective hq ⟨e', hker⟩ (q.toRingHom (C b)) = _
    rw [RingHom.liftOfSurjective_comp_apply]
    change Principal.LocalizationZeroDescent.principalRefinementMap s t (e (C b)) = _
    rw [heB, Principal.LocalizationZeroDescent.principalRefinementMap_algebraMap]
  · apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := hq x
    change Principal.PrimeLocalization.principalToPrimeMap p (s * t) hst
      (q.toRingHom.liftOfSurjective hq ⟨e', hker⟩ (q.toRingHom x)) = f (q x)
    rw [RingHom.liftOfSurjective_comp_apply]
    exact RingHom.congr_fun he' x

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PresentationPrimeLift
