import Mathlib.RingTheory.Norm.Basic

/-! # Norm Characters Eq -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.NormCharactersEq.Construction.NormCharacters

noncomputable section

/-!
# CartierDuality: the norm calculation for finite-group exponents

An algebra automorphism preserves norms. If it multiplies a unit by a
base scalar, that scalar's power equal to the algebra rank is one.
-/

/-- The norm of a translated unit detects the finite-free rank exponent. -/
theorem scalar_pow_card_eq_one
    {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι]
    (b : Module.Basis ι R A) (e : A ≃ₐ[R] A)
    (c : R) (x : A) (hx : IsUnit x) (he : e x = algebraMap R A c * x) :
    c ^ Fintype.card ι = 1 := by
  have h := Algebra.norm_eq_of_algEquiv e x
  rw [he, map_mul, Algebra.norm_algebraMap_of_basis b] at h
  have hu : IsUnit (Algebra.norm R x) := hx.map (Algebra.norm R)
  apply hu.mul_right_cancel
  simpa only [one_mul] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.NormCharactersEq.Construction.NormCharacters
