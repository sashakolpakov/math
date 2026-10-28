import OAI.Geometry.ComplexTorus.RiemannProjectivity.CharacterSeparationEq
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Affine Vanishing -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints

noncomputable section

/-! # RiemannProjectivity: the reduced affine coordinate algebra and its genuine points -/

open Set

variable {ι : Type*}

abbrev coordinateRing (S : Set (ι → ℂ)) := MvPolynomial ι ℂ ⧸ MvPolynomial.vanishingIdeal ℂ S

theorem vanishingIdeal_isRadical (S : Set (ι → ℂ)) : (MvPolynomial.vanishingIdeal ℂ S).IsRadical := by
  intro p hp x hx
  obtain ⟨k, hk⟩ := hp
  have h := hk x hx
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

instance isReduced (S : Set (ι → ℂ)) : IsReduced (coordinateRing S) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (vanishingIdeal_isRadical S)

def coordinates (S : Set (ι → ℂ)) (q : coordinateRing S →ₐ[ℂ] ℂ) : ι → ℂ :=
  fun i => q (Ideal.Quotient.mk _ (MvPolynomial.X i))

theorem eval_coordinates (S : Set (ι → ℂ)) (q : coordinateRing S →ₐ[ℂ] ℂ)
    (p : MvPolynomial ι ℂ) :
    MvPolynomial.eval (coordinates S q) p = q (Ideal.Quotient.mk _ p) := by
  have h : MvPolynomial.aeval (coordinates S q) = q.comp (Ideal.Quotient.mkₐ ℂ _) := by
    ext i
    simp [coordinates]
  exact congrArg (fun f : MvPolynomial ι ℂ →ₐ[ℂ] ℂ => f p) h

theorem coordinates_mem (S : Set (ι → ℂ))
    (hS : ∀ x, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ S, MvPolynomial.eval x p = 0) → x ∈ S)
    (q : coordinateRing S →ₐ[ℂ] ℂ) : coordinates S q ∈ S := by
  apply hS
  intro p hp
  rw [eval_coordinates, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints
