import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SupportedExponentCompletion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialAlgebra

/-! # Monomial Fractions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.MonomialFractions

noncomputable section

/-! Unit denominator cancellation works over every commutative ring.
It identifies the balanced fractions with the normalized coordinates. -/
open scoped BigOperators Classical
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

theorem unitDenominator_fraction_eq {p q b f : R} (hp : IsUnit p) (hb : IsUnit b)
    (h : q * b = p * f) :
    q * (↑hp.unit⁻¹ : R) = f * (↑hb.unit⁻¹ : R) := by
  have hp' : p * (↑hp.unit⁻¹ : R) = 1 := by
    exact (congrArg (fun x : R => x * ↑hp.unit⁻¹) hp.unit_spec).symm.trans (Units.mul_inv hp.unit)
  have hb' : b * (↑hb.unit⁻¹ : R) = 1 := by
    exact (congrArg (fun x : R => x * ↑hb.unit⁻¹) hb.unit_spec).symm.trans (Units.mul_inv hb.unit)
  calc
    q * ↑hp.unit⁻¹ = (q * ↑hp.unit⁻¹) * (b * ↑hb.unit⁻¹) := by rw [hb', mul_one]
    _ = (q * b) * ↑hp.unit⁻¹ * ↑hb.unit⁻¹ := by ring
    _ = (p * f) * ↑hp.unit⁻¹ * ↑hb.unit⁻¹ := by rw [h]
    _ = f * (p * ↑hp.unit⁻¹) * ↑hb.unit⁻¹ := by ring
    _ = f * ↑hb.unit⁻¹ := by rw [hp', mul_one]

theorem exponentMonomial_isUnit_of_le {κ : Type v} [Fintype κ]
    (D : κ → R) {a b : κ → ℕ} (hab : b ≤ a) (ha : IsUnit (Balanced.MonomialAlgebra.exponentMonomial D a)) :
    IsUnit (Balanced.MonomialAlgebra.exponentMonomial D b) := by
  obtain ⟨c, hc⟩ := SupportedExponentCompletion.exponent_complement_of_le hab
  rw [← hc, Balanced.MonomialAlgebra.exponentMonomial_add] at ha
  exact isUnit_of_mul_isUnit_right ha

theorem completedMonomial_fraction_eq {κ : Type v} [Fintype κ]
    (D : κ → R) (a C b d : κ → ℕ) (hC : C + b = a)
    (ha : IsUnit (Balanced.MonomialAlgebra.exponentMonomial D a)) :
    ∃ hb : IsUnit (Balanced.MonomialAlgebra.exponentMonomial D b),
      Balanced.MonomialAlgebra.exponentMonomial D (C + d) * (↑ha.unit⁻¹ : R) =
        Balanced.MonomialAlgebra.exponentMonomial D d * (↑hb.unit⁻¹ : R) := by
  have hb : IsUnit (Balanced.MonomialAlgebra.exponentMonomial D b) := by
    rw [← hC, Balanced.MonomialAlgebra.exponentMonomial_add] at ha
    exact isUnit_of_mul_isUnit_right ha
  refine ⟨hb, unitDenominator_fraction_eq ha hb ?_⟩
  rw [← hC, Balanced.MonomialAlgebra.exponentMonomial_add, Balanced.MonomialAlgebra.exponentMonomial_add]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.MonomialFractions
