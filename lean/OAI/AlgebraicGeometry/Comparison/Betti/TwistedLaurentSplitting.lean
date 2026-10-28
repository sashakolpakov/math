import OAI.AlgebraicGeometry.Comparison.Betti.ParametricLaurentSplitting
import OAI.AlgebraicGeometry.Comparison.Betti.EntireMonomialDivision

/-! # Twisted Laurent Splitting -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TwistedLaurentSplitting.Dolbeault

noncomputable section

/-! Twisted Laurent splitting with holomorphic parameters and a finite
polynomial obstruction for negative twists. All operators are the actual
normalized contour projections and monomial-division operators. -/

open _root_.Complex Set _root_.Polynomial

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

def negativeTwistLaurentRemainder (G : P × ℂ → ℂ) (m : ℕ) : P → Polynomial ℂ :=
  EntireMonomialDivision.Dolbeault.entireMonomialRemainder (ParametricLaurentSplitting.Dolbeault.negativeLaurentFamily G) m

def negativeTwistLaurentQuotient (G : P × ℂ → ℂ) (m : ℕ) : P × ℂ → ℂ :=
  EntireMonomialDivision.Dolbeault.entireMonomialQuotient (ParametricLaurentSplitting.Dolbeault.negativeLaurentFamily G) m

theorem negativeTwistLaurentQuotient_holomorphic {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) (m : ℕ) :
    DifferentiableOn ℂ (negativeTwistLaurentQuotient G m) (S ×ˢ univ) :=
  EntireMonomialDivision.Dolbeault.entireMonomialQuotient_holomorphic hS (ParametricLaurentSplitting.Dolbeault.negativeLaurentFamily_holomorphic hS hG) m

theorem negativeTwistLaurentRemainder_coeff_holomorphic {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) (m k : ℕ) :
    DifferentiableOn ℂ (fun p => (negativeTwistLaurentRemainder G m p).coeff k) S :=
  (EntireMonomialDivision.Dolbeault.entireMonomial_local_division hS (ParametricLaurentSplitting.Dolbeault.negativeLaurentFamily_holomorphic hS hG) m).2.1 k

theorem negativeTwistLaurentRemainder_coeff_zero {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) (m : ℕ)
    {p : P} (hp : p ∈ S) (k : ℕ) (hk : m ≤ k) :
    (negativeTwistLaurentRemainder G m p).coeff k = 0 :=
  (EntireMonomialDivision.Dolbeault.entireMonomial_local_division hS (ParametricLaurentSplitting.Dolbeault.negativeLaurentFamily_holomorphic hS hG) m).2.2.1 p hp k hk

theorem negativeTwistLaurentRemainder_constant_zero {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) {m : ℕ} (hm : 0 < m)
    {p : P} (hp : p ∈ S) : (negativeTwistLaurentRemainder G m p).coeff 0 = 0 := by
  have h := EntireMonomialDivision.Dolbeault.entireMonomialDivision_identity hS (ParametricLaurentSplitting.Dolbeault.negativeLaurentFamily_holomorphic hS hG) m hp 0
  rw [coeff_zero_eq_eval_zero]
  simpa only [negativeTwistLaurentRemainder, ParametricLaurentSplitting.Dolbeault.negativeLaurentFamily, Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_zero,
    zero_pow (Nat.ne_of_gt hm), zero_mul, add_zero] using h.symm

theorem negativeTwistLaurentSplitting_identity {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) (m : ℕ)
    {p : P} (hp : p ∈ S) {z : ℂ} (hz : z ≠ 0) :
    G (p, z) = ParametricPositiveLaurent.Dolbeault.positiveLaurentFamily G (p, z) + (negativeTwistLaurentRemainder G m p).eval z⁻¹ +
      (z ^ m)⁻¹ * negativeTwistLaurentQuotient G m (p, z⁻¹) := by
  have h := ParametricLaurentSplitting.Dolbeault.parametricLaurentSplitting_identity G p hz
  rw [EntireMonomialDivision.Dolbeault.entireMonomialDivision_identity hS (ParametricLaurentSplitting.Dolbeault.negativeLaurentFamily_holomorphic hS hG) m hp z⁻¹] at h
  simpa only [negativeTwistLaurentRemainder, negativeTwistLaurentQuotient, inv_pow, add_assoc] using h.symm

def positiveTwistLaurentQuotient (G : P × ℂ → ℂ) (k : ℕ) (q : P × ℂ) : ℂ :=
  q.2 ^ k * ParametricLaurentSplitting.Dolbeault.negativeLaurentFamily G q

theorem positiveTwistLaurentQuotient_holomorphic {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) (k : ℕ) :
    DifferentiableOn ℂ (positiveTwistLaurentQuotient G k) (S ×ˢ univ) :=
  (differentiable_snd.pow k).differentiableOn.fun_mul (ParametricLaurentSplitting.Dolbeault.negativeLaurentFamily_holomorphic hS hG)

omit [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] in
theorem positiveTwistLaurentSplitting_identity (G : P × ℂ → ℂ) (k : ℕ) (p : P) {z : ℂ} (hz : z ≠ 0) :
    G (p, z) = ParametricPositiveLaurent.Dolbeault.positiveLaurentFamily G (p, z) + z ^ k * positiveTwistLaurentQuotient G k (p, z⁻¹) := by
  unfold positiveTwistLaurentQuotient
  rw [inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero k hz), one_mul]
  exact (ParametricLaurentSplitting.Dolbeault.parametricLaurentSplitting_identity G p hz).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.TwistedLaurentSplitting.Dolbeault
