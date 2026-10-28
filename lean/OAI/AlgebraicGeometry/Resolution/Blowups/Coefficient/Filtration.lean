import Mathlib.RingTheory.Polynomial.Basic

/-! # Filtration -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.Filtration.Construction

noncomputable section

/-! Coefficient order along a center in a polynomial coefficient ring. -/

open _root_.Polynomial

variable {R : Type*} [CommSemiring R]

/-- Multiplication adds the control exponents in the coefficient inequalities. -/
theorem coeff_mul_mem_idealPower (I : Ideal R) (m n : ℕ) (p q : R[X])
    (hp : ∀ j, p.coeff j ∈ I ^ (m - j)) (hq : ∀ j, q.coeff j ∈ I ^ (n - j))
    (k : ℕ) : (p * q).coeff k ∈ I ^ (m + n - k) := by
  classical
  rw [coeff_mul]
  apply sum_mem
  rintro ⟨i, j⟩ hij
  have hij' := Finset.mem_antidiagonal.mp hij
  apply Ideal.pow_le_pow_right (show m + n - k ≤ (m - i) + (n - j) by omega)
  rw [pow_add]
  exact Ideal.mul_mem_mul (hp i) (hq j)

/-- The coefficient inequalities define an actual polynomial ideal. -/
def coefficientFiltration (I : Ideal R) (b : ℕ) : Ideal R[X] where
  carrier := {p | ∀ j, p.coeff j ∈ I ^ (b - j)}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq j
    simpa only [coeff_add] using Ideal.add_mem _ (hp j) (hq j)
  smul_mem' := by
    intro p q hq j
    change (p * q).coeff j ∈ I ^ (b - j)
    have hp : ∀ k, p.coeff k ∈ I ^ (0 - k) := by simp
    simpa only [zero_add] using coeff_mul_mem_idealPower I 0 b p q hp hq j

theorem coefficientFiltration_zero (I : Ideal R) : coefficientFiltration I 0 = ⊤ := by
  ext p
  simp [coefficientFiltration]

theorem coefficientFiltration_mul (I : Ideal R) (m n : ℕ) :
    coefficientFiltration I m * coefficientFiltration I n ≤ coefficientFiltration I (m + n) := by
  apply Ideal.mul_le.mpr
  intro p hp q hq k
  exact coeff_mul_mem_idealPower I m n p q hp hq k

/-- The center obtained by adjoining the distinguished variable to `I`. -/
def polynomialCenterIdeal (I : Ideal R) : Ideal R[X] :=
  I.map C ⊔ Ideal.span {X}

theorem polynomialCenterIdeal_le_coefficientFiltration (I : Ideal R) :
    polynomialCenterIdeal I ≤ coefficientFiltration I 1 := by
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr j
    by_cases hj : j = 0
    · subst j
      simpa using hr
    · simp [coeff_C, hj]
  · rw [Ideal.span_singleton_le_iff_mem]
    intro j
    by_cases hj : j = 1
    · subst j
      simp
    · simp [coeff_X, Ne.symm hj]

theorem polynomialCenterIdeal_pow_le_coefficientFiltration (I : Ideal R) (b : ℕ) :
    polynomialCenterIdeal I ^ b ≤ coefficientFiltration I b := by
  induction b with
  | zero => rw [pow_zero, coefficientFiltration_zero, Ideal.one_eq_top]
  | succ b ih =>
    rw [pow_succ]
    exact (mul_le_mul' ih (polynomialCenterIdeal_le_coefficientFiltration I)).trans
      (coefficientFiltration_mul I b 1)

/-- Each coefficient term satisfying its expected order belongs to the
corresponding power of the center. -/
theorem coefficient_term_mem_centerPower (I : Ideal R) (b j : ℕ) (r : R)
    (hr : r ∈ I ^ (b - j)) : C r * X ^ j ∈ polynomialCenterIdeal I ^ b := by
  have hc : C r ∈ polynomialCenterIdeal I ^ (b - j) := by
    apply pow_le_pow_left' (show I.map C ≤ polynomialCenterIdeal I from le_sup_left)
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem C hr
  have hx : X ^ j ∈ polynomialCenterIdeal I ^ j :=
    Ideal.pow_mem_pow
      ((show Ideal.span {X} ≤ polynomialCenterIdeal I from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton X))) j
  apply Ideal.pow_le_pow_right (show b ≤ (b - j) + j by omega)
  rw [pow_add]
  exact Ideal.mul_mem_mul hc hx

/-- Polynomial order along the center `(I,z)` is completely determined by
the orders of the coefficients along `I`. -/
theorem polynomialCenterIdeal_pow_eq_coefficientFiltration (I : Ideal R) (b : ℕ) :
    polynomialCenterIdeal I ^ b = coefficientFiltration I b := by
  apply le_antisymm (polynomialCenterIdeal_pow_le_coefficientFiltration I b)
  intro p hp
  rw [← p.sum_monomial_eq]
  apply sum_mem
  intro j _
  change monomial j (p.coeff j) ∈ polynomialCenterIdeal I ^ b
  rw [← C_mul_X_pow_eq_monomial]
  exact coefficient_term_mem_centerPower I b j (p.coeff j) (hp j)

theorem polynomial_mem_centerPower_iff (I : Ideal R) (b : ℕ) (p : R[X]) :
    p ∈ polynomialCenterIdeal I ^ b ↔ ∀ j, p.coeff j ∈ I ^ (b - j) := by
  rw [polynomialCenterIdeal_pow_eq_coefficientFiltration]
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.Filtration.Construction
