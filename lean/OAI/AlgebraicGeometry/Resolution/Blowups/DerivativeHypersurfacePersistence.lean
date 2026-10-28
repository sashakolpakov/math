import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialControlledTransform

/-! # Derivative Hypersurface Persistence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DerivativeHypersurfacePersistence.Construction

noncomputable section

/-! Persistence of derivative-defined coordinate hypersurfaces under controlled transforms. -/

open _root_.Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The usual formal derivative as a derivation over the coefficient ring. -/
def polynomialDerivation : Derivation R R[X] R[X] :=
  Derivation.mk' derivative (by
    intro p q
    rw [derivative_mul]
    change derivative p * q + p * derivative q = p * derivative q + q * derivative p
    ring)

/-- Repeated formal derivatives lower any ideal-power bound by at most
the number of differentiations. -/
theorem iteratedPolynomialDerivative_mem_pow (M : Ideal R[X]) (n k : ℕ)
    {p : R[X]} (hp : p ∈ M ^ (n + k)) : derivative^[k] p ∈ M ^ n := by
  induction k generalizing n with
  | zero => simpa using hp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    apply DifferentialOrder.Construction.derivation_mem_pow (polynomialDerivation (R := R)) M n
    apply ih (n + 1)
    simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hp

/-- A derivative that is a unit multiple of the coordinate forces every
point of the corresponding high-order locus onto that coordinate hypersurface. -/
theorem derivative_equation_forces_coordinate_mem (M : Ideal R[X]) (p : R[X])
    (b : ℕ) (u : R) (hu : IsUnit u)
    (hd : derivative^[b] p = C u * X) (hp : p ∈ M ^ (b + 1)) : X ∈ M := by
  have hder : derivative^[b] p ∈ M := by
    simpa only [pow_one] using iteratedPolynomialDerivative_mem_pow M 1 b
      (by simpa only [Nat.add_comm 1 b] using hp)
  rw [hd] at hder
  obtain ⟨v, hv⟩ := hu
  rw [← hv] at hder
  have h := M.mul_mem_left (C (v⁻¹ : Rˣ)) hder
  simpa only [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] using h

/-- If `D^b p = u z`, the same derivative equation holds after the control
`b+1` transform, with `u` mapped to the new coefficient ring. -/
theorem derivative_coordinate_equation_transforms (φ : R →+* S)
    (p : R[X]) (q : S[X]) (c : S) (hc : IsRegular c) (b : ℕ) (u : R)
    (hd : derivative^[b] p = C u * X)
    (h : (p.map φ).comp (C c * X) = C (c ^ (b + 1)) * q) :
    derivative^[b] q = C (φ u) * X := by
  have he := ResidualCoefficientTransform.Construction.iteratedDerivative_controlledTransform φ p q c (b + 1) b hc (by omega) h
  rw [hd, Polynomial.map_mul, map_C, map_X, mul_comp, C_comp, X_comp] at he
  simp only [Nat.add_sub_cancel_left, pow_one] at he
  apply (PolynomialControlledTransform.Construction.polynomial_C_regular c hc).left
  calc
    C c * derivative^[b] q = C (φ u) * (C c * X) := he.symm
    _ = C c * (C (φ u) * X) := by ring

/-- The transformed high-order locus remains in the transformed coordinate
hypersurface when the original coordinate has a unit derivative equation. -/
theorem derivative_coordinate_hypersurface_persists (φ : R →+* S)
    (p : R[X]) (q : S[X]) (c : S) (hc : IsRegular c) (b : ℕ) (u : R)
    (hu : IsUnit u) (hd : derivative^[b] p = C u * X)
    (h : (p.map φ).comp (C c * X) = C (c ^ (b + 1)) * q)
    (M : Ideal S[X]) (hq : q ∈ M ^ (b + 1)) : X ∈ M :=
  derivative_equation_forces_coordinate_mem M q b (φ u) (hu.map φ)
    (derivative_coordinate_equation_transforms φ p q c hc b u hd h) hq

/-- Transform existence on the actual coefficient chart yields persistence
without assuming a transformed polynomial in advance. -/
theorem blowupChart_derivative_coordinate_hypersurface_persists
    (I : Ideal R) (a : I) (p : R[X]) (b : ℕ) (u : R)
    (hu : IsUnit u) (hd : derivative^[b] p = C u * X)
    (hp : p ∈ Coefficient.Filtration.Construction.polynomialCenterIdeal I ^ (b + 1)) :
    ∃ q : (Blowup.Charts.Construction.blowupChart I a)[X],
      (p.map (Blowup.Charts.Construction.blowupChartConstants I a)).comp (C (Blowup.Charts.Construction.blowupChartConstants I a a.val) * X) =
        C ((Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ (b + 1)) * q ∧
      ∀ M : Ideal ((Blowup.Charts.Construction.blowupChart I a)[X]), q ∈ M ^ (b + 1) → X ∈ M := by
  obtain ⟨q, hq, _⟩ := PolynomialControlledTransform.Construction.blowupChart_existsUnique_polynomialControlledTransform I a p (b + 1) hp
  refine ⟨q, hq, ?_⟩
  intro M hM
  exact derivative_coordinate_hypersurface_persists (Blowup.Charts.Construction.blowupChartConstants I a) p q _
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a) b u hu hd hq M hM

/-- For a monic polynomial with vanishing next-to-leading coefficient, the
last nonconstant derivative is a factorial multiple of the variable. -/
theorem monic_zero_next_coefficient_derivative (p : R[X]) (b : ℕ)
    (hm : p.Monic) (hdeg : p.natDegree = b + 1) (hnext : p.coeff b = 0) :
    derivative^[b] p = C ((b + 1).factorial : R) * X := by
  ext j
  rw [coeff_iterate_derivative, coeff_C_mul, coeff_X]
  by_cases hj0 : j = 0
  · subst j
    simp [hnext]
  by_cases hj1 : j = 1
  · subst j
    have hcoeff : p.coeff (b + 1) = 1 := by
      rw [← hdeg]
      exact hm.coeff_natDegree
    have hfact : (b + 1).descFactorial b = (b + 1).factorial := by
      have h := Nat.factorial_mul_descFactorial (show b ≤ b + 1 by omega)
      simpa using h
    simp [Nat.add_comm 1 b, hcoeff, hfact]
  · have hcoeff : p.coeff (j + b) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hcoeff, Ne.symm hj1]

/-- Over a rational algebra, the factorial in the derivative equation is a unit. -/
theorem factorial_isUnit_of_rationalAlgebra [Algebra ℚ R] (b : ℕ) :
    IsUnit (b.factorial : R) := by
  have hQ : IsUnit (b.factorial : ℚ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b))
  simpa using hQ.map (algebraMap ℚ R)

/-- Monic equations with zero next-to-leading coefficient give an explicit
class of coordinate hypersurfaces whose contact with the high-order locus
persists under the controlled chart transformation. -/
theorem monic_coordinate_hypersurface_persists [Algebra ℚ R]
    (I : Ideal R) (a : I) (p : R[X]) (b : ℕ)
    (hm : p.Monic) (hdeg : p.natDegree = b + 1) (hnext : p.coeff b = 0)
    (hp : p ∈ Coefficient.Filtration.Construction.polynomialCenterIdeal I ^ (b + 1)) :
    ∃ q : (Blowup.Charts.Construction.blowupChart I a)[X],
      (p.map (Blowup.Charts.Construction.blowupChartConstants I a)).comp (C (Blowup.Charts.Construction.blowupChartConstants I a a.val) * X) =
        C ((Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ (b + 1)) * q ∧
      ∀ M : Ideal ((Blowup.Charts.Construction.blowupChart I a)[X]), q ∈ M ^ (b + 1) → X ∈ M :=
  blowupChart_derivative_coordinate_hypersurface_persists I a p b ((b + 1).factorial : R)
    (factorial_isUnit_of_rationalAlgebra (b + 1))
    (monic_zero_next_coefficient_derivative p b hm hdeg hnext) hp

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DerivativeHypersurfacePersistence.Construction
