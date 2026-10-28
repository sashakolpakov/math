import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialContraction

/-! # Polynomial Projection -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialProjection.PrimePolynomialProjection

noncomputable section

/-! # Residual polynomial projections and compatibility with coefficient Frobenius -/

open _root_.Polynomial

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialContraction.PrimePolynomialContraction

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]

local notation "W" => WittVector p k

omit [CharP k p] in
theorem projection_idempotent (ε : ℕ) :
    (PolynomialContraction.PrimePolynomialContraction.projection p k ε).comp (PolynomialContraction.PrimePolynomialContraction.projection p k ε) = PolynomialContraction.PrimePolynomialContraction.projection p k ε := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  change PolynomialContraction.PrimePolynomialContraction.projection p k ε (PolynomialContraction.PrimePolynomialContraction.projection p k ε (monomial n a)) = PolynomialContraction.PrimePolynomialContraction.projection p k ε (monomial n a)
  by_cases h : p ∣ n + ε
  · simp only [PolynomialContraction.PrimePolynomialContraction.projection_monomial, ite_eq_left h]
  · simp only [PolynomialContraction.PrimePolynomialContraction.projection_monomial, ite_eq_right h, map_zero]

theorem primitive_projection : (PolynomialContraction.PrimePolynomialContraction.primitive p k).comp (PolynomialContraction.PrimePolynomialContraction.projection p k 1) = 0 := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  change PolynomialContraction.PrimePolynomialContraction.primitive p k (PolynomialContraction.PrimePolynomialContraction.projection p k 1 (monomial n a)) = 0
  rw [PolynomialContraction.PrimePolynomialContraction.projection_monomial]
  by_cases h : p ∣ n + 1
  · rw [ite_eq_left h, PolynomialContraction.PrimePolynomialContraction.primitive_monomial]
    simp [Witt.PrimeWeightUnits.WittPrimeWeightUnits.inverse, h]
  · rw [ite_eq_right h, map_zero]

theorem projection_primitive : (PolynomialContraction.PrimePolynomialContraction.projection p k 0).comp (PolynomialContraction.PrimePolynomialContraction.primitive p k) = 0 := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  change PolynomialContraction.PrimePolynomialContraction.projection p k 0 (PolynomialContraction.PrimePolynomialContraction.primitive p k (monomial n a)) = 0
  rw [PolynomialContraction.PrimePolynomialContraction.primitive_monomial, PolynomialContraction.PrimePolynomialContraction.projection_monomial, Nat.add_zero]
  by_cases h : p ∣ n + 1
  · rw [ite_eq_left h]
    simp [Witt.PrimeWeightUnits.WittPrimeWeightUnits.inverse, h]
  · rw [ite_eq_right h]

theorem primitive_map (f : W →+* W) (a : W[X]) :
    PolynomialContraction.PrimePolynomialContraction.primitive p k (a.map f) = (PolynomialContraction.PrimePolynomialContraction.primitive p k a).map f := by
  induction a using Polynomial.induction_on' with
  | add a b ha hb => simp only [Polynomial.map_add, map_add, ha, hb]
  | monomial n a =>
    rw [Polynomial.map_monomial, PolynomialContraction.PrimePolynomialContraction.primitive_monomial, PolynomialContraction.PrimePolynomialContraction.primitive_monomial,
      Polynomial.map_monomial, f.map_mul, Witt.PrimeWeightUnits.WittPrimeWeightUnits.fixed]

omit [CharP k p] in
theorem projection_map (ε : ℕ) (f : W →+* W) (a : W[X]) :
    PolynomialContraction.PrimePolynomialContraction.projection p k ε (a.map f) = (PolynomialContraction.PrimePolynomialContraction.projection p k ε a).map f := by
  induction a using Polynomial.induction_on' with
  | add a b ha hb => simp only [Polynomial.map_add, map_add, ha, hb]
  | monomial n a =>
    rw [Polynomial.map_monomial, PolynomialContraction.PrimePolynomialContraction.projection_monomial, PolynomialContraction.PrimePolynomialContraction.projection_monomial]
    by_cases h : p ∣ n + ε
    · simp only [ite_eq_left h, Polynomial.map_monomial]
    · simp only [ite_eq_right h, Polynomial.map_zero]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialProjection.PrimePolynomialProjection
