import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.PrimeWeightUnits
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Primitive
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Multivariable Primitive -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariablePrimitive.PrimeMultivariablePrimitive

noncomputable section

/-!
# Integral partial integration in each ordinary polynomial coordinate

The primitive divides only by the coordinate weights prime to p.
Both residual projection identities hold, and the primitive commutes
with all other coordinate derivatives.
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W

def operator (v : (σ →₀ ℕ) → P) : P →ₗ[W] P :=
  (Finsupp.linearCombination W v).comp (AddMonoidAlgebra.coeffLinearEquiv W).toLinearMap

omit [CharP k p] in
theorem operator_monomial (v : (σ →₀ ℕ) → P) (d : σ →₀ ℕ) (a : W) :
    operator p k σ v (MvPolynomial.monomial d a) = a • v d := by
  change Finsupp.linearCombination W v (Finsupp.single d a) = a • v d
  exact Finsupp.linearCombination_single W a d

def primitive (i : σ) : P →ₗ[W] P :=
  operator p k σ (fun d => MvPolynomial.monomial (d + Finsupp.single i 1)
    (Witt.PrimeWeightUnits.WittPrimeWeightUnits.inverse p k (d i + 1)))

def projection (i : σ) (ε : ℕ) : P →ₗ[W] P :=
  operator p k σ (fun d => if p ∣ d i + ε then MvPolynomial.monomial d 1 else 0)

theorem primitive_monomial (i : σ) (d : σ →₀ ℕ) (a : W) :
    primitive p k σ i (MvPolynomial.monomial d a) = MvPolynomial.monomial (d + Finsupp.single i 1)
      (a * Witt.PrimeWeightUnits.WittPrimeWeightUnits.inverse p k (d i + 1)) := by
  rw [primitive, operator_monomial, MvPolynomial.smul_monomial, smul_eq_mul]

omit [CharP k p] in
theorem projection_monomial (i : σ) (ε : ℕ) (d : σ →₀ ℕ) (a : W) :
    projection p k σ i ε (MvPolynomial.monomial d a) =
      if p ∣ d i + ε then MvPolynomial.monomial d a else 0 := by
  rw [projection, operator_monomial]
  by_cases h : p ∣ d i + ε
  · simp [h, MvPolynomial.smul_monomial, smul_eq_mul]
  · simp [h]

theorem derivative_primitive (i : σ) :
    (MvPolynomial.pderiv i).toLinearMap.comp (primitive p k σ i) + projection p k σ i 1 = LinearMap.id := by
  classical
  apply MvPolynomial.linearMap_ext
  intro d
  apply LinearMap.ext
  intro a
  change MvPolynomial.pderiv i (primitive p k σ i (MvPolynomial.monomial d a)) +
    projection p k σ i 1 (MvPolynomial.monomial d a) = MvPolynomial.monomial d a
  rw [primitive_monomial, MvPolynomial.pderiv_monomial, add_tsub_cancel_right, projection_monomial]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
  rw [mul_assoc, ← Nat.cast_succ, Witt.PrimeWeightUnits.WittPrimeWeightUnits.inverse_mul]
  by_cases h : p ∣ d i + 1 <;> simp [h]

theorem primitive_derivative (i : σ) :
    (primitive p k σ i).comp (MvPolynomial.pderiv i).toLinearMap + projection p k σ i 0 = LinearMap.id := by
  classical
  apply MvPolynomial.linearMap_ext
  intro d
  apply LinearMap.ext
  intro a
  change primitive p k σ i (MvPolynomial.pderiv i (MvPolynomial.monomial d a)) +
    projection p k σ i 0 (MvPolynomial.monomial d a) = MvPolynomial.monomial d a
  by_cases hi : d i = 0
  · rw [MvPolynomial.pderiv_monomial, hi, Nat.cast_zero, mul_zero, map_zero, map_zero, zero_add,
      projection_monomial, hi, Nat.add_zero, ite_eq_left (dvd_zero p)]
  · obtain ⟨s, rfl⟩ := Multivariable.Primitive.MultivariablePrimitive.exists_predecessor σ i d hi
    rw [MvPolynomial.pderiv_monomial, add_tsub_cancel_right, primitive_monomial, projection_monomial]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one, Nat.add_zero]
    rw [mul_assoc, ← Nat.cast_succ, Witt.PrimeWeightUnits.WittPrimeWeightUnits.mul_inverse]
    by_cases h : p ∣ s i + 1 <;> simp [h]

theorem derivative_commutes (i j : σ) (hij : i ≠ j) :
    (MvPolynomial.pderiv j).toLinearMap.comp (primitive p k σ i) =
      (primitive p k σ i).comp (MvPolynomial.pderiv j).toLinearMap := by
  classical
  apply MvPolynomial.linearMap_ext
  intro d
  apply LinearMap.ext
  intro a
  change MvPolynomial.pderiv j (primitive p k σ i (MvPolynomial.monomial d a)) =
    primitive p k σ i (MvPolynomial.pderiv j (MvPolynomial.monomial d a))
  have hidx : (d + Finsupp.single i 1) - Finsupp.single j 1 =
      (d - Finsupp.single j 1) + Finsupp.single i 1 := by
    ext b
    rw [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.add_apply, Finsupp.tsub_apply]
    by_cases hb : b = i
    · subst b
      simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij, Nat.sub_zero]
    · simp only [Finsupp.single_eq_of_ne hb, add_zero]
  have hj : (d + Finsupp.single i 1 : σ →₀ ℕ) j = d j := by
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hij.symm, add_zero]
  have hi : (d - Finsupp.single j 1 : σ →₀ ℕ) i = d i := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hij, Nat.sub_zero]
  rw [primitive_monomial, MvPolynomial.pderiv_monomial, MvPolynomial.pderiv_monomial,
    primitive_monomial, hidx, hj, hi]
  congr 1
  ring

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariablePrimitive.PrimeMultivariablePrimitive
