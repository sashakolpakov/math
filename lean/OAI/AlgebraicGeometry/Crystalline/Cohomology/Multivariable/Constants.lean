import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Primitive

/-! # Constants -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Constants.MultivariableConstants

noncomputable section

/-!
# The constant part of the multivariable divided-power algebra

Composing every coordinate's coefficient projection retains exactly
the coefficient of the zero divided monomial.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Primitive.MultivariablePrimitive Classical

universe u

variable (R σ K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))

local notation "G" => DividedPowerAlgebra R (σ →₀ R)

def constantCoefficient : G →ₗ[R] R :=
  (Finsupp.lapply 0).comp (DividedAlgebra.MultivariableDividedAlgebra.coefficientEquiv R σ K h).symm.toLinearMap

def constants : R →ₗ[R] G := Algebra.linearMap R G

theorem monomial_zero : DividedAlgebra.MultivariableDividedAlgebra.monomial R σ 0 = 1 := by
  simp [DividedAlgebra.MultivariableDividedAlgebra.monomial]

theorem constantCoefficient_monomial (d : σ →₀ ℕ) :
    constantCoefficient R σ K h (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = if d = 0 then 1 else 0 := by
  change (DividedAlgebra.MultivariableDividedAlgebra.coefficientEquiv R σ K h).symm (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) 0 = _
  rw [Primitive.MultivariablePrimitive.coefficients_monomial]
  by_cases hd : d = 0
  · subst d
    simp only [Finsupp.single_eq_same, ite_true]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hd), ite_eq_right hd]

theorem constantCoefficient_one : constantCoefficient R σ K h 1 = 1 := by
  rw [← monomial_zero R σ, constantCoefficient_monomial, ite_eq_left rfl]

theorem constantCoefficient_constants :
    (constantCoefficient R σ K h).comp (constants R σ) = LinearMap.id := by
  apply LinearMap.ext
  intro r
  change constantCoefficient R σ K h (algebraMap R G r) = r
  rw [Algebra.algebraMap_eq_smul_one, map_smul, constantCoefficient_one, smul_eq_mul, mul_one]

def successive : List σ → Module.End R G
  | [] => LinearMap.id
  | i :: l => (successive l).comp (Primitive.MultivariablePrimitive.projection R σ K h i)

theorem successive_monomial (l : List σ) (d : σ →₀ ℕ) :
    MultivariableConstants.successive R σ K h l (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) =
      if ∀ i ∈ l, d i = 0 then DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d else 0 := by
  induction l with
  | nil => simp [MultivariableConstants.successive]
  | cons i l ih =>
    change MultivariableConstants.successive R σ K h l (Primitive.MultivariablePrimitive.projection R σ K h i _) = _
    rw [Primitive.MultivariablePrimitive.projection_monomial]
    by_cases hi : d i = 0
    · rw [ite_eq_left hi, ih]
      congr 1
      simp only [List.mem_cons, forall_eq_or_imp, hi, true_and]
    · rw [ite_eq_right hi, map_zero, ite_eq_right]
      exact fun hf => hi (hf i List.mem_cons_self)

theorem successive_eq_constants (l : List σ) (hl : ∀ i, i ∈ l) :
    MultivariableConstants.successive R σ K h l = (constants R σ).comp (constantCoefficient R σ K h) := by
  apply LinearMap.ext_on (DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
  rintro _ ⟨d, rfl⟩
  change MultivariableConstants.successive R σ K h l (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) =
    constants R σ (constantCoefficient R σ K h (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d))
  rw [successive_monomial, constantCoefficient_monomial]
  by_cases hd : d = 0
  · subst d
    rw [ite_eq_left (show ∀ i ∈ l, (0 : σ →₀ ℕ) i = 0 from fun _ _ => rfl),
      ite_eq_left rfl, monomial_zero]
    exact (map_one (algebraMap R G)).symm
  · have hn : ¬ ∀ i ∈ l, d i = 0 := fun hf => hd (Finsupp.ext (fun i => hf i (hl i)))
    rw [ite_eq_right hn, ite_eq_right hd, map_zero]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Constants.MultivariableConstants
