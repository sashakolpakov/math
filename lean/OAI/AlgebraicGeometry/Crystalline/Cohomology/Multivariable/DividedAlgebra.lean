import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Divided Algebra -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

noncomputable section

/-!
# Divided monomials in several variables

The actual divided-power algebra of a free module is spanned by its
divided monomials. Polynomial realization over a characteristic-zero
field will identify their coefficients.
-/

universe u

variable (R σ : Type u) [CommRing R]

local notation "G" => DividedPowerAlgebra R (σ →₀ R)

def generator (n : ℕ) (i : σ) : G := DividedPowerAlgebra.dp R n (Finsupp.single i (1 : R))

def monomial (d : σ →₀ ℕ) : G := d.prod (fun i n => generator R σ n i)

def fromCoefficients : ((σ →₀ ℕ) →₀ R) →ₗ[R] G := Finsupp.linearCombination R (MultivariableDividedAlgebra.monomial R σ)

theorem fromCoefficients_single (d : σ →₀ ℕ) (a : R) :
    fromCoefficients R σ (Finsupp.single d a) = a • MultivariableDividedAlgebra.monomial R σ d :=
  Finsupp.linearCombination_single R a d

theorem span_monomial_eq_top : Submodule.span R (Set.range (MultivariableDividedAlgebra.monomial R σ)) = ⊤ := by
  apply DividedPowerAlgebra.submodule_span_prod_dp_eq_top
  exact (Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R)).span_eq

theorem fromCoefficients_surjective : Function.Surjective (fromCoefficients R σ) := by
  rw [← LinearMap.range_eq_top, fromCoefficients, Finsupp.range_linearCombination]
  exact span_monomial_eq_top R σ

variable (K : Type u) [Field K] [CharZero K] [Algebra R K]

def variableMap : (σ →₀ R) →ₗ[R] MvPolynomial σ K :=
  Finsupp.linearCombination R (MvPolynomial.X : σ → MvPolynomial σ K)

def realize : G →ₐ[R] MvPolynomial σ K := by
  classical
  exact DividedPowerAlgebra.lift (DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal (MvPolynomial σ K)))
    (variableMap R σ K) (fun _ => Submodule.mem_top)

theorem realize_generator (n : ℕ) (i : σ) :
    realize R σ K (generator R σ n i) =
      (n.factorial : K)⁻¹ • (MvPolynomial.X i : MvPolynomial σ K) ^ n := by
  classical
  change DividedPowerAlgebra.lift _ _ _ (DividedPowerAlgebra.dp R n (Finsupp.single i (1 : R))) = _
  rw [DividedPowerAlgebra.lift_apply_dp]
  change (DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal (MvPolynomial σ K))).dpow n
    (Finsupp.linearCombination R (MvPolynomial.X : σ → MvPolynomial σ K) (Finsupp.single i (1 : R))) = _
  rw [Finsupp.linearCombination_single, one_smul]
  have h := DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul
    (⊤ : Ideal (MvPolynomial σ K))
    (DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal (MvPolynomial σ K)))
    (n := n) (x := MvPolynomial.X i) Submodule.mem_top
  refine h.trans ?_
  rw [MvPolynomial.X_pow_eq_monomial]
  ext d
  simp [MvPolynomial.coeff_monomial, Algebra.smul_def, Ring.inverse_eq_inv']

def weight (d : σ →₀ ℕ) : K := d.prod (fun _ n => (n.factorial : K)⁻¹)

theorem realize_monomial (d : σ →₀ ℕ) :
    realize R σ K (MultivariableDividedAlgebra.monomial R σ d) = MvPolynomial.monomial d (weight σ K d) := by
  classical
  simp only [MultivariableDividedAlgebra.monomial, Finsupp.prod, map_prod, realize_generator, Finset.prod_smul]
  rw [MvPolynomial.prod_X_pow_eq_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rfl

theorem weight_ne_zero (d : σ →₀ ℕ) : weight σ K d ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (d i)))

theorem coeff_realize_fromCoefficients (f : (σ →₀ ℕ) →₀ R) (d : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff ((realize R σ K (fromCoefficients R σ f))) (d) =
      algebraMap R K (f d) * weight σ K d := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul, hf, hg]
  | single e a =>
    rw [fromCoefficients_single, map_smul, realize_monomial]
    by_cases h : e = d
    · subst e
      simp [MvPolynomial.coeff_monomial, Algebra.smul_def]
    · simp [MvPolynomial.coeff_monomial, Algebra.smul_def, h, Ne.symm h]

variable (h : Function.Injective (algebraMap R K))

include h in
theorem fromCoefficients_injective : Function.Injective (fromCoefficients R σ) := by
  intro f g hfg
  ext d
  apply h
  apply mul_right_cancel₀ (weight_ne_zero σ K d)
  exact (coeff_realize_fromCoefficients R σ K f d).symm.trans
    ((congrArg (fun x => AddMonoidAlgebra.coeff ((realize R σ K x)) (d)) hfg).trans
      (coeff_realize_fromCoefficients R σ K g d))

/-- Unique divided-monomial coefficients in the actual multivariable algebra. -/
def coefficientEquiv : ((σ →₀ ℕ) →₀ R) ≃ₗ[R] G :=
  LinearEquiv.ofBijective (fromCoefficients R σ)
    ⟨fromCoefficients_injective R σ K h, fromCoefficients_surjective R σ⟩

include h in
theorem realize_injective : Function.Injective (realize R σ K) := by
  intro x y hxy
  obtain ⟨f, rfl⟩ := fromCoefficients_surjective R σ x
  obtain ⟨g, rfl⟩ := fromCoefficients_surjective R σ y
  apply congrArg (fromCoefficients R σ)
  ext d
  apply h
  apply mul_right_cancel₀ (weight_ne_zero σ K d)
  exact (coeff_realize_fromCoefficients R σ K f d).symm.trans
    ((congrArg ((fun p => AddMonoidAlgebra.coeff p (d))) hxy).trans (coeff_realize_fromCoefficients R σ K g d))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra
