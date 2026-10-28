import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialUniversal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Poincare

/-! # Polynomial Reduction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialReduction.DividedPolynomialReduction

noncomputable section

/-!
# Reduction of the actual divided-polynomial algebra

Evaluation at the zero variable is an algebra map. After reducing its
constant coefficient modulo the base PD ideal, its kernel is exactly
the constructed relative PD ideal.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra

universe u

variable (R : Type u) [CommRing R]

local notation "G" => DividedPowerAlgebra R R

def augmentation : G →ₐ[R] R :=
  PolynomialUniversal.DividedPolynomialUniversal.lift R R ⊥ (dividedPowersBot R) 0 (Submodule.zero_mem _)

@[simp] theorem augmentation_monomial_succ (n : ℕ) : augmentation R (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (n + 1)) = 0 := by
  rw [augmentation, PolynomialUniversal.DividedPolynomialUniversal.lift_monomial,
    DividedPowers.dpow_eval_zero _ (Nat.succ_ne_zero n)]

@[simp] theorem augmentation_monomial_zero : augmentation R (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R 0) = 1 := by
  rw [PolynomialAlgebra.DividedPolynomialAlgebra.monomial, DividedPowerAlgebra.dp_zero, map_one]

theorem augmentation_fromCoefficients (a : Polynomial.DividedPolynomial.Coefficients R) :
    augmentation R (PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients R a) = a 0 := by
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add a b ha hb => simp only [map_add, ha, hb, Finsupp.add_apply]
  | single n c =>
    rw [PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients_single, map_smul]
    cases n with
    | zero => rw [augmentation_monomial_zero, smul_eq_mul, mul_one, Finsupp.single_eq_same]
    | succ n => simp [augmentation_monomial_succ]

variable (I : Ideal R)

def reduction : G →ₐ[R] (R ⧸ I) := (Ideal.Quotient.mkₐ R I).comp (augmentation R)

theorem reduction_surjective : Function.Surjective (reduction R I) := by
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨algebraMap R G a, (reduction R I).commutes a⟩

theorem ideal_le_kernel : PolynomialPowers.DividedPolynomialPowers.ideal R I ≤ RingHom.ker (reduction R I) := by
  apply Ideal.span_le.mpr
  intro a ha
  rcases ha with ⟨a, rfl⟩ | ⟨n, rfl⟩
  · change reduction R I (algebraMap R G a) = 0
    rw [AlgHom.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr a.property
  · change Ideal.Quotient.mk I (augmentation R (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (n + 1))) = 0
    rw [augmentation_monomial_succ, map_zero]

theorem subtract_constant_mem (a : G) :
    a - algebraMap R G (augmentation R a) ∈ PolynomialPowers.DividedPolynomialPowers.ideal R I := by
  obtain ⟨a, rfl⟩ := PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients_surjective R a
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero, sub_self, Submodule.zero_mem]
  | add a b ha hb =>
    simp only [map_add]
    rw [add_sub_add_comm]
    exact (PolynomialPowers.DividedPolynomialPowers.ideal R I).add_mem ha hb
  | single n c =>
    rw [PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients_single, map_smul]
    cases n with
    | zero =>
      rw [augmentation_monomial_zero, smul_eq_mul, mul_one, PolynomialAlgebra.DividedPolynomialAlgebra.monomial, DividedPowerAlgebra.dp_zero,
        Algebra.smul_def, mul_one, sub_self]
      exact Submodule.zero_mem _
    | succ n =>
      rw [augmentation_monomial_succ, smul_zero, map_zero, sub_zero]
      exact Submodule.smul_of_tower_mem _ c
        (PolynomialPowers.DividedPolynomialPowers.positive_monomial_mem R I (n + 1) (Nat.succ_ne_zero n))

theorem reduction_kernel : RingHom.ker (reduction R I) = PolynomialPowers.DividedPolynomialPowers.ideal R I := by
  apply le_antisymm _ (ideal_le_kernel R I)
  intro a ha
  have hc : augmentation R a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp ha
  have hm : algebraMap R G (augmentation R a) ∈ PolynomialPowers.DividedPolynomialPowers.ideal R I :=
    Ideal.subset_span (Or.inl ⟨⟨augmentation R a, hc⟩, rfl⟩)
  have hs := (PolynomialPowers.DividedPolynomialPowers.ideal R I).add_mem (subtract_constant_mem R I a) hm
  simpa only [sub_add_cancel] using hs

variable (K : Type u) [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))

theorem augmentation_eq_constantCoefficient :
    (augmentation R).toLinearMap = Polynomial.Poincare.PolynomialPoincare.constantCoefficient R K h := by
  apply LinearMap.ext
  intro a
  obtain ⟨a, rfl⟩ := PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients_surjective R a
  rw [AlgHom.toLinearMap_apply, augmentation_fromCoefficients]
  change a 0 = ((PolynomialAlgebra.DividedPolynomialAlgebra.coefficientEquiv R K h).symm ((PolynomialAlgebra.DividedPolynomialAlgebra.coefficientEquiv R K h) a)) 0
  rw [LinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialReduction.DividedPolynomialReduction
