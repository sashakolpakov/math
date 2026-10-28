import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Forms

/-! # Reduction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction

noncomputable section

/-!
# Reduction of the actual multivariable divided-power algebra

The augmentation sends all divided coordinates to zero. Its reduction
modulo the base ideal has exactly the constructed relative PD ideal as
kernel, providing the residual ring of the crystalline thickenings.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra Classical

universe u

variable (R σ : Type u) [CommRing R]

local notation "G" => DividedPowerAlgebra R (σ →₀ R)

def augmentation : G →ₐ[R] R :=
  DividedUniversal.MultivariableDividedUniversal.lift R σ R ⊥ (dividedPowersBot R) (fun _ => 0) (fun _ => Submodule.zero_mem _)

theorem augmentation_generator (n : ℕ) (i : σ) :
    augmentation R σ (DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = (dividedPowersBot R).dpow n 0 :=
  DividedUniversal.MultivariableDividedUniversal.lift_generator R σ R ⊥ (dividedPowersBot R) (fun _ => 0) _ n i

theorem exists_positive_coordinate (d : σ →₀ ℕ) (hd : d ≠ 0) : ∃ i, d i ≠ 0 := by
  by_contra hx
  apply hd
  apply Finsupp.ext
  intro i
  exact Classical.not_not.mp (fun hi => hx ⟨i, hi⟩)

theorem augmentation_monomial_nonzero (d : σ →₀ ℕ) (hd : d ≠ 0) :
    augmentation R σ (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = 0 := by
  obtain ⟨i, hi⟩ := exists_positive_coordinate σ d hd
  rw [Primitive.MultivariablePrimitive.monomial_factor R σ i d, map_mul,
    augmentation_generator, DividedPowers.dpow_eval_zero _ hi, zero_mul]

theorem augmentation_monomial (d : σ →₀ ℕ) :
    augmentation R σ (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = if d = 0 then 1 else 0 := by
  by_cases hd : d = 0
  · subst d
    rw [Constants.MultivariableConstants.monomial_zero, map_one, ite_eq_left rfl]
  · rw [augmentation_monomial_nonzero R σ d hd, ite_eq_right hd]

variable (I : Ideal R)

def reduction : G →ₐ[R] (R ⧸ I) := (Ideal.Quotient.mkₐ R I).comp (augmentation R σ)

theorem reduction_surjective : Function.Surjective (reduction R σ I) := by
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨algebraMap R G a, (reduction R σ I).commutes a⟩

theorem ideal_le_kernel : Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I ≤ RingHom.ker (reduction R σ I) := by
  apply Ideal.span_le.mpr
  intro a ha
  rcases ha with ⟨a, rfl⟩ | ⟨⟨n, i⟩, rfl⟩
  · change reduction R σ I (algebraMap R G a) = 0
    rw [AlgHom.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr a.property
  · change Ideal.Quotient.mk I (augmentation R σ (DividedAlgebra.MultivariableDividedAlgebra.generator R σ (n + 1) i)) = 0
    rw [augmentation_generator, DividedPowers.dpow_eval_zero _ (Nat.succ_ne_zero n), map_zero]

theorem monomial_mem (d : σ →₀ ℕ) (hd : d ≠ 0) : DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d ∈ Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I := by
  obtain ⟨i, hi⟩ := exists_positive_coordinate σ d hd
  rw [Primitive.MultivariablePrimitive.monomial_factor R σ i d]
  exact Ideal.mul_mem_right _ _ (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i (d i) hi)

theorem subtract_constant_mem (a : G) :
    a - algebraMap R G (augmentation R σ a) ∈ Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I := by
  obtain ⟨a, rfl⟩ := DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_surjective R σ a
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero, sub_self, Submodule.zero_mem]
  | add a b ha hb =>
    simp only [map_add]
    rw [add_sub_add_comm]
    exact (Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I).add_mem ha hb
  | single d c =>
    rw [DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_single, map_smul, augmentation_monomial]
    by_cases hd : d = 0
    · subst d
      rw [ite_eq_left rfl, Constants.MultivariableConstants.monomial_zero, smul_eq_mul, mul_one,
        Algebra.smul_def, mul_one, sub_self]
      exact Submodule.zero_mem _
    · rw [ite_eq_right hd, smul_zero, map_zero, sub_zero]
      exact Submodule.smul_of_tower_mem _ c (monomial_mem R σ I d hd)

theorem reduction_kernel : RingHom.ker (reduction R σ I) = Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I := by
  apply le_antisymm _ (ideal_le_kernel R σ I)
  intro a ha
  have hc : augmentation R σ a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp ha
  have hm : algebraMap R G (augmentation R σ a) ∈ Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I :=
    Ideal.subset_span (Or.inl ⟨⟨augmentation R σ a, hc⟩, rfl⟩)
  have hs := (Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I).add_mem (subtract_constant_mem R σ I a) hm
  simpa only [sub_add_cancel] using hs

variable (K : Type u) [Field K] [CharZero K] [Algebra R K] (h : Function.Injective (algebraMap R K))

theorem augmentation_eq_constantCoefficient :
    (augmentation R σ).toLinearMap = Constants.MultivariableConstants.constantCoefficient R σ K h := by
  apply LinearMap.ext_on (DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
  rintro _ ⟨d, rfl⟩
  exact (augmentation_monomial R σ d).trans (Constants.MultivariableConstants.constantCoefficient_monomial R σ K h d).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction
