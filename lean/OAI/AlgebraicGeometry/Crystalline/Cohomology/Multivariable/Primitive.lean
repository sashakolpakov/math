import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.CoordinateDerivation

/-! # Primitive -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Primitive.MultivariablePrimitive

noncomputable section

/-!
# Integral primitives in a divided-polynomial coordinate

Raising one divided exponent defines a linear primitive on the actual
multivariable algebra. The coordinate derivative of this primitive is
the identity, with all other coordinates retained as coefficients.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.CoordinateDerivation.MultivariableCoordinateDerivation

universe u

theorem derivation_prod_zero {S T ι : Type*} [CommRing S] [CommRing T] [Algebra S T]
    (D : Derivation S T T) (s : Finset ι) (f : ι → T) (hf : ∀ i ∈ s, D (f i) = 0) :
    D (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Derivation.map_one_eq_zero]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, D.leibniz, hf i (Finset.mem_insert_self i s),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)), smul_zero, smul_zero, add_zero]

variable (R σ K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.CoordinateDerivation.MultivariableCoordinateDerivation.derivation R σ K h I δ hunit
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.coefficientEquiv R σ K h

theorem derivation_generator_ne (i j : σ) (hji : j ≠ i) (n : ℕ) : D i (DividedAlgebra.MultivariableDividedAlgebra.generator R σ n j) = 0 := by
  classical
  cases n with
  | zero => exact CoordinateDerivation.MultivariableCoordinateDerivation.derivation_generator_zero R σ K h I δ hunit i j
  | succ n => simpa only [ite_eq_right hji] using CoordinateDerivation.MultivariableCoordinateDerivation.derivation_generator_succ R σ K h I δ hunit i j n

theorem derivation_monomial_zero (i : σ) (d : σ →₀ ℕ) (hi : d i = 0) : D i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = 0 := by
  classical
  apply derivation_prod_zero
  intro j hj
  have hji : j ≠ i := by
    intro hji
    subst j
    exact (Finsupp.mem_support_iff.mp hj) hi
  exact derivation_generator_ne R σ K h I δ hunit i j hji (d j)

theorem monomial_factor (i : σ) (d : σ →₀ ℕ) :
    DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d = DividedAlgebra.MultivariableDividedAlgebra.generator R σ (d i) i * DividedAlgebra.MultivariableDividedAlgebra.monomial R σ (d.erase i) := by
  exact (d.mul_prod_erase' i (fun i n => DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i)
    (fun _ => DividedPowerAlgebra.dp_zero)).symm

theorem derivation_monomial_raise (i : σ) (d : σ →₀ ℕ) :
    D i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ (d + Finsupp.single i 1)) = DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d := by
  classical
  rw [monomial_factor R σ i (d + Finsupp.single i 1)]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.erase_add, Finsupp.erase_single, add_zero]
  rw [(D i).leibniz, derivation_monomial_zero R σ K h I δ hunit i (d.erase i) Finsupp.erase_same,
    CoordinateDerivation.MultivariableCoordinateDerivation.derivation_generator_succ, ite_eq_left rfl, smul_zero, zero_add, smul_eq_mul,
    mul_comm, ← monomial_factor]

def primitiveCoefficients (i : σ) : ((σ →₀ ℕ) →₀ R) →ₗ[R] G :=
  Finsupp.linearCombination R (fun d => DividedAlgebra.MultivariableDividedAlgebra.monomial R σ (d + Finsupp.single i 1))

/-- Integration in one divided coordinate, retaining all other exponents. -/
def primitive (i : σ) : G →ₗ[R] G :=
  (primitiveCoefficients R σ i).comp (c).symm.toLinearMap

theorem coefficients_monomial (d : σ →₀ ℕ) : (c).symm (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = Finsupp.single d 1 := by
  apply (c).injective
  rw [LinearEquiv.apply_symm_apply]
  exact ((DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_single R σ d 1).trans (one_smul R _)).symm

theorem primitive_monomial (i : σ) (d : σ →₀ ℕ) :
    primitive R σ K h i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = DividedAlgebra.MultivariableDividedAlgebra.monomial R σ (d + Finsupp.single i 1) := by
  change primitiveCoefficients R σ i ((c).symm (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) = _
  rw [coefficients_monomial]
  exact (Finsupp.linearCombination_single R 1 d).trans (one_smul R _)

theorem derivation_primitive_linear (i : σ) :
    (D i).toLinearMap.comp (primitive R σ K h i) = LinearMap.id := by
  apply LinearMap.ext_on (DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
  rintro _ ⟨d, rfl⟩
  change D i (primitive R σ K h i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) = DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d
  rw [primitive_monomial, derivation_monomial_raise]

/-- The constructed coordinate primitive is a right inverse of the actual coordinate derivation. -/
theorem derivation_primitive (i : σ) (a : G) : D i (primitive R σ K h i a) = a :=
  LinearMap.congr_fun (derivation_primitive_linear R σ K h I δ hunit i) a

def projectionCoefficients (i : σ) : ((σ →₀ ℕ) →₀ R) →ₗ[R] G :=
  Finsupp.linearCombination R (fun d => if d i = 0 then DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d else 0)

/-- Keep precisely the terms constant in the chosen divided coordinate. -/
def projection (i : σ) : G →ₗ[R] G :=
  (projectionCoefficients R σ i).comp (c).symm.toLinearMap

theorem projection_monomial (i : σ) (d : σ →₀ ℕ) :
    projection R σ K h i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = if d i = 0 then DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d else 0 := by
  change projectionCoefficients R σ i ((c).symm (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) = _
  rw [coefficients_monomial]
  exact (Finsupp.linearCombination_single R 1 d).trans (one_smul R _)

theorem exists_predecessor (i : σ) (d : σ →₀ ℕ) (hi : d i ≠ 0) :
    ∃ s : σ →₀ ℕ, d = s + Finsupp.single i 1 := by
  classical
  have hle : Finsupp.single i 1 ≤ d := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Finsupp.single_eq_same] using Nat.one_le_iff_ne_zero.mpr hi
    · simp only [Finsupp.single_eq_of_ne hji, zero_le]
  exact ⟨d - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm⟩

theorem primitive_derivation_linear (i : σ) :
    (primitive R σ K h i).comp (D i).toLinearMap + projection R σ K h i = LinearMap.id := by
  apply LinearMap.ext_on (DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
  rintro _ ⟨d, rfl⟩
  change primitive R σ K h i (D i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) + projection R σ K h i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) =
    DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d
  rw [projection_monomial]
  by_cases hi : d i = 0
  · rw [ite_eq_left hi, derivation_monomial_zero R σ K h I δ hunit i d hi, map_zero, zero_add]
  · rw [ite_eq_right hi, add_zero]
    obtain ⟨s, rfl⟩ := exists_predecessor σ i d hi
    rw [derivation_monomial_raise, primitive_monomial]

/-- Integration recovers an element after subtracting its terms constant in this coordinate. -/
theorem primitive_derivation (i : σ) (a : G) :
    primitive R σ K h i (D i a) + projection R σ K h i a = a :=
  LinearMap.congr_fun (primitive_derivation_linear R σ K h I δ hunit i) a

theorem derivation_projection_linear (i : σ) :
    (D i).toLinearMap.comp (projection R σ K h i) = 0 := by
  apply LinearMap.ext_on (DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
  rintro _ ⟨d, rfl⟩
  change D i (projection R σ K h i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) = 0
  rw [projection_monomial]
  split_ifs with hi
  · exact derivation_monomial_zero R σ K h I δ hunit i d hi
  · exact map_zero _

theorem projection_primitive_linear (i : σ) :
    (projection R σ K h i).comp (primitive R σ K h i) = 0 := by
  apply LinearMap.ext_on (DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
  rintro _ ⟨d, rfl⟩
  change projection R σ K h i (primitive R σ K h i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) = 0
  rw [primitive_monomial, projection_monomial]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.add_one_ne_zero, ite_false]

theorem derivation_primitive_commute (i j : σ) (hij : i ≠ j) :
    (D j).toLinearMap.comp (primitive R σ K h i) =
      (primitive R σ K h i).comp (D j).toLinearMap := by
  classical
  apply LinearMap.ext_on (DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
  rintro _ ⟨d, rfl⟩
  change D j (primitive R σ K h i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) = primitive R σ K h i (D j (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d))
  rw [primitive_monomial]
  by_cases hd : d j = 0
  · have hraise : (d + Finsupp.single i 1 : σ →₀ ℕ) j = 0 := by
      simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hij.symm, hd, add_zero]
    rw [derivation_monomial_zero R σ K h I δ hunit j _ hraise,
      derivation_monomial_zero R σ K h I δ hunit j d hd, map_zero]
  · obtain ⟨s, rfl⟩ := exists_predecessor σ j d hd
    rw [derivation_monomial_raise, primitive_monomial]
    have he : (s + Finsupp.single j 1) + Finsupp.single i 1 =
        (s + Finsupp.single i 1) + Finsupp.single j 1 := by ac_rfl
    rw [he, derivation_monomial_raise]

theorem primitives_commute (i j : σ) :
    (primitive R σ K h i).comp (primitive R σ K h j) =
      (primitive R σ K h j).comp (primitive R σ K h i) := by
  apply LinearMap.ext_on (DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
  rintro _ ⟨d, rfl⟩
  change primitive R σ K h i (primitive R σ K h j (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) =
    primitive R σ K h j (primitive R σ K h i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d))
  rw [primitive_monomial, primitive_monomial, primitive_monomial, primitive_monomial]
  congr 1
  ac_rfl

theorem projection_idempotent (i : σ) (a : G) :
    projection R σ K h i (projection R σ K h i a) = projection R σ K h i a := by
  have he : (projection R σ K h i).comp (projection R σ K h i) = projection R σ K h i := by
    apply LinearMap.ext_on (DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
    rintro _ ⟨d, rfl⟩
    change projection R σ K h i (projection R σ K h i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) =
      projection R σ K h i (DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)
    rw [projection_monomial]
    split_ifs with hd
    · exact projection_monomial R σ K h i d |>.trans (ite_eq_left hd)
    · exact map_zero _
  exact LinearMap.congr_fun he a

theorem derivation_projection_commute (i j : σ) (hij : i ≠ j) (a : G) :
    D j (projection R σ K h i a) = projection R σ K h i (D j a) := by
  have h₁ := congrArg (D j) (primitive_derivation R σ K h I δ hunit i a)
  have h₂ := primitive_derivation R σ K h I δ hunit i (D j a)
  have hp : D j (primitive R σ K h i (D i a)) = primitive R σ K h i (D j (D i a)) :=
    LinearMap.congr_fun (derivation_primitive_commute R σ K h I δ hunit i j hij) (D i a)
  rw [map_add, hp, CoordinateDerivation.MultivariableCoordinateDerivation.derivations_commute R σ K h I δ hunit j i a] at h₁
  exact add_left_cancel (h₁.trans h₂.symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Primitive.MultivariablePrimitive
