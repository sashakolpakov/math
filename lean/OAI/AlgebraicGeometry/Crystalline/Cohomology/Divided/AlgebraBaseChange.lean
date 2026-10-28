import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction

/-! # Algebra Base Change -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraBaseChange.DividedAlgebraBaseChange

noncomputable section

/-!
# Coefficient base change for the actual free divided-power algebra

The defining divided-power relations give a ring map under arbitrary
coefficient extension. It carries each coordinate divided monomial to
the corresponding monomial. No characteristic or torsion assumption is
imposed on the new coefficient ring.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R S σ : Type u) [CommRing R] [CommRing S] [Algebra R S]

local notation "GR" => DividedPowerAlgebra R (σ →₀ R)
local notation "GS" => DividedPowerAlgebra S (σ →₀ S)

def moduleMap : (σ →₀ R) →ₗ[R] (σ →₀ S) :=
  Finsupp.mapRange.linearMap (Algebra.linearMap R S)

def map : GR →ₐ[R] GS :=
  DividedPowerAlgebra.lift' (f := fun nm => DividedPowerAlgebra.dp S nm.1 (moduleMap R S σ nm.2))
    (fun m => DividedPowerAlgebra.dp_zero)
    (fun n a m => by
      dsimp only
      rw [map_smul, ← algebraMap_smul S a (moduleMap R S σ m), DividedPowerAlgebra.dp_smul,
        ← map_pow, algebraMap_smul])
    (fun n m x => DividedPowerAlgebra.dp_mul)
    (fun n x y => by rw [map_add, DividedPowerAlgebra.dp_add])

theorem map_dp (n : ℕ) (m : σ →₀ R) :
    DividedAlgebraBaseChange.map R S σ (DividedPowerAlgebra.dp R n m) =
      DividedPowerAlgebra.dp S n (moduleMap R S σ m) :=
  DividedPowerAlgebra.lift'_apply_dp _ _ _ _ n m

theorem moduleMap_single (i : σ) (a : R) :
    moduleMap R S σ (Finsupp.single i a) = Finsupp.single i (algebraMap R S a) := by
  simp [moduleMap]

theorem map_generator (n : ℕ) (i : σ) :
    DividedAlgebraBaseChange.map R S σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ n i := by
  change DividedAlgebraBaseChange.map R S σ (DividedPowerAlgebra.dp R n (Finsupp.single i (1 : R))) = _
  rw [map_dp, moduleMap_single, map_one]
  rfl

theorem map_monomial (d : σ →₀ ℕ) :
    DividedAlgebraBaseChange.map R S σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial S σ d := by
  classical
  simp only [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial, Finsupp.prod, map_prod, map_generator]

theorem map_coefficient (a : R) :
    DividedAlgebraBaseChange.map R S σ (algebraMap R GR a) = algebraMap S GS (algebraMap R S a) :=
  (DividedAlgebraBaseChange.map R S σ).commutes a

theorem map_fromCoefficients (v : (σ →₀ ℕ) →₀ R) :
    DividedAlgebraBaseChange.map R S σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients R σ v) =
      Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients S σ (v.mapRange (algebraMap R S) (map_zero _)) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
    rw [Finsupp.mapRange_add (map_add (algebraMap R S))]
    simp only [map_add, hv, hw]
  | single d a =>
    rw [Finsupp.mapRange_single, Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_single, Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_single,
      map_smul, map_monomial, algebraMap_smul]

/-- Relations among coefficients vanish after extending them to the free PD algebra. -/
theorem coefficientIdeal_le_kernel (L : Ideal R) (hL : L ≤ RingHom.ker (algebraMap R S)) :
    L.map (algebraMap R GR) ≤ RingHom.ker (DividedAlgebraBaseChange.map R S σ).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change DividedAlgebraBaseChange.map R S σ (algebraMap R GR a) = 0
  rw [map_coefficient, show algebraMap R S a = 0 from hL ha, map_zero]

theorem augmentation_map (a : GR) :
    Multivariable.Reduction.MultivariableReduction.augmentation S σ (DividedAlgebraBaseChange.map R S σ a) =
      algebraMap R S (Multivariable.Reduction.MultivariableReduction.augmentation R σ a) := by
  have he : (((Multivariable.Reduction.MultivariableReduction.augmentation S σ).restrictScalars R).comp
      (DividedAlgebraBaseChange.map R S σ)).toLinearMap =
        ((Algebra.ofId R S).comp (Multivariable.Reduction.MultivariableReduction.augmentation R σ)).toLinearMap := by
    apply LinearMap.ext_on (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
    rintro _ ⟨d, rfl⟩
    change Multivariable.Reduction.MultivariableReduction.augmentation S σ (DividedAlgebraBaseChange.map R S σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) =
      algebraMap R S (Multivariable.Reduction.MultivariableReduction.augmentation R σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d))
    rw [map_monomial, Multivariable.Reduction.MultivariableReduction.augmentation_monomial,
      Multivariable.Reduction.MultivariableReduction.augmentation_monomial]
    split_ifs <;> simp only [map_one, map_zero]
  exact LinearMap.congr_fun he a

/-- Surjective coefficient maps induce surjections of the actual free divided-power algebras. -/
theorem map_surjective (hs : Function.Surjective (algebraMap R S)) :
    Function.Surjective (DividedAlgebraBaseChange.map R S σ) := by
  intro z
  obtain ⟨v, rfl⟩ := Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_surjective S σ z
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add v w hv hw =>
    obtain ⟨a, ha⟩ := hv
    obtain ⟨b, hb⟩ := hw
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  | single d a =>
    obtain ⟨b, rfl⟩ := hs a
    refine ⟨b • Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d, ?_⟩
    rw [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_single, map_smul, map_monomial, algebraMap_smul]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraBaseChange.DividedAlgebraBaseChange
