import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InjectiveTransfer

/-! # General Powers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.GeneralPowers.MultivariableGeneralPowers

noncomputable section

/-!
# Relative multivariable divided powers without a unit in the base ideal

The polynomial realization only needs to take the source ideal into the
rational target ideal. Thus the construction also applies to the zero
base ideal and to the ordinary augmentation ideal of a free PD algebra.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ : Type u) [CommRing R]
  (K : Type u) [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I)

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "f" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.realize R σ K

/-- The actual relative PD structure, including for a zero base ideal. -/
def dividedPowers : DividedPowers IG :=
  PD.InjectiveTransfer.PDInjectiveTransfer.fromGenerators (⊤ : Ideal (MvPolynomial σ K))
    (Multivariable.DividedPowers.MultivariableDividedPowers.rationalPowers σ K) (f).toRingHom
    (Multivariable.DividedPowers.MultivariableDividedPowers.generators R σ I) le_top
    (Multivariable.DividedPowers.MultivariableDividedPowers.generator_lifts R σ K I δ) (DividedAlgebra.MultivariableDividedAlgebra.realize_injective R σ K h)

theorem realize_dpow (n : ℕ) {x : G} (hx : x ∈ IG) :
    f ((dividedPowers R σ K h I δ).dpow n x) =
      (Multivariable.DividedPowers.MultivariableDividedPowers.rationalPowers σ K).dpow n (f x) :=
  PD.InjectiveTransfer.PDInjectiveTransfer.fromGenerators_map_dpow (⊤ : Ideal (MvPolynomial σ K))
    (Multivariable.DividedPowers.MultivariableDividedPowers.rationalPowers σ K) (f).toRingHom
    (Multivariable.DividedPowers.MultivariableDividedPowers.generators R σ I) le_top
    (Multivariable.DividedPowers.MultivariableDividedPowers.generator_lifts R σ K I δ) (DividedAlgebra.MultivariableDividedAlgebra.realize_injective R σ K h) n hx

theorem base_isDPMorphism :
    DividedPowers.IsDPMorphism δ (dividedPowers R σ K h I δ) (algebraMap R G) where
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (fun x hx =>
    Ideal.subset_span (Or.inl ⟨⟨x, hx⟩, rfl⟩))
  dpow_comp {n} x hx := by
    apply DividedAlgebra.MultivariableDividedAlgebra.realize_injective R σ K h
    rw [realize_dpow R σ K h I δ n (Ideal.subset_span (Or.inl ⟨⟨x, hx⟩, rfl⟩))]
    exact (Multivariable.DividedPowers.MultivariableDividedPowers.base_dpow R σ K I δ n x hx).symm

theorem generator_dpow (n m : ℕ) (i : σ) :
    (dividedPowers R σ K h I δ).dpow n (DividedAlgebra.MultivariableDividedAlgebra.generator R σ (m + 1) i) =
      (Nat.uniformBell n (m + 1) : R) • DividedAlgebra.MultivariableDividedAlgebra.generator R σ (n * (m + 1)) i := by
  apply DividedAlgebra.MultivariableDividedAlgebra.realize_injective R σ K h
  rw [realize_dpow R σ K h I δ n
    (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i _ (Nat.succ_ne_zero m))]
  exact (Multivariable.DividedPowers.MultivariableDividedPowers.realize_generator_comp R σ K n m i).symm

theorem coordinate_dpow (n : ℕ) (i : σ) :
    (dividedPowers R σ K h I δ).dpow n (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i := by
  simpa only [Nat.zero_add, Nat.uniformBell_one_right, Nat.mul_one, Nat.cast_one, one_smul] using
    generator_dpow R σ K h I δ n 0 i

/-- This extends the previously constructed relative structure. -/
theorem eq_previous (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a)) :
    dividedPowers R σ K h I δ = Multivariable.DividedPowers.MultivariableDividedPowers.dividedPowers R σ K h I δ hunit := by
  apply DividedPowers.ext
  intro n x hx
  apply DividedAlgebra.MultivariableDividedAlgebra.realize_injective R σ K h
  rw [realize_dpow R σ K h I δ n hx,
    Multivariable.DividedPowers.MultivariableDividedPowers.realize_dpow R σ K h I δ hunit n hx]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.GeneralPowers.MultivariableGeneralPowers
