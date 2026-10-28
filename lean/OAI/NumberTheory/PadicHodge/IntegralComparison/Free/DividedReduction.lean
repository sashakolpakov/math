import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Nilpotence
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Augmentation

/-! # Divided Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.DividedReduction

noncomputable section

/-!
# IntegralComparison: the reduction of the actual free divided-power coordinate algebra
-/

universe u

variable (T σ : Type u) [CommRing T] (I : Ideal T)

local notation "G" => DividedPowerAlgebra T (σ →₀ T)
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation T σ

def reduction : G →+* T ⧸ I := (Ideal.Quotient.mk I).comp (ε).toRingHom

theorem reduction_coefficient (a : T) : reduction T σ I (algebraMap T G a) = Ideal.Quotient.mk I a :=
  congrArg (Ideal.Quotient.mk I) ((ε).commutes a)

theorem reduction_surjective : Function.Surjective (reduction T σ I) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨algebraMap T G a, reduction_coefficient T σ I a⟩

theorem kernel_eq_ideal : RingHom.ker (reduction T σ I) = AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal T σ I := by
  ext x
  rw [AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Augmentation.FreeRelativeAugmentation.ideal_eq_comap]
  exact Ideal.Quotient.eq_zero_iff_mem

theorem reduction_generator (n : ℕ) (hn : n ≠ 0) (i : σ) :
    reduction T σ I (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator T σ n i) = 0 := by
  change Ideal.Quotient.mk I (ε (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator T σ n i)) = 0
  rw [AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation_generator, DividedPowers.dpow_eval_zero _ hn, map_zero]

theorem kernel_nil (p : ℕ) [Fact p.Prime] (δ : DividedPowers I) (hp : IsNilpotent (p : T))
    (x : G) (hx : reduction T σ I x = 0) : IsNilpotent x := by
  have hmem : x ∈ AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal T σ I := by
    rw [← kernel_eq_ideal]
    exact hx
  have hpG : IsNilpotent (p : G) := by
    simpa only [map_natCast] using hp.map (algebraMap T G)
  exact DividedPower.Nilpotence.nilpotent_of_mem
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers T σ I δ) p (Fact.out : p.Prime).pos hpG hmem

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.DividedReduction
