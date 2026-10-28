import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal

/-! # Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Augmentation.FreeRelativeAugmentation

noncomputable section

/-! # The augmentation of the relative free PD algebra is a PD morphism -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ : Type u) [CommRing R] (I : Ideal R) (δ : DividedPowers I)

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation R σ
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ

theorem ideal_eq_comap : J = I.comap (ε).toRingHom :=
  RelativeDivided.RelativeDividedQuotient.ideal_eq_comap R σ I

theorem isDPMorphism : DividedPowers.IsDPMorphism γ δ (ε).toRingHom := by
  let f := Universal.FreeRelativeUniversal.lift R σ R I δ (fun _ => 0) (fun _ => I.zero_mem)
  have hf : DividedPowers.IsDPMorphism γ δ f.toRingHom :=
    Universal.FreeRelativeUniversal.lift_isDPMorphism R σ I δ R I δ
      (by
        rw [Algebra.algebraMap_self]
        exact (DividedPowers.DPMorphism.id δ).isDPMorphism)
      (fun _ => 0) (fun _ => I.zero_mem)
  have hg (n : ℕ) (i : σ) : f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = ε (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) := by
    change Universal.FreeRelativeUniversal.lift R σ R I δ _ _ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = _
    rw [Universal.FreeRelativeUniversal.lift_generator, Multivariable.Reduction.MultivariableReduction.augmentation_generator]
    by_cases hn : n = 0
    · subst n
      rw [δ.dpow_zero I.zero_mem, (dividedPowersBot R).dpow_zero (Submodule.zero_mem _)]
    · rw [δ.dpow_eval_zero hn, (dividedPowersBot R).dpow_eval_zero hn]
  have he : f.toLinearMap = (ε).toLinearMap := by
    apply LinearMap.ext_on (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
    rintro _ ⟨d, rfl⟩
    change f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = ε (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)
    classical
    simp only [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial, Finsupp.prod, map_prod, hg]
  have he' : f = ε := AlgHom.ext (LinearMap.congr_fun he)
  rw [he'] at hf
  exact hf

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Augmentation.FreeRelativeAugmentation
