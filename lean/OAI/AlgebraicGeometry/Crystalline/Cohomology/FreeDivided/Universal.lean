import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Powers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.GeneralUniversal

/-! # Universal -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Universal.FreeDividedUniversal

noncomputable section

/-!
# The free augmented PD algebra over an arbitrary coefficient ring

Assigning PD-ideal elements to the coordinates gives a unique PD algebra
map out of the actual free divided-power algebra. Neither the source nor
the target coefficient ring needs to be torsion-free.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (J : Ideal A) (δ : DividedPowers J) (x : σ → A) (hx : ∀ i, x i ∈ J)

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Powers.FreeDividedPowers.dividedPowers R σ

def lift : G →ₐ[R] A := Multivariable.GeneralUniversal.MultivariableGeneralUniversal.lift R σ A J δ x hx

theorem lift_generator (n : ℕ) (i : σ) : lift R σ A J δ x hx (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = δ.dpow n (x i) :=
  Multivariable.GeneralUniversal.MultivariableGeneralUniversal.lift_generator R σ A J δ x hx n i

theorem lift_coordinate (i : σ) : lift R σ A J δ x hx (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = x i := by
  rw [lift_generator, δ.dpow_one (hx i)]

theorem lift_isDPMorphism : DividedPowers.IsDPMorphism γ δ (lift R σ A J δ x hx).toRingHom := by
  apply DividedPowers.IsDPMorphism.on_span γ δ
    (S := Multivariable.DividedPowers.MultivariableDividedPowers.generators R σ (⊥ : Ideal R))
    (Multivariable.AugmentationPowers.MultivariableAugmentationPowers.augmentation_kernel R σ)
  · intro a ha
    rcases ha with ⟨a, rfl⟩ | ⟨⟨m, i⟩, rfl⟩
    · have ha : (a : R) = 0 := a.property
      change lift R σ A J δ x hx (algebraMap R G a) ∈ J
      rw [ha, map_zero, map_zero]
      exact J.zero_mem
    · change lift R σ A J δ x hx (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (m + 1) i) ∈ J
      rw [lift_generator]
      exact δ.dpow_mem (Nat.succ_ne_zero m) (hx i)
  · intro n a ha
    rcases ha with ⟨a, rfl⟩ | ⟨⟨m, i⟩, rfl⟩
    · have ha : (a : R) = 0 := a.property
      change lift R σ A J δ x hx ((γ).dpow n (algebraMap R G a)) =
        δ.dpow n (lift R σ A J δ x hx (algebraMap R G a))
      rw [ha, map_zero, map_zero]
      by_cases hn : n = 0
      · subst n
        rw [(γ).dpow_zero (Submodule.zero_mem _), δ.dpow_zero J.zero_mem, map_one]
      · rw [(γ).dpow_eval_zero hn, δ.dpow_eval_zero hn, map_zero]
    · change lift R σ A J δ x hx ((γ).dpow n (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (m + 1) i)) =
        δ.dpow n (lift R σ A J δ x hx (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (m + 1) i))
      rw [Powers.FreeDividedPowers.generator_dpow, map_smul, lift_generator, lift_generator,
        δ.dpow_comp (Nat.succ_ne_zero m) (hx i), Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem lift_unique (g : G →ₐ[R] A) (hg : DividedPowers.IsDPMorphism γ δ g.toRingHom)
    (hX : ∀ i, g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = x i) : g = lift R σ A J δ x hx := by
  classical
  have hgen (n : ℕ) (i : σ) : g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = lift R σ A J δ x hx (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) := by
    rw [← Powers.FreeDividedPowers.coordinate_dpow R σ n i]
    have hgi : g ((γ).dpow n (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) = δ.dpow n (g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) :=
      hg.map_dpow (Multivariable.AugmentationPowers.MultivariableAugmentationPowers.coordinate_mem R σ i)
    rw [hgi, hX, Powers.FreeDividedPowers.coordinate_dpow, lift_generator]
  apply AlgHom.ext
  intro a
  obtain ⟨v, rfl⟩ := Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_surjective R σ a
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single d a =>
    rw [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_single, map_smul, map_smul]
    congr 1
    simp only [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial, Finsupp.prod, map_prod, hgen]

include hx in
theorem existsUnique_lift : ∃! g : G →ₐ[R] A,
    DividedPowers.IsDPMorphism γ δ g.toRingHom ∧ ∀ i, g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = x i := by
  refine ⟨lift R σ A J δ x hx, ⟨lift_isDPMorphism R σ A J δ x hx,
    lift_coordinate R σ A J δ x hx⟩, ?_⟩
  intro g hg
  exact lift_unique R σ A J δ x hx g hg.1 hg.2

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Universal.FreeDividedUniversal
