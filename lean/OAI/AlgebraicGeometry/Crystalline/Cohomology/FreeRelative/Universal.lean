import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers

/-! # Universal -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal.FreeRelativeUniversal

noncomputable section

/-!
# Universal property of the relative free PD algebra over arbitrary bases

Choosing target PD-ideal elements for all coordinates determines a unique
genuine PD algebra map. Both the base and target may have torsion.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ : Type u) [CommRing R]
  (I : Ideal R) (δ : DividedPowers I)
  (A : Type u) [CommRing A] [Algebra R A]
  (J : Ideal A) (ε : DividedPowers J)
  (hbase : DividedPowers.IsDPMorphism δ ε (algebraMap R A))
  (x : σ → A) (hx : ∀ i, x i ∈ J)

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ

include hx in
theorem linearCombination_mem (a : σ →₀ R) : Finsupp.linearCombination R x a ∈ J := by
  classical
  change (∑ i ∈ a.support, a i • x i) ∈ J
  exact Submodule.sum_mem J (fun i _ => Submodule.smul_of_tower_mem J _ (hx i))

def lift : G →ₐ[R] A :=
  DividedPowerAlgebra.lift ε (Finsupp.linearCombination R x) (linearCombination_mem R σ A J x hx)

theorem lift_generator (n : ℕ) (i : σ) :
    FreeRelativeUniversal.lift R σ A J ε x hx (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = ε.dpow n (x i) := by
  change DividedPowerAlgebra.lift _ _ _ (DividedPowerAlgebra.dp R n (Finsupp.single i (1 : R))) = _
  rw [DividedPowerAlgebra.lift_apply_dp, Finsupp.linearCombination_single, one_smul]

theorem lift_coordinate (i : σ) : FreeRelativeUniversal.lift R σ A J ε x hx (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = x i := by
  rw [lift_generator, ε.dpow_one (hx i)]

include hbase in
theorem lift_isDPMorphism : DividedPowers.IsDPMorphism γ ε (FreeRelativeUniversal.lift R σ A J ε x hx).toRingHom := by
  apply DividedPowers.IsDPMorphism.on_span γ ε
    (f := (FreeRelativeUniversal.lift R σ A J ε x hx).toRingHom) (S := Multivariable.DividedPowers.MultivariableDividedPowers.generators R σ I) rfl
  · intro a ha
    rcases ha with ⟨a, rfl⟩ | ⟨⟨n, i⟩, rfl⟩
    · change FreeRelativeUniversal.lift R σ A J ε x hx (algebraMap R G a) ∈ J
      rw [AlgHom.commutes]
      exact hbase.ideal_comp (Ideal.mem_map_of_mem _ a.property)
    · change FreeRelativeUniversal.lift R σ A J ε x hx (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (n + 1) i) ∈ J
      rw [lift_generator]
      exact ε.dpow_mem (Nat.succ_ne_zero n) (hx i)
  · intro n a ha
    rcases ha with ⟨a, rfl⟩ | ⟨⟨m, i⟩, rfl⟩
    · have heq := (Powers.FreeRelativePowers.base_isDPMorphism R σ I δ).dpow_comp
        (n := n) a a.property
      change FreeRelativeUniversal.lift R σ A J ε x hx ((γ).dpow n (algebraMap R G a)) =
        ε.dpow n (FreeRelativeUniversal.lift R σ A J ε x hx (algebraMap R G a))
      rw [heq, AlgHom.commutes, AlgHom.commutes]
      exact (hbase.dpow_comp a a.property).symm
    · change FreeRelativeUniversal.lift R σ A J ε x hx ((γ).dpow n (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (m + 1) i)) =
        ε.dpow n (FreeRelativeUniversal.lift R σ A J ε x hx (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (m + 1) i))
      rw [Powers.FreeRelativePowers.generator_dpow, map_smul, lift_generator, lift_generator,
        ε.dpow_comp (Nat.succ_ne_zero m) (hx i), Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem lift_unique (g : G →ₐ[R] A) (hg : DividedPowers.IsDPMorphism γ ε g.toRingHom)
    (hX : ∀ i, g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = x i) : g = FreeRelativeUniversal.lift R σ A J ε x hx := by
  classical
  have hgen (n : ℕ) (i : σ) : g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = FreeRelativeUniversal.lift R σ A J ε x hx (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) := by
    rw [← Powers.FreeRelativePowers.coordinate_dpow R σ I δ n i]
    have hgi : g ((γ).dpow n (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) = ε.dpow n (g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) :=
      hg.map_dpow (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i 1 one_ne_zero)
    rw [hgi, hX, Powers.FreeRelativePowers.coordinate_dpow, lift_generator]
  apply AlgHom.ext
  intro a
  obtain ⟨f, rfl⟩ := Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_surjective R σ a
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single d a =>
    rw [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_single, map_smul, map_smul]
    congr 1
    change g (d.prod (fun i n => Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i)) =
      FreeRelativeUniversal.lift R σ A J ε x hx (d.prod (fun i n => Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i))
    simp only [Finsupp.prod, map_prod, hgen]

include hbase hx in
theorem existsUnique_lift : ∃! g : G →ₐ[R] A,
    DividedPowers.IsDPMorphism γ ε g.toRingHom ∧ ∀ i, g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = x i := by
  refine ⟨FreeRelativeUniversal.lift R σ A J ε x hx, ⟨lift_isDPMorphism R σ I δ A J ε hbase x hx,
    lift_coordinate R σ A J ε x hx⟩, ?_⟩
  intro g hg
  exact lift_unique R σ I δ A J ε x hx g hg.1 hg.2

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal.FreeRelativeUniversal
