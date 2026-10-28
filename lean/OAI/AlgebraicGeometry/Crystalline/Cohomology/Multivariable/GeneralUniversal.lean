import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.GeneralPowers

/-! # General Universal -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.GeneralUniversal.MultivariableGeneralUniversal

noncomputable section

/-!
# Universal property including proper augmentation ideals

Choosing target PD-ideal elements for all coordinates determines a unique
genuine PD algebra map. The target may have torsion.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I)
  (A : Type u) [CommRing A] [Algebra R A]
  (J : Ideal A) (ε : DividedPowers J)
  (hbase : DividedPowers.IsDPMorphism δ ε (algebraMap R A))
  (x : σ → A) (hx : ∀ i, x i ∈ J)

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.GeneralPowers.MultivariableGeneralPowers.dividedPowers R σ K h I δ

include hx in
theorem linearCombination_mem (a : σ →₀ R) : Finsupp.linearCombination R x a ∈ J := by
  classical
  change (∑ i ∈ a.support, a i • x i) ∈ J
  exact Submodule.sum_mem J (fun i _ => Submodule.smul_of_tower_mem J _ (hx i))

def lift : G →ₐ[R] A :=
  DividedPowerAlgebra.lift ε (Finsupp.linearCombination R x) (linearCombination_mem R σ A J x hx)

theorem lift_generator (n : ℕ) (i : σ) :
    MultivariableGeneralUniversal.lift R σ A J ε x hx (DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = ε.dpow n (x i) := by
  change DividedPowerAlgebra.lift _ _ _ (DividedPowerAlgebra.dp R n (Finsupp.single i (1 : R))) = _
  rw [DividedPowerAlgebra.lift_apply_dp, Finsupp.linearCombination_single, one_smul]

theorem lift_coordinate (i : σ) : MultivariableGeneralUniversal.lift R σ A J ε x hx (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = x i := by
  rw [lift_generator, ε.dpow_one (hx i)]

include hbase in
theorem lift_isDPMorphism : DividedPowers.IsDPMorphism γ ε (MultivariableGeneralUniversal.lift R σ A J ε x hx).toRingHom := by
  apply DividedPowers.IsDPMorphism.on_span γ ε
    (f := (MultivariableGeneralUniversal.lift R σ A J ε x hx).toRingHom) (S := Multivariable.DividedPowers.MultivariableDividedPowers.generators R σ I) rfl
  · intro a ha
    rcases ha with ⟨a, rfl⟩ | ⟨⟨n, i⟩, rfl⟩
    · change MultivariableGeneralUniversal.lift R σ A J ε x hx (algebraMap R G a) ∈ J
      rw [AlgHom.commutes]
      exact hbase.ideal_comp (Ideal.mem_map_of_mem _ a.property)
    · change MultivariableGeneralUniversal.lift R σ A J ε x hx (DividedAlgebra.MultivariableDividedAlgebra.generator R σ (n + 1) i) ∈ J
      rw [lift_generator]
      exact ε.dpow_mem (Nat.succ_ne_zero n) (hx i)
  · intro n a ha
    rcases ha with ⟨a, rfl⟩ | ⟨⟨m, i⟩, rfl⟩
    · have heq := (GeneralPowers.MultivariableGeneralPowers.base_isDPMorphism R σ K h I δ).dpow_comp
        (n := n) a a.property
      change MultivariableGeneralUniversal.lift R σ A J ε x hx ((γ).dpow n (algebraMap R G a)) =
        ε.dpow n (MultivariableGeneralUniversal.lift R σ A J ε x hx (algebraMap R G a))
      rw [heq, AlgHom.commutes, AlgHom.commutes]
      exact (hbase.dpow_comp a a.property).symm
    · change MultivariableGeneralUniversal.lift R σ A J ε x hx ((γ).dpow n (DividedAlgebra.MultivariableDividedAlgebra.generator R σ (m + 1) i)) =
        ε.dpow n (MultivariableGeneralUniversal.lift R σ A J ε x hx (DividedAlgebra.MultivariableDividedAlgebra.generator R σ (m + 1) i))
      rw [GeneralPowers.MultivariableGeneralPowers.generator_dpow, map_smul, lift_generator, lift_generator,
        ε.dpow_comp (Nat.succ_ne_zero m) (hx i), Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem lift_unique (g : G →ₐ[R] A) (hg : DividedPowers.IsDPMorphism γ ε g.toRingHom)
    (hX : ∀ i, g (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = x i) : g = MultivariableGeneralUniversal.lift R σ A J ε x hx := by
  classical
  have hgen (n : ℕ) (i : σ) : g (DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = MultivariableGeneralUniversal.lift R σ A J ε x hx (DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) := by
    rw [← GeneralPowers.MultivariableGeneralPowers.coordinate_dpow R σ K h I δ n i]
    have hgi : g ((γ).dpow n (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) = ε.dpow n (g (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) :=
      hg.map_dpow (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i 1 one_ne_zero)
    rw [hgi, hX, GeneralPowers.MultivariableGeneralPowers.coordinate_dpow, lift_generator]
  apply AlgHom.ext
  intro a
  obtain ⟨f, rfl⟩ := DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_surjective R σ a
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single d a =>
    rw [DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_single, map_smul, map_smul]
    congr 1
    change g (d.prod (fun i n => DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i)) =
      MultivariableGeneralUniversal.lift R σ A J ε x hx (d.prod (fun i n => DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i))
    simp only [Finsupp.prod, map_prod, hgen]

include hbase hx in
theorem existsUnique_lift : ∃! g : G →ₐ[R] A,
    DividedPowers.IsDPMorphism γ ε g.toRingHom ∧ ∀ i, g (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = x i := by
  refine ⟨MultivariableGeneralUniversal.lift R σ A J ε x hx, ⟨lift_isDPMorphism R σ K h I δ A J ε hbase x hx,
    lift_coordinate R σ A J ε x hx⟩, ?_⟩
  intro g hg
  exact lift_unique R σ K h I δ A J ε x hx g hg.1 hg.2

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.GeneralUniversal.MultivariableGeneralUniversal
