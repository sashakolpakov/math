import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialOneForms

/-! # Polynomial Universal -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialUniversal.DividedPolynomialUniversal

noncomputable section

/-!
# Universal property of the actual relative divided-polynomial algebra

A chosen element of a target PD ideal determines a unique morphism from
the rank-one divided-polynomial algebra, compatible with the base divided
powers. This upgrades the weak algebraic lift to a genuine PD universal property.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra

universe u

variable (R K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))
  (A : Type u) [CommRing A] [Algebra R A]
  (J : Ideal A) (ε : DividedPowers J)
  (hbase : DividedPowers.IsDPMorphism δ ε (algebraMap R A))
  (x : A) (hx : x ∈ J)

local notation "G" => DividedPowerAlgebra R R
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.ideal R I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.dividedPowers R K h I δ hunit
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra.monomial R 1

/-- Send the variable to the chosen element of the target PD ideal. -/
def lift : G →ₐ[R] A :=
  DividedPowerAlgebra.lift ε (LinearMap.smulRight (LinearMap.id : R →ₗ[R] R) x)
    (fun a => Submodule.smul_of_tower_mem J a hx)

@[simp] theorem lift_monomial (n : ℕ) : DividedPolynomialUniversal.lift R A J ε x hx (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R n) = ε.dpow n x := by
  exact (DividedPowerAlgebra.lift_apply_dp ε
    (g := LinearMap.smulRight (LinearMap.id : R →ₗ[R] R) x)
    (fun a => Submodule.smul_of_tower_mem J a hx) n (1 : R)).trans
      (congrArg (ε.dpow n) (one_smul R x))

@[simp] theorem lift_variable : DividedPolynomialUniversal.lift R A J ε x hx X = x := by
  rw [lift_monomial, ε.dpow_one hx]

include hbase in
theorem lift_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (DividedPolynomialUniversal.lift R A J ε x hx).toRingHom := by
  apply DividedPowers.IsDPMorphism.on_span γ ε
    (f := (DividedPolynomialUniversal.lift R A J ε x hx).toRingHom) (S := PolynomialPowers.DividedPolynomialPowers.generators R I) rfl
  · intro a ha
    rcases ha with ⟨a, rfl⟩ | ⟨n, rfl⟩
    · change DividedPolynomialUniversal.lift R A J ε x hx (algebraMap R G a) ∈ J
      rw [AlgHom.commutes]
      exact hbase.ideal_comp (Ideal.mem_map_of_mem _ a.property)
    · change DividedPolynomialUniversal.lift R A J ε x hx (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (n + 1)) ∈ J
      rw [lift_monomial]
      exact ε.dpow_mem (Nat.succ_ne_zero n) hx
  · intro n a ha
    rcases ha with ⟨a, rfl⟩ | ⟨m, rfl⟩
    · have heq := (PolynomialPowers.DividedPolynomialPowers.base_isDPMorphism R K h I δ hunit).dpow_comp (n := n) a a.property
      change DividedPolynomialUniversal.lift R A J ε x hx ((γ).dpow n (algebraMap R G a)) =
        ε.dpow n (DividedPolynomialUniversal.lift R A J ε x hx (algebraMap R G a))
      rw [heq, AlgHom.commutes, AlgHom.commutes]
      exact (hbase.dpow_comp a a.property).symm
    · change DividedPolynomialUniversal.lift R A J ε x hx ((γ).dpow n (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (m + 1))) =
        ε.dpow n (DividedPolynomialUniversal.lift R A J ε x hx (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (m + 1)))
      rw [PolynomialPowers.DividedPolynomialPowers.monomial_dpow, map_smul, lift_monomial, lift_monomial,
        ε.dpow_comp (Nat.succ_ne_zero m) hx, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem lift_unique (g : G →ₐ[R] A) (hg : DividedPowers.IsDPMorphism γ ε g.toRingHom)
    (hX : g X = x) : g = DividedPolynomialUniversal.lift R A J ε x hx := by
  apply DividedPowerAlgebra.algHom_ext
  intro n a
  rw [PolynomialAlgebra.DividedPolynomialAlgebra.dp_eq_smul, map_smul, map_smul,
    ← PolynomialOneForms.DividedPolynomialOneForms.variable_dpow R K h I δ hunit n]
  have hg' : g ((γ).dpow n X) = ε.dpow n (g X) :=
    hg.map_dpow (PolynomialOneForms.DividedPolynomialOneForms.variable_mem R I)
  rw [hg', hX, PolynomialOneForms.DividedPolynomialOneForms.variable_dpow, lift_monomial]

include hbase hx in
/-- The full rank-one relative PD universal property, including uniqueness. -/
theorem existsUnique_lift : ∃! g : G →ₐ[R] A,
    DividedPowers.IsDPMorphism γ ε g.toRingHom ∧ g X = x := by
  refine ⟨DividedPolynomialUniversal.lift R A J ε x hx, ⟨lift_isDPMorphism R K h I δ hunit A J ε hbase x hx,
    lift_variable R A J ε x hx⟩, ?_⟩
  intro g hg
  exact lift_unique R K h I δ hunit A J ε x hx g hg.1 hg.2

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialUniversal.DividedPolynomialUniversal
