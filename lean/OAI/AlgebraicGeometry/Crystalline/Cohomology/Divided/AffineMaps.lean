import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.BaseChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Derivation

/-! # Affine Maps -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineMaps.DividedAffineMaps

noncomputable section

/-!
# Affine coordinate changes in relative free PD algebras

A PD coefficient map and translations in the target PD ideal determine
an actual PD map of free divided-power algebras. Coordinate derivatives
commute with these maps. This allows coordinate lifts to vary between
crystalline objects without imposing naturality on their primitives.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R S σ : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal S) (δ : DividedPowers I) (b : σ → S) (hb : ∀ i, b i ∈ I)

local notation "GR" => DividedPowerAlgebra R (σ →₀ R)
local notation "GS" => DividedPowerAlgebra S (σ →₀ S)
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal S σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers S σ I δ

def coordinate (i : σ) : GS := algebraMap S GS (b i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1 i

include hb in
theorem coordinate_mem (i : σ) : coordinate S σ b i ∈ J :=
  (J).add_mem (Ideal.subset_span (Or.inl ⟨⟨b i, hb i⟩, rfl⟩))
    (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem S σ I i 1 one_ne_zero)

def map : GR →ₐ[R] GS :=
  FreeRelative.Universal.FreeRelativeUniversal.lift R σ GS J γ (coordinate S σ b) (coordinate_mem S σ I b hb)

theorem map_coefficient (a : R) :
    map R S σ I δ b hb (algebraMap R GR a) = algebraMap S GS (algebraMap R S a) :=
  (map R S σ I δ b hb).commutes a

theorem map_generator (n : ℕ) (i : σ) :
    map R S σ I δ b hb (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = (γ).dpow n (coordinate S σ b i) :=
  FreeRelative.Universal.FreeRelativeUniversal.lift_generator R σ GS J γ (coordinate S σ b) (coordinate_mem S σ I b hb) n i

theorem map_coordinate (i : σ) :
    map R S σ I δ b hb (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = coordinate S σ b i := by
  rw [map_generator, (γ).dpow_one (coordinate_mem S σ I b hb i)]

include hb in
theorem map_isDPMorphism (IR : Ideal R) (δR : DividedPowers IR)
    (hbase : DividedPowers.IsDPMorphism δR δ (algebraMap R S)) :
    DividedPowers.IsDPMorphism (FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ IR δR) γ
      (map R S σ I δ b hb).toRingHom := by
  have hc : DividedPowers.IsDPMorphism δR γ (algebraMap R GS) := by
    have hd := (FreeRelative.Powers.FreeRelativePowers.base_isDPMorphism S σ I δ).comp _ hbase
    rw [← IsScalarTower.algebraMap_eq R S GS] at hd
    exact hd
  exact FreeRelative.Universal.FreeRelativeUniversal.lift_isDPMorphism R σ IR δR GS J γ hc
    (coordinate S σ b) (coordinate_mem S σ I b hb)

local notation "DR" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Derivation.FreeDividedDerivation.derivation R σ
local notation "DS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Derivation.FreeDividedDerivation.derivation S σ
local notation "f" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineMaps.DividedAffineMaps.map R S σ I δ b hb

theorem derivation_coordinate (i j : σ) [Decidable (j = i)] :
    DS i (coordinate S σ b j) = if j = i then 1 else 0 := by
  rw [coordinate, map_add, Derivation.map_algebraMap, zero_add, FreeDivided.Derivation.FreeDividedDerivation.derivation_coordinate]

theorem derivation_dpow (i : σ) (n : ℕ) (a : GS) (ha : a ∈ J) :
    DS i ((γ).dpow (n + 1) a) = (γ).dpow n a * DS i a := by
  have hd := FreeRelative.Derivation.FreeRelativeDerivation.derivation_dpow S σ I δ i n ha
  rw [FreeRelative.Derivation.FreeRelativeDerivation.derivation_eq_free] at hd
  exact hd

theorem derivation_generator (i j : σ) (n : ℕ) :
    DS i (f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n j)) = f (DR i (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n j)) := by
  classical
  rw [map_generator]
  cases n with
  | zero =>
    rw [(γ).dpow_zero (coordinate_mem S σ I b hb j), Derivation.map_one_eq_zero,
      FreeDivided.Derivation.FreeDividedDerivation.derivation_generator_zero, map_zero]
  | succ n =>
    rw [derivation_dpow S σ I δ i n _ (coordinate_mem S σ I b hb j),
      derivation_coordinate, FreeDivided.Derivation.FreeDividedDerivation.derivation_generator_succ]
    split_ifs <;> simp only [mul_one, mul_zero, map_zero, map_generator]

theorem derivation_monomial (i : σ) (d : σ →₀ ℕ) :
    DS i (f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) = f (DR i (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) := by
  classical
  have hp (s : Finset σ) : DS i (f (∏ j ∈ s, Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (d j) j)) =
      f (DR i (∏ j ∈ s, Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (d j) j)) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, map_one, Derivation.map_one_eq_zero, map_zero]
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, map_mul, (DS i).leibniz, (DR i).leibniz, map_add,
        ih, derivation_generator]
      simp only [smul_eq_mul, map_mul]
  exact hp d.support

/-- Coordinate derivatives commute with PD-ideal translations and arbitrary coefficient maps. -/
theorem derivation_naturality (i : σ) (a : GR) : DS i (f a) = f (DR i a) := by
  have he : ((DS i).toLinearMap.restrictScalars R).comp (f).toLinearMap =
      (f).toLinearMap.comp (DR i).toLinearMap := by
    apply LinearMap.ext_on (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
    rintro _ ⟨d, rfl⟩
    exact derivation_monomial R S σ I δ b hb i d
  exact LinearMap.congr_fun he a

theorem ringHom_ext_of_coordinate (IR : Ideal R) (δR : DividedPowers IR)
    (A : Type u) [CommRing A] (IA : Ideal A) (δA : DividedPowers IA)
    (g₁ g₂ : GR →+* A)
    (h₁ : DividedPowers.IsDPMorphism (FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ IR δR) δA g₁)
    (h₂ : DividedPowers.IsDPMorphism (FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ IR δR) δA g₂)
    (hc : ∀ r, g₁ (algebraMap R GR r) = g₂ (algebraMap R GR r))
    (hX : ∀ i, g₁ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = g₂ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) : g₁ = g₂ := by
  apply FreeRelative.BaseChange.FreeRelativeBaseChange.ringHom_ext R σ A g₁ g₂ hc
  intro n i
  rw [← FreeRelative.Powers.FreeRelativePowers.coordinate_dpow R σ IR δR n i,
    h₁.map_dpow (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ IR i 1 one_ne_zero),
    h₂.map_dpow (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ IR i 1 one_ne_zero), hX]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineMaps.DividedAffineMaps
