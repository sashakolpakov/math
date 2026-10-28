import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Primitive

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.BaseChange.FreeRelativeBaseChange

noncomputable section

/-!
# Functoriality of relative free divided powers and coordinate operators

A PD coefficient map induces a genuine PD map on the actual free divided
algebras. The coordinate derivatives and primitives commute with arbitrary
coefficient changes, including noninjective maps between torsion rings.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R S σ : Type u) [CommRing R] [CommRing S] [Algebra R S]

local notation "GR" => DividedPowerAlgebra R (σ →₀ R)
local notation "GS" => DividedPowerAlgebra S (σ →₀ S)
local notation "f" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map R S σ

theorem ringHom_ext (A : Type u) [CommRing A] (g₁ g₂ : GR →+* A)
    (hc : ∀ r, g₁ (algebraMap R GR r) = g₂ (algebraMap R GR r))
    (hg : ∀ n i, g₁ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = g₂ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i)) : g₁ = g₂ := by
  classical
  apply RingHom.ext
  intro a
  obtain ⟨v, rfl⟩ := Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_surjective R σ a
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | single d r =>
    rw [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.fromCoefficients_single, Algebra.smul_def, map_mul, map_mul, hc]
    congr 1
    simp only [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial, Finsupp.prod, map_prod, hg]

section DividedPowers

variable (IR : Ideal R) (δR : DividedPowers IR) (IS : Ideal S) (δS : DividedPowers IS)
  (hbase : DividedPowers.IsDPMorphism δR δS (algebraMap R S))

local notation "JR" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ IR
local notation "JS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal S σ IS
local notation "γR" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ IR δR
local notation "γS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers S σ IS δS

include hbase in
theorem map_isDPMorphism : DividedPowers.IsDPMorphism γR γS (f).toRingHom := by
  have hc : DividedPowers.IsDPMorphism δR γS (algebraMap R GS) := by
    have hd := (Powers.FreeRelativePowers.base_isDPMorphism S σ IS δS).comp _ hbase
    rw [← IsScalarTower.algebraMap_eq R S GS] at hd
    exact hd
  let g := Universal.FreeRelativeUniversal.lift R σ GS JS γS (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1)
    (fun i => Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem S σ IS i 1 one_ne_zero)
  have hg : DividedPowers.IsDPMorphism γR γS g.toRingHom :=
    Universal.FreeRelativeUniversal.lift_isDPMorphism R σ IR δR GS JS γS hc (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1)
      (fun i => Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem S σ IS i 1 one_ne_zero)
  have hgen (n : ℕ) (i : σ) : g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) := by
    change Universal.FreeRelativeUniversal.lift R σ GS JS γS _ _ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = _
    rw [Universal.FreeRelativeUniversal.lift_generator, Powers.FreeRelativePowers.coordinate_dpow,
      Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_generator]
  have he : g.toLinearMap = (f).toLinearMap := by
    apply LinearMap.ext_on (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
    rintro _ ⟨d, rfl⟩
    change g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)
    classical
    simp only [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial, Finsupp.prod, map_prod, hgen]
  have he' : g = f := AlgHom.ext (LinearMap.congr_fun he)
  rw [he'] at hg
  exact hg

end DividedPowers

local notation "DR" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Derivation.FreeDividedDerivation.derivation R σ
local notation "DS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Derivation.FreeDividedDerivation.derivation S σ

theorem derivation_generator (i j : σ) (n : ℕ) :
    DS i (f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n j)) = f (DR i (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n j)) := by
  classical
  rw [Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_generator]
  cases n with
  | zero => rw [FreeDivided.Derivation.FreeDividedDerivation.derivation_generator_zero,
      FreeDivided.Derivation.FreeDividedDerivation.derivation_generator_zero, map_zero]
  | succ n =>
    rw [FreeDivided.Derivation.FreeDividedDerivation.derivation_generator_succ, FreeDivided.Derivation.FreeDividedDerivation.derivation_generator_succ]
    split_ifs
    · exact (Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_generator R S σ n j).symm
    · exact (map_zero f).symm

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

/-- Actual coordinate derivatives commute with every coefficient map. -/
theorem derivation_naturality (i : σ) (a : GR) : DS i (f a) = f (DR i a) := by
  have he : ((DS i).toLinearMap.restrictScalars R).comp (f).toLinearMap =
      (f).toLinearMap.comp (DR i).toLinearMap := by
    apply LinearMap.ext_on (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
    rintro _ ⟨d, rfl⟩
    exact derivation_monomial R S σ i d
  exact LinearMap.congr_fun he a

/-- Actual integral coordinate primitives commute with every coefficient map. -/
theorem primitive_naturality (i : σ) (a : GR) :
    FreeDivided.Primitive.FreeDividedPrimitive.primitive S σ i (f a) = f (FreeDivided.Primitive.FreeDividedPrimitive.primitive R σ i a) := by
  have he : ((FreeDivided.Primitive.FreeDividedPrimitive.primitive S σ i).restrictScalars R).comp (f).toLinearMap =
      (f).toLinearMap.comp (FreeDivided.Primitive.FreeDividedPrimitive.primitive R σ i) := by
    apply LinearMap.ext_on (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
    rintro _ ⟨d, rfl⟩
    change FreeDivided.Primitive.FreeDividedPrimitive.primitive S σ i (f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) =
      f (FreeDivided.Primitive.FreeDividedPrimitive.primitive R σ i (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d))
    rw [Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_monomial, FreeDivided.Primitive.FreeDividedPrimitive.primitive_monomial,
      FreeDivided.Primitive.FreeDividedPrimitive.primitive_monomial, Divided.AlgebraBaseChange.DividedAlgebraBaseChange.map_monomial]
  exact LinearMap.congr_fun he a

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.BaseChange.FreeRelativeBaseChange
