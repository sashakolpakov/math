import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableThickening
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Tower

/-! # Multivariable Tower -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTower.WittMultivariableTower

noncomputable section

/-! # The actual multivariable Witt crystalline inverse system -/

open _root_.CategoryTheory Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "K" => FractionRing W
local notation "I" => Ideal.span {(p : W)}
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "h" => IsFractionRing.injective W K
local notation "unit" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.base_unit p k
local notation "G" => DividedPowerAlgebra W (σ →₀ W)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal W σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.dividedPowers W σ K h I δ unit
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableThickening.WittMultivariableThickening.thickening p k σ
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.baseIdeal p k
local notation "subDP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.baseIdeal_subDP p k
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableThickening.WittMultivariableThickening.quotient p k σ

theorem quotient_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism γ (S n).dividedPowers (q n).toRingHom where
  ideal_comp := by
    change (IG).map (q n).toRingHom ≤ RingHom.ker (MultivariableThickening.WittMultivariableThickening.reduction p k σ n)
    rw [MultivariableThickening.WittMultivariableThickening.reduction_kernel]
    exact le_rfl
  dpow_comp x hx :=
    (QuotientMultivariableD.QuotientMultivariableForms.quotient_isDPMorphism W σ K h I δ unit (L n) (subDP n)).dpow_comp x hx

def transitionHom (n m : ℕ) (hnm : n ≤ m) :
    MultivariableThickening.WittMultivariableThickening.Ring p k σ m →ₐ[W] MultivariableThickening.WittMultivariableThickening.Ring p k σ n :=
  QuotientMultivariableTo.QuotientMultivariableTransitions.transition W σ (L n) (L m) (WittPolynomial.Tower.WittPolynomialTower.baseIdeal_antitone p k hnm)

omit [CharP k p] [PerfectRing k p] in
theorem transitionHom_quotient (n m : ℕ) (hnm : n ≤ m) (a : G) :
    transitionHom p k σ n m hnm (q m a) = q n a := rfl

theorem transitionHom_isDPMorphism (n m : ℕ) (hnm : n ≤ m) :
    DividedPowers.IsDPMorphism (S m).dividedPowers (S n).dividedPowers
      (transitionHom p k σ n m hnm).toRingHom where
  ideal_comp := by
    change (RingHom.ker (MultivariableThickening.WittMultivariableThickening.reduction p k σ m)).map _ ≤
      RingHom.ker (MultivariableThickening.WittMultivariableThickening.reduction p k σ n)
    rw [MultivariableThickening.WittMultivariableThickening.reduction_kernel, MultivariableThickening.WittMultivariableThickening.reduction_kernel]
    exact (QuotientMultivariableTo.QuotientMultivariableTransitions.transition_isDPMorphism W σ K h I δ unit (L n) (L m)
      (subDP n) (subDP m) (WittPolynomial.Tower.WittPolynomialTower.baseIdeal_antitone p k hnm)).ideal_comp
  dpow_comp x hx := by
    have hx' : x ∈ QuotientMultivariableD.QuotientMultivariableForms.ideal W σ I (L m) :=
      MultivariableThickening.WittMultivariableThickening.reduction_kernel p k σ m ▸ hx
    exact (QuotientMultivariableTo.QuotientMultivariableTransitions.transition_isDPMorphism W σ K h I δ unit (L n) (L m)
      (subDP n) (subDP m) (WittPolynomial.Tower.WittPolynomialTower.baseIdeal_antitone p k hnm)).dpow_comp x hx'

theorem transitionHom_reduction (n m : ℕ) (hnm : n ≤ m) :
    (MultivariableThickening.WittMultivariableThickening.reduction p k σ n).comp (transitionHom p k σ n m hnm).toRingHom =
      MultivariableThickening.WittMultivariableThickening.reduction p k σ m := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change MultivariableThickening.WittMultivariableThickening.reduction p k σ n (transitionHom p k σ n m hnm (q m a)) =
    MultivariableThickening.WittMultivariableThickening.reduction p k σ m (q m a)
  rw [transitionHom_quotient, MultivariableThickening.WittMultivariableThickening.reduction_quotient,
    MultivariableThickening.WittMultivariableThickening.reduction_quotient]

def transition (n m : ℕ) (hnm : n ≤ m) : S m ⟶ S n where
  hom := transitionHom p k σ n m hnm
  reduction_comp := transitionHom_reduction p k σ n m hnm
  dp_comp := transitionHom_isDPMorphism p k σ n m hnm

omit [CharP k p] [PerfectRing k p] in
theorem transitionHom_refl (n : ℕ) :
    transitionHom p k σ n n le_rfl = AlgHom.id W (MultivariableThickening.WittMultivariableThickening.Ring p k σ n) := by
  apply AlgHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact transitionHom_quotient p k σ n n le_rfl a

omit [CharP k p] [PerfectRing k p] in
theorem transitionHom_comp (l n m : ℕ) (hln : l ≤ n) (hnm : n ≤ m) :
    (transitionHom p k σ l n hln).comp (transitionHom p k σ n m hnm) =
      transitionHom p k σ l m (hln.trans hnm) := by
  apply AlgHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change transitionHom p k σ l n hln (transitionHom p k σ n m hnm (q m a)) =
    transitionHom p k σ l m (hln.trans hnm) (q m a)
  rw [transitionHom_quotient, transitionHom_quotient, transitionHom_quotient]

theorem transition_refl (n : ℕ) : transition p k σ n n le_rfl = 𝟙 (S n) := by
  apply PD.Thickening.AffinePDThickening.Hom.ext
  exact transitionHom_refl p k σ n

theorem transition_comp (l n m : ℕ) (hln : l ≤ n) (hnm : n ≤ m) :
    transition p k σ n m hnm ≫ transition p k σ l n hln = transition p k σ l m (hln.trans hnm) := by
  apply PD.Thickening.AffinePDThickening.Hom.ext
  exact transitionHom_comp p k σ l n m hln hnm

def tower : ℕᵒᵖ ⥤ PD.Thickening.AffinePDThickening p k k where
  obj n := S n.unop
  map f := transition p k σ _ _ (leOfHom f.unop)
  map_id n := transition_refl p k σ n.unop
  map_comp f g := (transition_comp p k σ _ _ _ (leOfHom g.unop) (leOfHom f.unop)).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTower.WittMultivariableTower
