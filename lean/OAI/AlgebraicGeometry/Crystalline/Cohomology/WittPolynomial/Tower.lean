import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening
import OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialTransition
import Mathlib.CategoryTheory.Category.Preorder

/-! # Tower -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Tower.WittPolynomialTower

noncomputable section

/-!
# The crystalline inverse system of Witt divided-polynomial rings

The quotient transition maps preserve reduction and the actual divided
powers on its kernel. They define an inverse system in the affine
crystalline category.
-/

open _root_.CategoryTheory Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "K" => FractionRing W
local notation "I₀" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "h" => IsFractionRing.injective W K
local notation "G" => DividedPowerAlgebra W W
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.ideal W I₀
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.dividedPowers W K h I₀ δ₀ (OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.base_unit p k)
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.thickening p k
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.baseIdeal p k
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.quotient p k

omit [CharP k p] [PerfectRing k p] in
theorem baseIdeal_antitone : Antitone (Thickening.WittPolynomialThickening.baseIdeal p k) := by
  intro n m hnm
  exact Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1)

theorem quotient_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism γ (S n).dividedPowers (q n).toRingHom where
  ideal_comp := by
    change (IG).map (q n).toRingHom ≤ RingHom.ker (Thickening.WittPolynomialThickening.reduction p k n)
    rw [Thickening.WittPolynomialThickening.reduction_kernel]
    exact le_rfl
  dpow_comp x hx :=
    (QuotientPolynomialEq.QuotientPolynomialForms.quotient_isDPMorphism W K h I₀ δ₀ (Thickening.WittPolynomialThickening.base_unit p k)
      (L n) (Thickening.WittPolynomialThickening.baseIdeal_subDP p k n)).dpow_comp x hx

def transitionHom (n m : ℕ) (hnm : n ≤ m) :
    Thickening.WittPolynomialThickening.Ring p k m →ₐ[W] Thickening.WittPolynomialThickening.Ring p k n :=
  QuotientPolynomialTransition.QuotientPolynomialTransitions.transition W (L n) (L m) (baseIdeal_antitone p k hnm)

omit [CharP k p] [PerfectRing k p] in
@[simp] theorem transitionHom_quotient (n m : ℕ) (hnm : n ≤ m) (a : G) :
    transitionHom p k n m hnm (q m a) = q n a := rfl

theorem transitionHom_isDPMorphism (n m : ℕ) (hnm : n ≤ m) :
    DividedPowers.IsDPMorphism (S m).dividedPowers (S n).dividedPowers
      (transitionHom p k n m hnm).toRingHom where
  ideal_comp := by
    change (RingHom.ker (Thickening.WittPolynomialThickening.reduction p k m)).map _ ≤
      RingHom.ker (Thickening.WittPolynomialThickening.reduction p k n)
    rw [Thickening.WittPolynomialThickening.reduction_kernel, Thickening.WittPolynomialThickening.reduction_kernel]
    exact (QuotientPolynomialTransition.QuotientPolynomialTransitions.transition_isDPMorphism W K h I₀ δ₀
      (Thickening.WittPolynomialThickening.base_unit p k) (L n) (L m)
      (Thickening.WittPolynomialThickening.baseIdeal_subDP p k n)
      (Thickening.WittPolynomialThickening.baseIdeal_subDP p k m) (baseIdeal_antitone p k hnm)).ideal_comp
  dpow_comp x hx := by
    have hx' : x ∈ QuotientPolynomialEq.QuotientPolynomialForms.ideal W I₀ (L m) :=
      Thickening.WittPolynomialThickening.reduction_kernel p k m ▸ hx
    exact (QuotientPolynomialTransition.QuotientPolynomialTransitions.transition_isDPMorphism W K h I₀ δ₀
      (Thickening.WittPolynomialThickening.base_unit p k) (L n) (L m)
      (Thickening.WittPolynomialThickening.baseIdeal_subDP p k n)
      (Thickening.WittPolynomialThickening.baseIdeal_subDP p k m) (baseIdeal_antitone p k hnm)).dpow_comp x hx'

theorem transitionHom_reduction (n m : ℕ) (hnm : n ≤ m) :
    (Thickening.WittPolynomialThickening.reduction p k n).comp (transitionHom p k n m hnm).toRingHom =
      Thickening.WittPolynomialThickening.reduction p k m := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Thickening.WittPolynomialThickening.reduction p k n (transitionHom p k n m hnm (q m a)) =
    Thickening.WittPolynomialThickening.reduction p k m (q m a)
  rw [transitionHom_quotient, Thickening.WittPolynomialThickening.reduction_quotient,
    Thickening.WittPolynomialThickening.reduction_quotient]

def transition (n m : ℕ) (hnm : n ≤ m) : S m ⟶ S n where
  hom := transitionHom p k n m hnm
  reduction_comp := transitionHom_reduction p k n m hnm
  dp_comp := transitionHom_isDPMorphism p k n m hnm

omit [CharP k p] [PerfectRing k p] in
theorem transitionHom_refl (n : ℕ) :
    transitionHom p k n n le_rfl = AlgHom.id W (Thickening.WittPolynomialThickening.Ring p k n) := by
  apply AlgHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact transitionHom_quotient p k n n le_rfl a

omit [CharP k p] [PerfectRing k p] in
theorem transitionHom_comp (l n m : ℕ) (hln : l ≤ n) (hnm : n ≤ m) :
    (transitionHom p k l n hln).comp (transitionHom p k n m hnm) =
      transitionHom p k l m (hln.trans hnm) := by
  apply AlgHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change transitionHom p k l n hln (transitionHom p k n m hnm (q m a)) =
    transitionHom p k l m (hln.trans hnm) (q m a)
  rw [transitionHom_quotient, transitionHom_quotient, transitionHom_quotient]

theorem transition_refl (n : ℕ) : transition p k n n le_rfl = 𝟙 (S n) := by
  apply PD.Thickening.AffinePDThickening.Hom.ext
  exact transitionHom_refl p k n

theorem transition_comp (l n m : ℕ) (hln : l ≤ n) (hnm : n ≤ m) :
    transition p k n m hnm ≫ transition p k l n hln = transition p k l m (hln.trans hnm) := by
  apply PD.Thickening.AffinePDThickening.Hom.ext
  exact transitionHom_comp p k l n m hln hnm

/-- The actual crystalline tower Γ(W)/p^(n+1). -/
def tower : ℕᵒᵖ ⥤ PD.Thickening.AffinePDThickening p k k where
  obj n := S n.unop
  map f := transition p k _ _ (leOfHom f.unop)
  map_id n := transition_refl p k n.unop
  map_comp f g := (transition_comp p k _ _ _ (leOfHom g.unop) (leOfHom f.unop)).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Tower.WittPolynomialTower
