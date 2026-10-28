import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Tower
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence

/-! # Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Forms.WittPolynomialForms

noncomputable section

/-!
# Poincaré contractions on the actual Witt crystalline thickenings

Identify the explicit quotient PD ideal with the reduction kernel, then
transport the checked local calculation to the forms on the actual
crystalline objects. The primitives are compatible throughout the tower.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "K" => FractionRing W
local notation "I₀" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "h" => IsFractionRing.injective W K
local notation "hu" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.base_unit p k
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.thickening p k
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.baseIdeal p k
local notation "hL" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.baseIdeal_subDP p k
local notation "J" => fun n => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.ideal W I₀ (L n)
local notation "ε" => fun n => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.dividedPowers W K h I₀ δ₀ hu (L n) (hL n)

abbrev Form (n j : ℕ) :=
  PD.DeRham.PDDeRham.Form W (Thickening.WittPolynomialThickening.Ring p k n) (RingHom.ker (Thickening.WittPolynomialThickening.reduction p k n)) (Thickening.WittPolynomialThickening.kernelDividedPowers p k n) j

theorem identity_toKernel (n : ℕ) :
    DividedPowers.IsDPMorphism (ε n) (Thickening.WittPolynomialThickening.kernelDividedPowers p k n) (RingHom.id (Thickening.WittPolynomialThickening.Ring p k n)) where
  ideal_comp := by
    change (J n).map (RingHom.id (Thickening.WittPolynomialThickening.Ring p k n)) ≤
      RingHom.ker (Thickening.WittPolynomialThickening.reduction p k n)
    rw [Ideal.map_id]
    exact (Thickening.WittPolynomialThickening.reduction_kernel p k n).symm.le
  dpow_comp _ _ := rfl

theorem identity_fromKernel (n : ℕ) :
    DividedPowers.IsDPMorphism (Thickening.WittPolynomialThickening.kernelDividedPowers p k n) (ε n) (RingHom.id (Thickening.WittPolynomialThickening.Ring p k n)) where
  ideal_comp := by
    change (RingHom.ker (Thickening.WittPolynomialThickening.reduction p k n)).map
      (RingHom.id (Thickening.WittPolynomialThickening.Ring p k n)) ≤ J n
    rw [Ideal.map_id]
    exact (Thickening.WittPolynomialThickening.reduction_kernel p k n).le
  dpow_comp _ _ := rfl

def formsEquiv (n j : ℕ) : PD.DeRham.PDDeRham.Form W (Thickening.WittPolynomialThickening.Ring p k n) (J n) (ε n) j ≃ₗ[W] Form p k n j :=
  PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv (A := CommAlgCat.of W (Thickening.WittPolynomialThickening.Ring p k n)) (B := CommAlgCat.of W (Thickening.WittPolynomialThickening.Ring p k n))
    AlgEquiv.refl (identity_toKernel p k n) (identity_fromKernel p k n) j

local notation "D" => fun n => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D W (OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.Ring p k n) (RingHom.ker (OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.reduction p k n)) (OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.kernelDividedPowers p k n)
local notation "DQ" => fun n => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D W (OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.Ring p k n) (J n) (ε n)

theorem formsEquiv_D (n : ℕ) (a : (Thickening.WittPolynomialThickening.Ring p k n)) : formsEquiv p k n 1 (DQ n a) = D n a :=
  PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv_D
    (A := CommAlgCat.of W (Thickening.WittPolynomialThickening.Ring p k n)) (B := CommAlgCat.of W (Thickening.WittPolynomialThickening.Ring p k n))
    AlgEquiv.refl (identity_toKernel p k n) (identity_fromKernel p k n) a

theorem formsEquiv_symm_D (n : ℕ) (a : (Thickening.WittPolynomialThickening.Ring p k n)) : (formsEquiv p k n 1).symm (D n a) = DQ n a := by
  apply (formsEquiv p k n 1).injective
  rw [LinearEquiv.apply_symm_apply, formsEquiv_D]

def toRing (n : ℕ) : Form p k n 1 →ₗ[W] (Thickening.WittPolynomialThickening.Ring p k n) :=
  ((QuotientPolynomialEq.QuotientPolynomialForms.toRing W K h I₀ δ₀ hu (L n) (hL n)).restrictScalars W).comp
    (formsEquiv p k n 1).symm.toLinearMap

theorem toRing_D (n : ℕ) (a : (Thickening.WittPolynomialThickening.Ring p k n)) :
    toRing p k n (D n a) = QuotientPolynomialEq.QuotientPolynomialForms.derivation W K h (L n) a := by
  change QuotientPolynomialEq.QuotientPolynomialForms.toRing W K h I₀ δ₀ hu (L n) (hL n)
    ((formsEquiv p k n 1).symm (D n a)) = _
  rw [formsEquiv_symm_D, QuotientPolynomialEq.QuotientPolynomialForms.toRing_D]

def primitiveForms (n : ℕ) : Form p k n 1 →ₗ[W] (Thickening.WittPolynomialThickening.Ring p k n) :=
  (QuotientPolynomialMk.QuotientPolynomialPoincare.primitiveForms W K h I₀ δ₀ hu (L n) (hL n)).comp
    (formsEquiv p k n 1).symm.toLinearMap

theorem differential_primitive (n : ℕ) (ω : Form p k n 1) : D n (primitiveForms p k n ω) = ω := by
  have hp := congrArg (formsEquiv p k n 1)
    (QuotientPolynomialMk.QuotientPolynomialPoincare.differential_primitive W K h I₀ δ₀ hu (L n) (hL n)
      ((formsEquiv p k n 1).symm ω))
  rw [formsEquiv_D, LinearEquiv.apply_symm_apply] at hp
  exact hp

theorem primitive_differential (n : ℕ) (a : (Thickening.WittPolynomialThickening.Ring p k n)) :
    primitiveForms p k n (D n a) + QuotientPolynomialMk.QuotientPolynomialPoincare.constants W (L n)
      (QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient W K h (L n) a) = a := by
  change QuotientPolynomialMk.QuotientPolynomialPoincare.primitive W K h (L n)
    (QuotientPolynomialEq.QuotientPolynomialForms.toRing W K h I₀ δ₀ hu (L n) (hL n)
      ((formsEquiv p k n 1).symm (D n a))) + _ = _
  rw [formsEquiv_symm_D, QuotientPolynomialEq.QuotientPolynomialForms.toRing_D]
  exact QuotientPolynomialMk.QuotientPolynomialPoincare.primitive_derivation W K h (L n) a

theorem differential_constants (n : ℕ) (a : W ⧸ L n) :
    D n (QuotientPolynomialMk.QuotientPolynomialPoincare.constants W (L n) a) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact (D n).map_algebraMap a

def formMap (n m : ℕ) (hnm : n ≤ m) (j : ℕ) : Form p k m j →ₗ[W] Form p k n j :=
  PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (Tower.WittPolynomialTower.transitionHom p k n m hnm))
    (Tower.WittPolynomialTower.transitionHom_isDPMorphism p k n m hnm) j

theorem toRing_formMap (n m : ℕ) (hnm : n ≤ m) (ω : Form p k m 1) :
    toRing p k n (formMap p k n m hnm 1 ω) =
      Tower.WittPolynomialTower.transitionHom p k n m hnm (toRing p k m ω) := by
  have hs : Function.Surjective (D m) := fun ω => ⟨primitiveForms p k m ω, differential_primitive p k m ω⟩
  obtain ⟨a, rfl⟩ := hs ω
  have hd := PD.FormSurjective.PDFormSurjective.formMap_D
    (CommAlgCat.ofHom (Tower.WittPolynomialTower.transitionHom p k n m hnm))
    (Tower.WittPolynomialTower.transitionHom_isDPMorphism p k n m hnm) a
  change formMap p k n m hnm 1 (D m a) = D n (Tower.WittPolynomialTower.transitionHom p k n m hnm a) at hd
  rw [hd, toRing_D, toRing_D]
  exact QuotientPolynomialTransition.QuotientPolynomialTransitions.derivation_transition W K h (L n) (L m)
    (Tower.WittPolynomialTower.baseIdeal_antitone p k hnm) a

theorem primitiveForms_formMap (n m : ℕ) (hnm : n ≤ m) (ω : Form p k m 1) :
    primitiveForms p k n (formMap p k n m hnm 1 ω) =
      Tower.WittPolynomialTower.transitionHom p k n m hnm (primitiveForms p k m ω) := by
  change QuotientPolynomialMk.QuotientPolynomialPoincare.primitive W K h (L n) (toRing p k n (formMap p k n m hnm 1 ω)) = _
  rw [toRing_formMap]
  exact QuotientPolynomialTransition.QuotientPolynomialTransitions.primitive_transition W K h (L n) (L m)
    (Tower.WittPolynomialTower.baseIdeal_antitone p k hnm) (toRing p k m ω)

theorem higher_form_eq_zero (n j : ℕ) (hj : 2 ≤ j) (ω : Form p k n j) : ω = 0 := by
  apply (formsEquiv p k n j).symm.injective
  rw [map_zero]
  exact QuotientPolynomialEq.QuotientPolynomialForms.higher_form_eq_zero W K h I₀ δ₀ hu (L n) (hL n) j hj _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Forms.WittPolynomialForms
