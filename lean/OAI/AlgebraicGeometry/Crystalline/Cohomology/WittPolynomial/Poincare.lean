import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Forms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham

/-! # Poincare -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Poincare.WittPolynomialPoincare

noncomputable section

/-!
# Poincaré lemma for the inverse-limit crystalline form complex

The finite-level primitives are compatible. Applying them coordinatewise
therefore contracts the actual inverse system of crystalline one-forms.
The constants are the compatible residues in W/p^(n+1).
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "K" => FractionRing W
local notation "h" => IsFractionRing.injective W K
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.baseIdeal p k
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Tower.WittPolynomialTower.tower p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k k T
local notation "Ω" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.CompletedForm p k k T 1
local notation "d" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.differentialRing p k k T

def coefficientTransition (n m : ℕ) (hnm : n ≤ m) : W ⧸ L m →ₐ[W] W ⧸ L n :=
  Ideal.Quotient.factorₐ W (Tower.WittPolynomialTower.baseIdeal_antitone p k hnm)

/-- The literal inverse limit of the positive p-power coefficient quotients. -/
def coefficients : Submodule W (∀ n : ℕ, W ⧸ L n) where
  carrier x := ∀ n m hnm, coefficientTransition p k n m hnm (x m) = x n
  zero_mem' n m hnm := map_zero (coefficientTransition p k n m hnm)
  add_mem' hx hy n m hnm := by rw [Pi.add_apply, map_add, hx n m hnm, hy n m hnm]; rfl
  smul_mem' w _ hx n m hnm := by rw [Pi.smul_apply, map_smul, hx n m hnm]; rfl

def constants : coefficients p k →ₗ[W] C where
  toFun x := ⟨fun n => QuotientPolynomialMk.QuotientPolynomialPoincare.constants W (L n) (x.val n), by
    intro n m hnm
    change Tower.WittPolynomialTower.transitionHom p k n m hnm
      (QuotientPolynomialMk.QuotientPolynomialPoincare.constants W (L m) (x.val m)) = _
    exact (QuotientPolynomialTransition.QuotientPolynomialTransitions.constants_transition W (L n) (L m)
      (Tower.WittPolynomialTower.baseIdeal_antitone p k hnm) (x.val m)).trans
        (congrArg (QuotientPolynomialMk.QuotientPolynomialPoincare.constants W (L n)) (x.property n m hnm))⟩
  map_add' x y := PD.InverseLimit.PDInverseLimit.ext p k k T (fun n =>
    (QuotientPolynomialMk.QuotientPolynomialPoincare.constants W (L n)).map_add (x.val n) (y.val n))
  map_smul' w x := PD.InverseLimit.PDInverseLimit.ext p k k T (fun n =>
    (QuotientPolynomialMk.QuotientPolynomialPoincare.constants W (L n)).toLinearMap.map_smul w (x.val n))

def constantCoefficient : C →ₗ[W] coefficients p k where
  toFun x := ⟨fun n => QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient W K h (L n)
    (PD.InverseLimit.PDInverseLimit.eval p k k T n x), by
      intro n m hnm
      change coefficientTransition p k n m hnm
        (QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient W K h (L m) (x.val m)) = _
      have hc := QuotientPolynomialTransition.QuotientPolynomialTransitions.constantCoefficient_transition W K h (L n) (L m)
        (Tower.WittPolynomialTower.baseIdeal_antitone p k hnm) (x.val m)
      exact hc.symm.trans (congrArg (QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient W K h (L n))
        (x.property n m hnm))⟩
  map_add' x y := Subtype.ext (funext (fun n =>
    (QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient W K h (L n)).map_add (x.val n) (y.val n)))
  map_smul' w x := Subtype.ext (funext (fun n =>
    (QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient W K h (L n)).map_smul w (x.val n)))

/-- The compatible finite primitives give a primitive in the inverse-limit ring. -/
def primitiveForms : Ω →ₗ[W] C where
  toFun ω := ⟨fun n => Forms.WittPolynomialForms.primitiveForms p k n (ω.val n), by
    intro n m hnm
    change Tower.WittPolynomialTower.transitionHom p k n m hnm
      (Forms.WittPolynomialForms.primitiveForms p k m (ω.val m)) = _
    exact (Forms.WittPolynomialForms.primitiveForms_formMap p k n m hnm (ω.val m)).symm.trans
      (congrArg (Forms.WittPolynomialForms.primitiveForms p k n) (ω.property n m hnm))⟩
  map_add' ω η := PD.InverseLimit.PDInverseLimit.ext p k k T (fun n =>
    (Forms.WittPolynomialForms.primitiveForms p k n).map_add (ω.val n) (η.val n))
  map_smul' w ω := PD.InverseLimit.PDInverseLimit.ext p k k T (fun n =>
    (Forms.WittPolynomialForms.primitiveForms p k n).map_smul w (ω.val n))

theorem differential_primitive (ω : Ω) : d (primitiveForms p k ω) = ω := by
  apply PD.PDDeRham.ext p k k T
  intro n
  rw [PD.PDDeRham.eval_differentialRing]
  exact Forms.WittPolynomialForms.differential_primitive p k n (ω.val n)

theorem primitive_differential (a : C) :
    primitiveForms p k (d a) + constants p k (constantCoefficient p k a) = a := by
  apply PD.InverseLimit.PDInverseLimit.ext p k k T
  intro n
  change Forms.WittPolynomialForms.primitiveForms p k n (PD.PDDeRham.eval p k k T 1 n (d a)) +
    QuotientPolynomialMk.QuotientPolynomialPoincare.constants W (L n)
      (QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient W K h (L n) (a.val n)) = a.val n
  rw [PD.PDDeRham.eval_differentialRing]
  exact Forms.WittPolynomialForms.primitive_differential p k n (a.val n)

theorem constantCoefficient_constants (a : coefficients p k) :
    constantCoefficient p k (constants p k a) = a :=
  Subtype.ext (funext (fun n => QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient_constants W K h (L n) (a.val n)))

theorem differential_constants (a : coefficients p k) : d (constants p k a) = 0 := by
  apply PD.PDDeRham.ext p k k T
  intro n
  rw [PD.PDDeRham.eval_differentialRing, map_zero]
  exact Forms.WittPolynomialForms.differential_constants p k n (a.val n)

def sequence : ShortComplex (ModuleCat.{u} W) :=
  ShortComplex.moduleCatMk (constants p k) d (LinearMap.ext (differential_constants p k))

/-- The actual inverse-limit crystalline Poincaré sequence is short exact. -/
theorem sequence_shortExact : (sequence p k).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro a
    change C at a
    change d a = 0 ↔ ∃ b, constants p k b = a
    constructor
    · intro ha
      exact ⟨constantCoefficient p k a, by
        simpa only [ha, map_zero, zero_add] using primitive_differential p k a⟩
    · rintro ⟨b, rfl⟩
      exact differential_constants p k b
  · exact Function.LeftInverse.injective (constantCoefficient_constants p k)
  · intro ω
    exact ⟨primitiveForms p k ω, differential_primitive p k ω⟩

theorem higher_form_eq_zero (j : ℕ) (hj : 2 ≤ j)
    (ω : PD.PDDeRham.CompletedForm p k k T j) : ω = 0 := by
  apply PD.PDDeRham.ext p k k T
  intro n
  exact Forms.WittPolynomialForms.higher_form_eq_zero p k n j hj (ω.val n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Poincare.WittPolynomialPoincare
