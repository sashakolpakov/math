import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTower
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialPoincare

/-! # Multivariable Operators -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableOperators.WittMultivariableOperators

noncomputable section

/-!
# Compatible coordinate operators on the actual crystalline inverse limit

Coordinate derivatives and primitives act on compatible sections because
they commute with every quotient transition. Their integral identities
hold coordinatewise in the actual inverse-limit ring.
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "K" => FractionRing W
local notation "I" => Ideal.span {(p : W)}
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "h" => IsFractionRing.injective W K
local notation "unit" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.base_unit p k
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableThickening.WittMultivariableThickening.Ring p k σ
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.baseIdeal p k
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTower.WittMultivariableTower.tower p k σ
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k k T
local notation "t" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTower.WittMultivariableTower.transitionHom p k σ
local notation "Residues" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Poincare.WittPolynomialPoincare.coefficients p k

def mapCompatible (f : ∀ n, Module.End W (Q n))
    (hf : ∀ n m hnm a, t n m hnm (f m a) = f n (t n m hnm a)) : Module.End W C where
  toFun x := ⟨fun n => f n (x.val n), by
    intro n m hnm
    change t n m hnm (f m (x.val m)) = f n (x.val n)
    exact (hf n m hnm (x.val m)).trans (congrArg (f n) (x.property n m hnm))⟩
  map_add' x y := PD.InverseLimit.PDInverseLimit.ext p k k T (fun n => (f n).map_add (x.val n) (y.val n))
  map_smul' a x := PD.InverseLimit.PDInverseLimit.ext p k k T (fun n => (f n).map_smul a (x.val n))

def derivative (i : σ) : Module.End W C :=
  mapCompatible p k σ (fun n => (QuotientMultivariableD.QuotientMultivariableForms.derivation W σ K h I δ unit (L n) i).toLinearMap)
    (fun n m hnm a => (QuotientMultivariableTo.QuotientMultivariableTransitions.derivation_transition W σ K h I δ unit
      (L n) (L m) (WittPolynomial.Tower.WittPolynomialTower.baseIdeal_antitone p k hnm) i a).symm)

def primitive (i : σ) : Module.End W C :=
  mapCompatible p k σ (fun n => QuotientMultivariableMk.QuotientMultivariablePrimitive.primitive W σ K h (L n) i)
    (fun n m hnm a => (QuotientMultivariableTo.QuotientMultivariableTransitions.primitive_transition W σ K h
      (L n) (L m) (WittPolynomial.Tower.WittPolynomialTower.baseIdeal_antitone p k hnm) i a).symm)

theorem eval_derivative (i : σ) (n : ℕ) (x : C) :
    PD.InverseLimit.PDInverseLimit.eval p k k T n (derivative p k σ i x) =
      QuotientMultivariableD.QuotientMultivariableForms.derivation W σ K h I δ unit (L n) i (PD.InverseLimit.PDInverseLimit.eval p k k T n x) := rfl

theorem eval_primitive (i : σ) (n : ℕ) (x : C) :
    PD.InverseLimit.PDInverseLimit.eval p k k T n (primitive p k σ i x) =
      QuotientMultivariableMk.QuotientMultivariablePrimitive.primitive W σ K h (L n) i (PD.InverseLimit.PDInverseLimit.eval p k k T n x) := rfl

theorem derivatives_commute (i j : σ) : Function.Commute (derivative p k σ i) (derivative p k σ j) := by
  intro x
  apply PD.InverseLimit.PDInverseLimit.ext p k k T
  intro n
  rw [eval_derivative, eval_derivative, eval_derivative, eval_derivative]
  exact QuotientMultivariableD.QuotientMultivariableForms.derivations_commute W σ K h I δ unit (L n) i j _

theorem derivative_primitive (i : σ) (x : C) : derivative p k σ i (primitive p k σ i x) = x := by
  apply PD.InverseLimit.PDInverseLimit.ext p k k T
  intro n
  rw [eval_derivative, eval_primitive]
  exact QuotientMultivariableMk.QuotientMultivariablePrimitive.derivation_primitive W σ K h I δ unit (L n) i _

theorem derivative_primitive_commute (i j : σ) (hji : j ≠ i) (x : C) :
    derivative p k σ j (primitive p k σ i x) = primitive p k σ i (derivative p k σ j x) := by
  apply PD.InverseLimit.PDInverseLimit.ext p k k T
  intro n
  rw [eval_derivative, eval_primitive, eval_primitive, eval_derivative]
  exact QuotientMultivariableMk.QuotientMultivariablePrimitive.derivation_primitive_commute W σ K h I δ unit (L n) i j hji _

def residueConstants : Residues →ₗ[W] C where
  toFun x := ⟨fun n => QuotientMultivariableMk.QuotientMultivariablePrimitive.constants W σ (L n) (x.val n), by
    intro n m hnm
    change t n m hnm (QuotientMultivariableMk.QuotientMultivariablePrimitive.constants W σ (L m) (x.val m)) = _
    exact (QuotientMultivariableTo.QuotientMultivariableTransitions.constants_transition W σ (L n) (L m)
      (WittPolynomial.Tower.WittPolynomialTower.baseIdeal_antitone p k hnm) (x.val m)).trans
        (congrArg (QuotientMultivariableMk.QuotientMultivariablePrimitive.constants W σ (L n)) (x.property n m hnm))⟩
  map_add' x y := PD.InverseLimit.PDInverseLimit.ext p k k T (fun n =>
    (QuotientMultivariableMk.QuotientMultivariablePrimitive.constants W σ (L n)).map_add (x.val n) (y.val n))
  map_smul' a x := PD.InverseLimit.PDInverseLimit.ext p k k T (fun n =>
    (QuotientMultivariableMk.QuotientMultivariablePrimitive.constants W σ (L n)).toLinearMap.map_smul a (x.val n))

def residueCoefficient : C →ₗ[W] Residues where
  toFun x := ⟨fun n => QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient W σ K h (L n) (x.val n), by
    intro n m hnm
    change WittPolynomial.Poincare.WittPolynomialPoincare.coefficientTransition p k n m hnm
      (QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient W σ K h (L m) (x.val m)) = _
    exact (QuotientMultivariableTo.QuotientMultivariableTransitions.constantCoefficient_transition W σ K h (L n) (L m)
      (WittPolynomial.Tower.WittPolynomialTower.baseIdeal_antitone p k hnm) (x.val m)).symm.trans
        (congrArg (QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient W σ K h (L n)) (x.property n m hnm))⟩
  map_add' x y := Subtype.ext (funext (fun n =>
    (QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient W σ K h (L n)).map_add (x.val n) (y.val n)))
  map_smul' a x := Subtype.ext (funext (fun n =>
    (QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient W σ K h (L n)).map_smul a (x.val n)))

theorem residueCoefficient_constants :
    (residueCoefficient p k σ).comp (residueConstants p k σ) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  exact LinearMap.congr_fun (QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient_constants W σ K h (L n)) (x.val n)

theorem derivative_constants (i : σ) (x : Residues) : derivative p k σ i (residueConstants p k σ x) = 0 := by
  apply PD.InverseLimit.PDInverseLimit.ext p k k T
  intro n
  exact QuotientMultivariableMk.QuotientMultivariablePrimitive.derivation_constants W σ K h I δ unit (L n) i (x.val n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableOperators.WittMultivariableOperators
