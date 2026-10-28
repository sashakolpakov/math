import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableOperators
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ProjectionNaturality

/-! # Multivariable Tensor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTensor.WittMultivariableTensor

noncomputable section

/-!
# The completed multivariable tensor Poincaré homotopy

All coordinate projections on compatible sections compose to the
compatible constant coefficient. The tensor exterior complex of this
actual inverse-limit ring therefore contracts onto W(k).
-/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableOperators.WittMultivariableOperators

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
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableOperators.WittMultivariableOperators.derivative p k σ
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableOperators.WittMultivariableOperators.primitive p k σ
local notation "Residues" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Poincare.WittPolynomialPoincare.coefficients p k

theorem coefficientProjection_constants (l : List σ) (hl : ∀ i, i ∈ l) :
    Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient W σ C D S l = (MultivariableOperators.WittMultivariableOperators.residueConstants p k σ).comp (MultivariableOperators.WittMultivariableOperators.residueCoefficient p k σ) := by
  apply LinearMap.ext
  intro a
  apply PD.InverseLimit.PDInverseLimit.ext p k k T
  intro n
  have hn := Koszul.ProjectionNaturality.KoszulProjectionNaturality.successive W σ C (Q n) D S
    (QuotientMultivariableMk.QuotientMultivariablePrimitive.derivatives W σ K h I δ unit (L n))
    (QuotientMultivariableMk.QuotientMultivariablePrimitive.primitive W σ K h (L n))
    (PD.InverseLimit.PDInverseLimit.eval p k k T n).toLinearMap (fun _ _ => rfl) (fun _ _ => rfl) l a
  exact hn.trans (LinearMap.congr_fun
    (QuotientMultivariableMk.QuotientMultivariablePrimitive.coefficientProjection_constants W σ K h I δ unit (L n) l hl) (a.val n))

variable [Fintype σ]

def complex : CochainComplex (ModuleCat W) ℕ :=
  Koszul.Tensor.KoszulTensor.complex W σ C D (MultivariableOperators.WittMultivariableOperators.derivatives_commute p k σ)

def residueHomotopyEquiv : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat W)).obj (ModuleCat.of W Residues)) (complex p k σ) :=
  Koszul.ConstantsRetraction.KoszulConstantsRetraction.homotopyEquiv W σ C Residues D S
    (MultivariableOperators.WittMultivariableOperators.derivatives_commute p k σ) (MultivariableOperators.WittMultivariableOperators.derivative_primitive p k σ) (MultivariableOperators.WittMultivariableOperators.derivative_primitive_commute p k σ)
    (Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.coordinateList σ) (Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.mem_coordinateList σ)
    (MultivariableOperators.WittMultivariableOperators.residueConstants p k σ) (MultivariableOperators.WittMultivariableOperators.residueCoefficient p k σ) (MultivariableOperators.WittMultivariableOperators.residueCoefficient_constants p k σ)
    (MultivariableOperators.WittMultivariableOperators.derivative_constants p k σ) (coefficientProjection_constants p k σ
      (Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.coordinateList σ) (Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.mem_coordinateList σ))

def homotopyEquiv : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat W)).obj (ModuleCat.of W W)) (complex p k σ) :=
  (HomotopyEquiv.ofIso ((CochainComplex.single₀ (ModuleCat W)).mapIso
    (WittPolynomial.PolynomialPoincare.WittPolynomialPoincare.coefficientsEquiv p k).toModuleIso)).trans (residueHomotopyEquiv p k σ)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTensor.WittMultivariableTensor
