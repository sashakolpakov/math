import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Semilinear

/-! # Polynomial Absolute Frobenius -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.PolynomialAbsoluteFrobenius

noncomputable section

/-!
# The completed polynomial operator is induced by the absolute-Frobenius lift

The integral lift on the original differential symbols factors through
the substitution and coefficient maps. This identity survives completion
coordinatewise and identifies the rational semilinear operator on tensors.
-/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "K₀" => FractionRing W
local notation "P" => MvPolynomial σ W
local notation "I" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.ideal p k
local notation "φ" => WittVector.frobeniusEquiv p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.completedComplex p k σ

def completedMap : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map (φ).toRingHom C C :=
  Semilinear.CompletionMap.SemilinearCompletionMap.map (φ).toRingHom I I
    (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.ideal_map p k (φ).toRingHom).le
    (AbsoluteFrobenius.PolynomialAbsoluteFrobenius.complexMap p k σ)

def completedSubstitution : C ⟶ C :=
  ((NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionLinear.functor I).mapHomologicalComplex (.up ℕ)).map
    (Cohomology.Prime.PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.ordinary p k σ)

theorem completed_factor (n : ℕ) (ω : (C).X n) :
    (completedMap p k σ).f n ω = (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.completedMap p k σ).f n
      ((completedSubstitution p k σ).f n ω) := by
  apply AdicCompletion.ext
  intro r
  change NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.reduce (φ).toRingHom I I
      (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.ideal_map p k (φ).toRingHom).le
      ((AbsoluteFrobenius.PolynomialAbsoluteFrobenius.complexMap p k σ).f n) r (ω.val r) =
    NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.reduce (φ).toRingHom I I
      (WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.ideal_map p k (φ).toRingHom).le
      ((WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.complexMap p k σ).f n) r
      (((Cohomology.Prime.PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.ordinary p k σ).f n).hom.reduceModIdeal (I ^ r) (ω.val r))
  generalize ω.val r = q
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    change Submodule.Quotient.mk ((AbsoluteFrobenius.PolynomialAbsoluteFrobenius.complexMap p k σ).f n x) =
      Submodule.Quotient.mk ((WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius.complexMap p k σ).f n
        ((Cohomology.Prime.PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.ordinary p k σ).f n x))
    exact congrArg (Submodule.Quotient.mk (p := I ^ r • (⊤ : Submodule W (DeRhamPresentationTo.DeRhamPresentation.Form W P n))))
      (AbsoluteFrobenius.PolynomialAbsoluteFrobenius.integral_factor p k σ n x)

theorem rational_tmul (n : ℕ) (a : K₀) (ω : (C).X n) :
    (RationalPolynomial.RationalPolynomialCoefficientFrobenius.frobenius p k σ).f n (a ⊗ₜ[W] ω) =
      RationalPolynomial.RationalPolynomialCoefficientFrobenius.scalarEquiv p k a ⊗ₜ[W] (completedMap p k σ).f n ω := by
  change RationalPolynomial.RationalPolynomialCoefficientFrobenius.formsEquiv p k σ n
    (((completedSubstitution p k σ).f n).hom.baseChange K₀ (a ⊗ₜ[W] ω)) = _
  rw [LinearMap.baseChange_tmul, RationalPolynomial.RationalPolynomialCoefficientFrobenius.formsEquiv_tmul,
    ← completed_factor]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.PolynomialAbsoluteFrobenius
