import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Derivation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorMap

/-! # Frame Differential -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential

noncomputable section

/-!
# Polynomial frame differentials in the divided-coordinate extension

Polynomial variables map to their chosen lifts plus divided coordinates.
The coordinate derivative of this map agrees with the ordinary polynomial
partial derivative. This gives a chain map from the actual polynomial
coordinate complex into its frame linearization over any coefficient base.
-/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (A R σ : Type u) [CommRing A] [CommRing R] [Algebra A R] (x : σ → R)

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Derivation.FreeDividedDerivation.derivation R σ

def polynomialMap : MvPolynomial σ A →ₐ[A] G :=
  MvPolynomial.aeval (fun i => algebraMap R G (x i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)

theorem derivative_X (i j : σ) :
    D i (polynomialMap A R σ x (MvPolynomial.X j)) =
      polynomialMap A R σ x (MvPolynomial.pderiv i (MvPolynomial.X j)) := by
  classical
  change D i (MvPolynomial.aeval (fun i => algebraMap R G (x i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)
    (MvPolynomial.X j)) = _
  rw [MvPolynomial.aeval_X, map_add, Derivation.map_algebraMap, zero_add,
    FreeDivided.Derivation.FreeDividedDerivation.derivation_coordinate]
  by_cases hij : j = i
  · subst j
    rw [ite_eq_left rfl, MvPolynomial.pderiv_X_self, map_one]
  · rw [ite_eq_right hij, MvPolynomial.pderiv_X_of_ne hij, map_zero]

theorem derivative_polynomialMap (i : σ) (t : MvPolynomial σ A) :
    D i (polynomialMap A R σ x t) = polynomialMap A R σ x (MvPolynomial.pderiv i t) := by
  induction t using MvPolynomial.induction_on with
  | C t =>
    change D i (MvPolynomial.aeval (fun i => algebraMap R G (x i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)
      (MvPolynomial.C t)) = _
    rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply A R G,
      Derivation.map_algebraMap, MvPolynomial.pderiv_C, map_zero]
  | add s t hs ht => simp only [map_add, hs, ht]
  | mul_X t j ht =>
    rw [map_mul, (D i).leibniz, derivative_X, ht, MvPolynomial.pderiv_mul]
    simp only [smul_eq_mul, map_add, map_mul]
    ac_rfl

omit [Algebra A R] in
theorem polynomial_derivatives_commute (i j : σ) :
    Function.Commute (MvPolynomial.pderiv (R := A) i) (MvPolynomial.pderiv j) := by
  classical
  have hc : ⁅(MvPolynomial.pderiv i : Derivation A (MvPolynomial σ A) (MvPolynomial σ A)),
      (MvPolynomial.pderiv j : Derivation A (MvPolynomial σ A) (MvPolynomial σ A))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro l
    simp [Derivation.commutator_apply, MvPolynomial.pderiv_X, Pi.single_apply, apply_ite]
  intro t
  exact sub_eq_zero.mp (Derivation.congr_fun hc t)

def derivatives (i : σ) : Module.End A G := (D i).toLinearMap.restrictScalars A

theorem derivatives_commute (i j : σ) : Function.Commute (derivatives A R σ i) (derivatives A R σ j) :=
  FreeDivided.Derivation.FreeDividedDerivation.derivations_commute R σ i j

def polynomialComplex [Fintype σ] : CochainComplex (ModuleCat A) ℕ :=
  Koszul.Tensor.KoszulTensor.complex A σ (MvPolynomial σ A) (fun i => (MvPolynomial.pderiv i).toLinearMap)
    (polynomial_derivatives_commute A σ)

def linearizedComplex [Fintype σ] : CochainComplex (ModuleCat A) ℕ :=
  Koszul.Tensor.KoszulTensor.complex A σ G (derivatives A R σ) (derivatives_commute A R σ)

def chainMap [Fintype σ] : polynomialComplex A σ ⟶ linearizedComplex A R σ :=
  Koszul.TensorMap.KoszulTensorMap.map A σ (MvPolynomial σ A) G (fun i => (MvPolynomial.pderiv i).toLinearMap)
    (derivatives A R σ) (polynomialMap A R σ x).toLinearMap
    (fun i t => (derivative_polynomialMap A R σ x i t).symm)
    (polynomial_derivatives_commute A σ) (derivatives_commute A R σ)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential
