import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariablePrimitive
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.PartialPrimitive
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.SuccessiveHomotopy
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialEq

/-! # Multivariable Koszul -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariableKoszul.PrimeMultivariableKoszul

noncomputable section

/-! # Integral coordinate homotopies on the actual ordinary polynomial form complex -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [Fintype σ]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W

abbrev derivatives (i : σ) : Module.End W P := (MvPolynomial.pderiv i).toLinearMap

local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariableKoszul.PrimeMultivariableKoszul.derivatives p k σ
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariablePrimitive.PrimeMultivariablePrimitive.primitive p k σ
local notation "comm" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomial_derivatives_commute W σ
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomialComplex W σ

def projection (i : σ) : K ⟶ K :=
  Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.projectionChain W σ P D i (S i) comm

def homotopy (i : σ) : Homotopy (𝟙 K) (projection p k σ i) :=
  Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.homotopy W σ P D i (S i) comm

omit [Fintype σ] in
theorem primitive_commutes (i j : σ) (hji : j ≠ i) (a : P) :
    MvPolynomial.pderiv j (S i a) = S i (MvPolynomial.pderiv j a) :=
  LinearMap.congr_fun (MultivariablePrimitive.PrimeMultivariablePrimitive.derivative_commutes p k σ i j hji.symm) a

theorem projection_f (i : σ) (n : ℕ) : (projection p k σ i).f n =
    ModuleCat.ofHom (Koszul.PartialPrimitive.KoszulPartialPrimitive.projection W σ P D i (S i) n) :=
  Koszul.PartialPrimitive.KoszulPartialPrimitive.projectionChain_f W σ P D i (S i) (primitive_commutes p k σ i) comm n

omit [Fintype σ] in
theorem coefficient_zero (i : σ) : Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection W σ P D i (S i) =
    MultivariablePrimitive.PrimeMultivariablePrimitive.projection p k σ i 0 :=
  sub_eq_iff_eq_add.mpr ((MultivariablePrimitive.PrimeMultivariablePrimitive.primitive_derivative p k σ i).symm.trans (add_comm _ _))

omit [Fintype σ] in
theorem coefficient_one (i : σ) : Koszul.PartialPrimitive.KoszulPartialPrimitive.projectionOne W σ P D i (S i) =
    MultivariablePrimitive.PrimeMultivariablePrimitive.projection p k σ i 1 :=
  sub_eq_iff_eq_add.mpr ((MultivariablePrimitive.PrimeMultivariablePrimitive.derivative_primitive p k σ i).symm.trans (add_comm _ _))

def successive (l : List σ) : K ⟶ K := Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.chain W σ P D S comm l

def successiveHomotopy (l : List σ) : Homotopy (𝟙 K) (successive p k σ l) :=
  Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.homotopy W σ P D S comm l

def ordinaryProjection (l : List σ) : DeRhamPresentationTo.DeRhamPresentation.complex W P ⟶ DeRhamPresentationTo.DeRhamPresentation.complex W P :=
  (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.complexIso W σ).inv ≫ successive p k σ l ≫
    (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.complexIso W σ).hom

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariableKoszul.PrimeMultivariableKoszul
