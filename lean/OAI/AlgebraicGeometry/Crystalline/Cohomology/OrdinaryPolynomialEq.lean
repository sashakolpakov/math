import OAI.AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameDifferential
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor
import Mathlib.RingTheory.Kaehler.Polynomial

/-! # Ordinary Polynomial Eq -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates

noncomputable section

/-!
# Integral coordinate forms of the ordinary polynomial de Rham complex

Kähler differentials of a polynomial algebra have their usual coordinate
basis. The ordered-symbol construction identifies every actual ordinary
form module, including the exterior differential, with the polynomial
coordinate tensor complex. No characteristic-zero assumption is needed.
-/

open _root_.CategoryTheory

universe u

variable (R σ : Type u) [CommRing R]

local notation "P" => MvPolynomial σ R
local notation "I" => (⊥ : Ideal P)
local notation "δ" => dividedPowersBot P

def basis : Module.Basis σ P (PD.DeRham.PDDeRham.Form R P I δ 1) :=
  (KaehlerDifferential.mvPolynomialBasis R σ).map (ZeroIdeal.ZeroIdealPDForms.oneFormsEquiv R P).symm

theorem basis_apply (i : σ) : basis R σ i = PD.OneForms.PDOneForms.D R P I δ (MvPolynomial.X i) := by
  rw [basis, Module.Basis.map_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  exact ZeroIdeal.ZeroIdealPDForms.fromKaehler_D R P (MvPolynomial.X i)

theorem D_eq_sum [Fintype σ] (a : P) :
    PD.OneForms.PDOneForms.D R P I δ a = ∑ i, MvPolynomial.pderiv i a • PD.OneForms.PDOneForms.D R P I δ (MvPolynomial.X i) := by
  apply (ZeroIdeal.ZeroIdealPDForms.oneFormsEquiv R P).injective
  change ZeroIdeal.ZeroIdealPDForms.toKaehler R P (PD.OneForms.PDOneForms.D R P I δ a) =
    ZeroIdeal.ZeroIdealPDForms.toKaehler R P (∑ i, MvPolynomial.pderiv i a • PD.OneForms.PDOneForms.D R P I δ (MvPolynomial.X i))
  simp only [map_sum, map_smul, ZeroIdeal.ZeroIdealPDForms.toKaehler_D]
  have hsum := (KaehlerDifferential.mvPolynomialBasis R σ).sum_repr (KaehlerDifferential.D R P a)
  simpa only [KaehlerDifferential.mvPolynomialBasis_repr_apply,
    KaehlerDifferential.mvPolynomialBasis_apply] using hsum.symm

def formsEquiv [LinearOrder σ] (n : ℕ) :
    Koszul.Tensor.KoszulTensor.Term R σ P n ≃ₗ[P] DeRhamPresentationTo.DeRhamPresentation.Form R P n :=
  (PD.FormsTensor.PDFormsTensor.formsEquiv R P σ I δ MvPolynomial.X (basis R σ) (basis_apply R σ) n).trans
    (ZeroIdeal.ZeroIdealPDForms.formsEquiv R P n)

theorem formsEquiv_word [LinearOrder σ] (n : ℕ) (a : P) (v : Fin n → σ) :
    formsEquiv R σ n (TensorProduct.tmul R a
      (exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1))) =
        DeRhamPresentationTo.DeRhamPresentation.symbol R P a (MvPolynomial.X ∘ v) := by
  change ZeroIdeal.ZeroIdealPDForms.formsEquiv R P n
    (PD.FormsTensor.PDFormsTensor.formsEquiv R P σ I δ MvPolynomial.X (basis R σ) (basis_apply R σ) n _) = _
  rw [PD.FormsTensor.PDFormsTensor.formsEquiv_word, ZeroIdeal.ZeroIdealPDForms.formsEquiv_symbol]

def complexIso [Fintype σ] : Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomialComplex R σ ≅
    DeRhamPresentationTo.DeRhamPresentation.complex R P := by
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact (PD.DeRhamTensor.PDDeRhamTensor.complexIso R P σ I δ MvPolynomial.X
    (fun i => (MvPolynomial.pderiv i).toLinearMap) (D_eq_sum R σ)
    (basis R σ) (basis_apply R σ) (Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomial_derivatives_commute R σ)) ≪≫
      (ZeroIdeal.ZeroIdealPDForms.complexIso R P).symm

/-- Ordinary algebraic polynomial forms map into the divided-coordinate frame complex. -/
def frameMap (A : Type u) [CommRing A] [Algebra R A] (x : σ → A) [Fintype σ] :
    DeRhamPresentationTo.DeRhamPresentation.complex R P ⟶ Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential.linearizedComplex R A σ :=
  (complexIso R σ).inv ≫ Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential.chainMap R A σ x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates
