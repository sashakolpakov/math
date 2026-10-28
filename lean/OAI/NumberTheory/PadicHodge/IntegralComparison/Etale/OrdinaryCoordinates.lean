import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateDerivations
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor

/-! # Ordinary Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.OrdinaryCoordinates.Ordinary

noncomputable section

/-! Coordinate forms identify the original de Rham complex of an etale chart. -/

open _root_.CategoryTheory

universe u

variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Algebra (MvPolynomial ι R) A] [IsScalarTower R (MvPolynomial ι R) A]
  [Algebra.FormallyEtale (MvPolynomial ι R) A]

def basis : Module.Basis ι A (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A ⊥ (dividedPowersBot A) 1) :=
  (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.basis R A ι).map
    (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.oneFormsEquiv R A).symm

theorem basis_apply (i : ι) : basis R A ι i =
    AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R A ⊥ (dividedPowersBot A) (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A ι i) := by
  rw [basis, Module.Basis.map_apply, AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.basis_apply]
  exact AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.fromKaehler_D R A _

theorem D_eq_sum [Fintype ι] (a : A) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R A ⊥ (dividedPowersBot A) a =
      ∑ i, AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι i a •
        AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R A ⊥ (dividedPowersBot A)
          (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A ι i) := by
  apply (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.oneFormsEquiv R A).injective
  change AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.toKaehler R A (AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R A ⊥ (dividedPowersBot A) a) =
    AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.toKaehler R A (∑ i, AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι i a •
      AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R A ⊥ (dividedPowersBot A) (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A ι i))
  simp only [map_sum, map_smul, AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.toKaehler_D]
  have hsum := (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.basis R A ι).sum_repr (KaehlerDifferential.D R A a)
  simpa only [AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation, Derivation.coe_comp,
    LinearMap.comp_apply, LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Module.Basis.coord_apply,
    AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.basis_apply] using hsum.symm

def formsEquiv [LinearOrder ι] (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term R ι A n ≃ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n :=
  (AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensor.PDFormsTensor.formsEquiv R A ι ⊥ (dividedPowersBot A)
    (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A ι) (basis R A ι) (basis_apply R A ι) n).trans
      (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv R A n)

theorem formsEquiv_word [LinearOrder ι] (n : ℕ) (a : A) (v : Fin n → ι) :
    formsEquiv R A ι n (TensorProduct.tmul R a
      (exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1))) =
        AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A ι ∘ v) := by
  change AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv R A n
    (AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensor.PDFormsTensor.formsEquiv R A ι ⊥ (dividedPowersBot A)
      (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A ι) (basis R A ι) (basis_apply R A ι) n _) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensor.PDFormsTensor.formsEquiv_word, AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv_symbol]

def complex [Fintype ι] : CochainComplex (ModuleCat R) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex R ι A (fun i => (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι i).toLinearMap)
    (CoordinateDerivations.commute R A ι)

def complexIso [Fintype ι] : complex R A ι ≅ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A := by
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  exact (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor.PDDeRhamTensor.complexIso R A ι ⊥ (dividedPowersBot A)
    (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A ι)
    (fun i => (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι i).toLinearMap) (D_eq_sum R A ι)
    (basis R A ι) (basis_apply R A ι) (CoordinateDerivations.commute R A ι)) ≪≫
      (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.complexIso R A).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.OrdinaryCoordinates.Ordinary
