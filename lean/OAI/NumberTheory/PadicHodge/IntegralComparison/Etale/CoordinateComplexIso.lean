import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.OrdinaryCoordinates

/-! # Coordinate Complex Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateComplexIso

noncomputable section

/-! The etale coordinate complex identification retains its original differential-symbol formula. -/

open _root_.CategoryTheory

universe u

variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Algebra (MvPolynomial ι R) A] [IsScalarTower R (MvPolynomial ι R) A]
  [Algebra.FormallyEtale (MvPolynomial ι R) A] [Fintype ι] [LinearOrder ι]

def iso : OrdinaryCoordinates.Ordinary.complex R A ι ≅ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A :=
  (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor.PDDeRhamTensor.complexIso R A ι ⊥ (dividedPowersBot A)
    (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A ι)
    (fun i => (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A ι i).toLinearMap)
    (OrdinaryCoordinates.Ordinary.D_eq_sum R A ι)
    (OrdinaryCoordinates.Ordinary.basis R A ι) (OrdinaryCoordinates.Ordinary.basis_apply R A ι)
    (CoordinateDerivations.commute R A ι)) ≪≫
      (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.complexIso R A).symm

theorem component (n : ℕ) : ((iso R A ι).hom.f n).hom =
    ((OrdinaryCoordinates.Ordinary.formsEquiv R A ι n).restrictScalars R).toLinearMap := rfl

theorem word (n : ℕ) (a : A) (v : Fin n → ι) :
    (iso R A ι).hom.f n (TensorProduct.tmul R a
      (exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1))) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A ι ∘ v) :=
  OrdinaryCoordinates.Ordinary.formsEquiv_word R A ι n a v

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateComplexIso
