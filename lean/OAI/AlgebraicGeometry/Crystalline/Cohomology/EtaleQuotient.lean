import OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleDeRham
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.IdealScalarNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.DeRhamComplex

/-! # Etale Quotient -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleQuotient.EtaleQuotientScalarExtension

noncomputable section

/-! Integral scalar extension of the full de Rham complexes at every coefficient-ideal level. -/

open _root_.CategoryTheory

universe u
variable (R S A B σ τ : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B] [Module.Flat R S]
  [LinearOrder σ] [LinearOrder τ]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) A]
  [Algebra (MvPolynomial τ S) B] [IsScalarTower S (MvPolynomial τ S) B]
  [Algebra.FormallyEtale (MvPolynomial τ S) B] (I : Ideal R)

abbrev scalarComplexFunctor : CochainComplex (ModuleCat.{u} R) ℕ ⥤ CochainComplex (ModuleCat.{u} S) ℕ :=
  (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S).mapHomologicalComplex (.up ℕ)

local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleQuotient.EtaleQuotientScalarExtension.scalarComplexFunctor R S
local notation "J" => I.map (algebraMap R S)

def coefficientIso : (F).obj (NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.complex R I (DeRhamPresentationTo.DeRhamPresentation.complex R A)) ≅
    NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.complex S J (DeRhamPresentationTo.DeRhamPresentation.complex S B) :=
  (Cohomology.Module.IdealScalarNaturality.ModuleIdealScalarNaturality.complexIso R S I (DeRhamPresentationTo.DeRhamPresentation.complex R A)).symm ≪≫
    ((NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.functor S J).mapHomologicalComplex (.up ℕ)).mapIso
      (EtaleDeRham.EtaleDeRhamScalarExtension.complexIso R S A B σ τ)

def complexIso : (F).obj (DeRhamPresentationTo.DeRhamPresentation.complex R (A ⧸ I.map (algebraMap R A))) ≅
    DeRhamPresentationTo.DeRhamPresentation.complex S (B ⧸ (J).map (algebraMap S B)) :=
  (F).mapIso (NumberTheory.PadicHodge.IntegralComparison.Quotient.DeRhamComplex.iso R A σ I
    (NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.coordinate R A σ)
    (NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.kaehlerBasis R A σ)
    (NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.kaehlerBasis_apply R A σ)).symm ≪≫
  coefficientIso R S A B σ τ I ≪≫
  NumberTheory.PadicHodge.IntegralComparison.Quotient.DeRhamComplex.iso S B τ J
    (NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.coordinate S B τ)
    (NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.kaehlerBasis S B τ)
    (NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.kaehlerBasis_apply S B τ)

def cohomologyIso (i : ℕ) : (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S).obj
    ((DeRhamPresentationTo.DeRhamPresentation.complex R (A ⧸ I.map (algebraMap R A))).homology i) ≅
    (DeRhamPresentationTo.DeRhamPresentation.complex S (B ⧸ (J).map (algebraMap S B))).homology i :=
  ((DeRhamPresentationTo.DeRhamPresentation.complex R (A ⧸ I.map (algebraMap R A))).sc i |>.mapHomologyIso
    (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (.up ℕ) i).mapIso
      (complexIso R S A B σ τ I)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleQuotient.EtaleQuotientScalarExtension
