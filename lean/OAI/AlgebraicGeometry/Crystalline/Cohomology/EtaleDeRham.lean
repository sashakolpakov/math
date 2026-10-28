import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsTensorBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlatScalar

/-! # Etale De Rham -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleDeRham.EtaleDeRhamScalarExtension

noncomputable section

/-! The full ordinary de Rham complexes of etale charts commute with flat integral scalar extension. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u
variable (R S A B σ τ : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B] [Module.Flat R S]
  [LinearOrder σ] [LinearOrder τ]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) A]
  [Algebra (MvPolynomial τ S) B] [IsScalarTower S (MvPolynomial τ S) B]
  [Algebra.FormallyEtale (MvPolynomial τ S) B]

def complexIso : ((NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S).mapHomologicalComplex (.up ℕ)).obj
    (DeRhamPresentationTo.DeRhamPresentation.complex R A) ≅ DeRhamPresentationTo.DeRhamPresentation.complex S B :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (FormsTensorBaseChange.EtaleFormsTensorBaseChange.scalarEquiv R S A B σ τ n).toModuleIso) (by
      intro n m hnm
      change n + 1 = m at hnm
      subst m
      simp only [Functor.mapHomologicalComplex_obj_d, DeRhamPresentationTo.DeRhamPresentation.complex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (FormsTensorBaseChange.EtaleFormsTensorBaseChange.differential R S A B σ τ n x).symm)

def cohomologyIso (n : ℕ) : (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S).obj ((DeRhamPresentationTo.DeRhamPresentation.complex R A).homology n) ≅
    (DeRhamPresentationTo.DeRhamPresentation.complex S B).homology n :=
  ((DeRhamPresentationTo.DeRhamPresentation.complex R A).sc n |>.mapHomologyIso (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℕ) n).mapIso (complexIso R S A B σ τ)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleDeRham.EtaleDeRhamScalarExtension
