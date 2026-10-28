import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarEquivalence
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlatScalar

/-! # De Rham Scalar Extension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.DeRhamScalarExtension.FormsBaseChange

noncomputable section

/-! The actual affine de Rham complexes and their cohomology commute with flat scalar extension. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
  [Algebra ℚ A] [Algebra ℚ B] [Module.Flat R S]

def affineComplexIso :
    ((FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A) ≅ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex S B :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Forms.ScalarEquivalence.FormsBaseChange.formsScalarEquiv R S A B n).toModuleIso) (by
      intro n m hnm
      change n + 1 = m at hnm
      subst m
      simp only [Functor.mapHomologicalComplex_obj_d, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (Forms.ScalarEquivalence.FormsBaseChange.formsScalarEquiv_differential R S A B n x).symm)

def affineCohomologyIso (n : ℕ) :
    (FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S).obj ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A).homology n) ≅
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex S B).homology n :=
  ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A).sc n |>.mapHomologyIso (FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.up ℕ) n).mapIso
      (affineComplexIso R S A B)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.DeRhamScalarExtension.FormsBaseChange
