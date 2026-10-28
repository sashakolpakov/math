import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamIs

/-! # Ordinary De Rham Diagram -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamDiagram.OrdinaryDeRhamReductionDiagram

noncomputable section

/-! Canonical coefficient reduction assembles over any diagram of
algebra maps whose targets annihilate the coefficient ideal. -/

open _root_.CategoryTheory

universe u v w
variable (R : Type u) [CommRing R] (I : Ideal R)
  {C : Type v} [Category.{w} C] (A B : C ⥤ CommAlgCat.{u} R) (α : A ⟶ B)
  (hB : ∀ X r, r ∈ I → algebraMap R (B.obj X) r = 0)

def transformation : A ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor R ⋙
    (IntegralComparison.Module.IdealQuotient.functor R I).mapHomologicalComplex (.up ℕ) ⟶
      B ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor R where
  app X := OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.map R I (α.app X) (hB X)
  naturality X Y f :=
    (OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.naturality R I (α.app X) (hB X) (α.app Y) (hB Y)
      (A.map f) (B.map f) (α.naturality f).symm).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamDiagram.OrdinaryDeRhamReductionDiagram
