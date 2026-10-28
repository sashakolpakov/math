import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamDiagram

/-! # Ordinary Reduction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryReduction.OrdinaryReductionDiagramSquare

noncomputable section

/-! A commuting square of algebra diagrams induces a commuting square
of their original ordinary de Rham coefficient reductions. -/

open _root_.CategoryTheory

universe u v w
variable (R : Type u) [CommRing R] (I : Ideal R)
  {C : Type v} [Category.{w} C]
  (A B A' B' : C ⥤ CommAlgCat.{u} R) (α : A ⟶ B) (β : A' ⟶ B')
  (hB : ∀ X r, r ∈ I → algebraMap R (B.obj X) r = 0)
  (hB' : ∀ X r, r ∈ I → algebraMap R (B'.obj X) r = 0)
  (f : A ⟶ A') (g : B ⟶ B') (h : α ≫ g = f ≫ β)

include h in
theorem natural : OrdinaryDeRhamDiagram.OrdinaryDeRhamReductionDiagram.transformation R I A B α hB ≫
    Functor.whiskerRight g (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor R) =
      Functor.whiskerRight f (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor R ⋙
        (IntegralComparison.Module.IdealQuotient.functor R I).mapHomologicalComplex (.up ℕ)) ≫
      OrdinaryDeRhamDiagram.OrdinaryDeRhamReductionDiagram.transformation R I A' B' β hB' := by
  apply NatTrans.ext
  funext X
  exact OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.naturality R I (α.app X) (hB X)
    (β.app X) (hB' X) (f.app X) (g.app X) (congrArg (fun a => a.app X) h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryReduction.OrdinaryReductionDiagramSquare
