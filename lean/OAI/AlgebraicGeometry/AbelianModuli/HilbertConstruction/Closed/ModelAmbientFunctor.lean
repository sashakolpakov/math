import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ModelAmbientBaseChange

/-! # Model Ambient Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! Iterated ambient coefficient change is functorial and transports isomorphisms of original ambient schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
variable {J : Type v} [Category.{w} J] {A B : Jᵒᵖ ⥤ CommAlgCat.{u} C}
variable (M : AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R) A B) (D : Subalgebra M.closingCoefficients R)

abbrev AlgebraDiagramModel.ClosedAlgebraDiagramModel.ambientBaseChangeFunctor : Over (Spec (.of C)) ⥤ Over (Spec (.of D)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C M.coefficients))) ⋙
    Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients M.closingCoefficients)))) ⋙
      Over.pullback (Spec.map (CommRingCat.ofHom (R := M.closingCoefficients) (S := D)
        (algebraMap M.closingCoefficients D)))

def AlgebraDiagramModel.ClosedAlgebraDiagramModel.ambientBaseChangeIso {X Y : Over (Spec (.of C))} (e : X ≅ Y) :
    M.ambientBaseChange D X ≅ M.ambientBaseChange D Y :=
  (M.ambientBaseChangeFunctor D).mapIso e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
