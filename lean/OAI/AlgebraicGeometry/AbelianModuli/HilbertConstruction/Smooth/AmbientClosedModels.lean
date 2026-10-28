import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AmbientFunctorModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AffineFunctorModels

/-! # Ambient Closed Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth

noncomputable section

/-! Smooth recovered ambient diagrams have compatible closed models over finite coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable {R : Type u} [CommRing R] {C : Subalgebra ℤ R}
variable {J : Type v} [Category.{w} J] {G : J ⥤ Over (Spec (.of C))}
variable (M : AmbientFunctorModel.SmoothAmbientFunctorModel C G)

abbrev AmbientFunctorModel.SmoothAmbientFunctorModel.ambient : J ⥤ Over (Spec (.of M.coefficients)) :=
  G ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion M.above).toRingHom))

instance AmbientFunctorModel.SmoothAmbientFunctorModel.source_affine (i : J) : IsAffine (M.source.obj i).left := M.affine i
instance AmbientFunctorModel.SmoothAmbientFunctorModel.source_smooth (i : J) : Smooth (M.source.obj i).hom := M.smooth i

instance AmbientFunctorModel.SmoothAmbientFunctorModel.ambient_affine [∀ i, IsAffine (G.obj i).left] (i : J) :
    IsAffine (M.ambient.obj i).left := Affine.FunctorBaseChange.affineFunctorBaseChange_affine G _ i

instance AmbientFunctorModel.SmoothAmbientFunctorModel.ambient_finiteType [∀ i, LocallyOfFiniteType (G.obj i).hom] (i : J) :
    LocallyOfFiniteType (M.ambient.obj i).hom := Affine.FunctorBaseChange.affineFunctorBaseChange_finiteType G _ i

theorem AmbientFunctorModel.SmoothAmbientFunctorModel.exists_closed_model [Finite J]
    [∀ i, IsAffine (G.obj i).left] [∀ i, LocallyOfFiniteType (G.obj i).hom]
    (E : Subalgebra M.coefficients R) (hE : E.FG) :
    ∃ N : Closed.AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R)
      (Affine.CoordinateFunctor.affineCoordinateFunctor M.coefficients M.ambient)
      (Affine.CoordinateFunctor.affineCoordinateFunctor M.coefficients M.source), E ≤ N.coefficients :=
  Closed.AffineFunctorModels.exists_closed_affine_functor_model M.source M.ambient M.recovery E hE

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth
