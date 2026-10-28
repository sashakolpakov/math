import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorCoordinateIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateFiniteType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineSchemeModels

/-! # Affine Functor Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AffineFunctorModels

noncomputable section

/-! Isomorphic recovered affine diagrams admit compatible closed models without flatness of the ambient charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

theorem exists_closed_affine_functor_model
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {J : Type v} [Category.{w} J] [Finite J]
    (F G : J ⥤ Over (Spec (.of C)))
    [∀ i, IsAffine (F.obj i).left] [∀ i, IsAffine (G.obj i).left]
    [∀ i, Smooth (F.obj i).hom] [∀ i, LocallyOfFiniteType (G.obj i).hom]
    (e : F ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R))) ≅
      G ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R))))
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ M : AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R)
      (Affine.CoordinateFunctor.affineCoordinateFunctor C G) (Affine.CoordinateFunctor.affineCoordinateFunctor C F), E ≤ M.coefficients := by
  have (i : Jᵒᵖ) : Algebra.Smooth C ((Affine.CoordinateFunctor.affineCoordinateFunctor C F).obj i) :=
    HilbertConstruction.Smooth.AffineSchemeModels.affineOverAlgebra_smooth C (F.obj i.unop)
  have (i : Jᵒᵖ) : Algebra.FiniteType C ((Affine.CoordinateFunctor.affineCoordinateFunctor C G).obj i) :=
    Affine.CoordinateFiniteType.affineOverAlgebra_finiteType C (G.obj i.unop)
  exact AlgebraDiagramModel.exists_closedAlgebraDiagramModel (Affine.CoordinateFunctor.affineCoordinateFunctor C G) (Affine.CoordinateFunctor.affineCoordinateFunctor C F)
    (Affine.TensorCoordinateIso.affineTensorCoordinateMap F G e) (Affine.TensorCoordinateIso.affineTensorCoordinateMap_bijective F G e) E hE

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AffineFunctorModels
