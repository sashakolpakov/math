import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorDiagramIso

/-! # Tensor Coordinate Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorCoordinateIso

noncomputable section

/-! An isomorphism of base-changed affine diagrams gives compatible isomorphisms of their tensor coordinate algebras. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
variable {J : Type v} [Category.{w} J] (F G : J ⥤ Over (Spec (.of C)))
variable [∀ i, IsAffine (F.obj i).left] [∀ i, IsAffine (G.obj i).left]
variable (e : F ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R))) ≅
  G ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R))))

def affineTensorCoordinateOppositeIso :
    (CoordinateFunctor.affineCoordinateFunctor C F ⋙ AlgebraTensorFunctor.algebraTensorFunctor C R).rightOp ≅
    (CoordinateFunctor.affineCoordinateFunctor C G ⋙ AlgebraTensorFunctor.algebraTensorFunctor C R).rightOp := by
  letI := (algSpec.fullyFaithful (R := CommRingCat.of R)).full
  letI := (algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  exact Functor.fullyFaithfulCancelRight (algSpec (.of R))
    (TensorDiagramIso.affineTensorDiagramIso C R F ≪≫ e ≪≫ (TensorDiagramIso.affineTensorDiagramIso C R G).symm)

def affineTensorCoordinateMap :
    CoordinateFunctor.affineCoordinateFunctor C G ⋙ AlgebraTensorFunctor.algebraTensorFunctor C R ⟶
    CoordinateFunctor.affineCoordinateFunctor C F ⋙ AlgebraTensorFunctor.algebraTensorFunctor C R :=
  (affineTensorCoordinateOppositeIso F G e).hom.removeRightOp

theorem affineTensorCoordinateMap_bijective (i : Jᵒᵖ) :
    Function.Bijective ((affineTensorCoordinateMap F G e).app i).hom :=
  (CommAlgCat.algEquivOfIso ((affineTensorCoordinateOppositeIso F G e).app i.unop).unop).bijective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorCoordinateIso
