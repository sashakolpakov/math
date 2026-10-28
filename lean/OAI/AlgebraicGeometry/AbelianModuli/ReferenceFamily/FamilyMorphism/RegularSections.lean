import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.TensorCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.RegularSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationSectionMorphism

/-! # Regular Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.RegularSections

noncomputable section

/-! The literal fixed-fiber tensor morphism is exactly the original
scheme pullback on regular sections over compatible affine subfamilies. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver FixedFiber.AffineDiagram.fixedFiberTensorDiagram FixedFiber.AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineCoordinateFunctor HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

variable (R k : Type) [CommRing R] [CommRing k] [Algebra R k]
    {X Y : Over (Spec (.of R))} (f : X ⟶ Y)
    (V : X.left.affineOpens) (W : Y.left.affineOpens) (h : V.1 ≤ f.left ⁻¹ᵁ W.1)

include h

theorem familyMorphismFixedFiber_open_le :
    FixedFiber.CoordinateProjection.fixedFiberAffineOpen R k X V ≤
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).map f).left ⁻¹ᵁ FixedFiber.CoordinateProjection.fixedFiberAffineOpen R k Y W := by
  let B := CommAlgCat.of k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W)
  let C := CommAlgCat.of k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let G := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X
  let H := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj Y
  let F : G ⟶ H := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).map f
  let i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ H := FixedFiber.AffineDiagram.fixedFiberTensorInclusion R k Y W
  let j : EtaleSplittingAt.EtaleSplitting.affineOver k C ⟶ G := FixedFiber.AffineDiagram.fixedFiberTensorInclusion R k X V
  have : IsOpenImmersion i.left := FixedFiber.AffineDiagram.fixedFiberTensorInclusion_open R k Y W
  have : IsOpenImmersion j.left := FixedFiber.AffineDiagram.fixedFiberTensorInclusion_open R k X V
  let q := TensorCoordinates.familyMorphismTensorCoordinates R k f V W h
  have hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B C q ≫ i = j ≫ F := TensorCoordinates.familyMorphismTensorCoordinates_inclusion R k f V W h
  have hR := Affine.PresentationSectionMorphism.openRange_preimage_of_square (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B C q).left i.left j.left F.left
    (congrArg Over.Hom.left hi)
  change (FixedFiber.AffineDiagram.fixedFiberTensorInclusion R k X V).left.opensRange ≤ F.left ⁻¹ᵁ
    (FixedFiber.AffineDiagram.fixedFiberTensorInclusion R k Y W).left.opensRange at hR
  rw [FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range, FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range] at hR
  exact hR

theorem fixedFiberRegularSectionEquiv_morphism (a : k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W) :
    FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R k X V (TensorCoordinates.familyMorphismTensorCoordinates R k f V W h a) =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).map f).left.appLE
        (FixedFiber.CoordinateProjection.fixedFiberAffineOpen R k Y W) (FixedFiber.CoordinateProjection.fixedFiberAffineOpen R k X V) (familyMorphismFixedFiber_open_le R k f V W h)
        (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R k Y W a) := by
  let B := CommAlgCat.of k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W)
  let C := CommAlgCat.of k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let G := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X
  let H := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj Y
  let F : G ⟶ H := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).map f
  let i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ H := FixedFiber.AffineDiagram.fixedFiberTensorInclusion R k Y W
  let j : EtaleSplittingAt.EtaleSplitting.affineOver k C ⟶ G := FixedFiber.AffineDiagram.fixedFiberTensorInclusion R k X V
  have : IsOpenImmersion i.left := FixedFiber.AffineDiagram.fixedFiberTensorInclusion_open R k Y W
  have : IsOpenImmersion j.left := FixedFiber.AffineDiagram.fixedFiberTensorInclusion_open R k X V
  let q := TensorCoordinates.familyMorphismTensorCoordinates R k f V W h
  have hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B C q ≫ i = j ≫ F := TensorCoordinates.familyMorphismTensorCoordinates_inclusion R k f V W h
  have hR := Affine.PresentationSectionMorphism.openRange_preimage_of_square (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B C q).left i.left j.left F.left
    (congrArg Over.Hom.left hi)
  have hn := Affine.PresentationSectionMorphism.affinePresentationRegularSectionEquiv_morphism k B C G H i j F q hi hR a
  exact (congrArg (Regular.SectionTransport.regularSectionTransport (FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R k X V)) hn).trans
    (Affine.PresentationSectionMorphism.regularSectionTransport_appLE F.left (FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R k Y W)
      (FixedFiber.CoordinateProjection.fixedFiberTensorInclusion_range R k X V) hR (familyMorphismFixedFiber_open_le R k f V W h)
      (Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv k B H i a))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.RegularSections
