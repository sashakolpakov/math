import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.OpenRestrictions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineTangentLifts

/-! # Tensor Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.TensorCoordinates

noncomputable section

/-! On actual affine subfamilies, the original family morphism has
literal tensor coordinates after any base change. Those maps commute
with the original inclusions into the whole base-changed family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver FixedFiber.AffineDiagram.fixedFiberTensorDiagram FixedFiber.AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineCoordinateFunctor HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineOpenDiagram

variable (R T : Type) [CommRing R] [CommRing T] [Algebra R T]
    {X Y : Over (Spec (.of R))} (f : X ⟶ Y)
    (V : X.left.affineOpens) (W : Y.left.affineOpens) (h : V.1 ≤ f.left ⁻¹ᵁ W.1)

def familyMorphismAffineCoordinates : Family.AffineTangentLifts.familyAffineRing R Y W →ₐ[R] Family.AffineTangentLifts.familyAffineRing R X V :=
  HilbertConstruction.Affine.OverMorphisms.affineOverMap R (X := (Affine.OpenDiagram.familyAffineOpenDiagram X).obj V)
    (Y := (Affine.OpenDiagram.familyAffineOpenDiagram Y).obj W) (OpenRestrictions.familyMorphismOpenRestriction f V.1 W.1 h)

def familyMorphismTensorCoordinates :
    (T ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W) →ₐ[T] (T ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) :=
  Algebra.TensorProduct.map (AlgHom.id T T) (familyMorphismAffineCoordinates R f V W h)

theorem familyMorphismTensorCoordinates_inclusion :
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom T (T ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W) (T ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
        (familyMorphismTensorCoordinates R T f V W h) ≫ FixedFiber.AffineDiagram.fixedFiberTensorInclusion R T Y W =
      FixedFiber.AffineDiagram.fixedFiberTensorInclusion R T X V ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))).map f := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))
  let a : (Affine.OpenDiagram.familyAffineOpenDiagram X).obj V ⟶ (Affine.OpenDiagram.familyAffineOpenDiagram Y).obj W :=
    OpenRestrictions.familyMorphismOpenRestriction f V.1 W.1 h
  let M := Affine.AlgebraAutomorphismNaturality.affineOverAlgHom T (T ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W) (T ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
    (familyMorphismTensorCoordinates R T f V W h)
  let e := Affine.BaseChangeCoordinates.affineBaseChangeCoordinates R T ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj V)
  let e' := Affine.BaseChangeCoordinates.affineBaseChangeCoordinates R T ((Affine.OpenDiagram.familyAffineOpenDiagram Y).obj W)
  have hi : e.inv ≫ F.map a = M ≫ e'.inv :=
    IsoNaturalitySquares.iso_inverse_square e e' (F.map a) M (Affine.BaseChangeCoordinates.affineBaseChangeCoordinates_natural R T a)
  change M ≫ (e'.inv ≫ F.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion Y W.1)) =
    (e.inv ≫ F.map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X V.1)) ≫ F.map f
  rw [← Category.assoc, ← hi, Category.assoc, ← F.map_comp]
  rw [OpenRestrictions.familyMorphismOpenRestriction_inclusion, F.map_comp, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.TensorCoordinates
