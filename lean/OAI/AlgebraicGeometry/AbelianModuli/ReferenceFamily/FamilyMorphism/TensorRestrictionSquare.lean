import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.TensorCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.DerivationPresheaf

/-! # Tensor Restriction Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.TensorRestrictionSquare

noncomputable section

/-! The original restricted family morphism commutes with both affine
restrictions on coordinate rings and on their actual tensor base changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineOpenDiagram

variable (R T : Type) [CommRing R] [CommRing T] [Algebra R T]
    {X Y : Over (Spec (.of R))} (f : X ⟶ Y)
    (V V' : X.left.affineOpens) (W W' : Y.left.affineOpens)
    (t : V'.1 ≤ V.1) (s : W'.1 ≤ W.1)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (h' : V'.1 ≤ f.left ⁻¹ᵁ W'.1)

theorem familyMorphismAffineCoordinates_square :
    (Affine.OpenDiagram.familyAffineCoordinateMap R X t).comp (TensorCoordinates.familyMorphismAffineCoordinates R f V W h) =
      (TensorCoordinates.familyMorphismAffineCoordinates R f V' W' h').comp (Affine.OpenDiagram.familyAffineCoordinateMap R Y s) := by
  have : IsAffine (HilbertConstruction.Open.ParameterPoints.openParameterScheme X V.1).left := V.2
  have : IsAffine (HilbertConstruction.Open.ParameterPoints.openParameterScheme X V'.1).left := V'.2
  have : IsAffine (HilbertConstruction.Open.ParameterPoints.openParameterScheme Y W.1).left := W.2
  have : IsAffine (HilbertConstruction.Open.ParameterPoints.openParameterScheme Y W'.1).left := W'.2
  have H := congrArg
    (HilbertConstruction.Affine.OverMorphisms.affineOverMap R (X := (Affine.OpenDiagram.familyAffineOpenDiagram X).obj V') (Y := (Affine.OpenDiagram.familyAffineOpenDiagram Y).obj W))
    (OpenRestrictions.familyMorphismOpenRestriction_square f t s h h')
  rw [HilbertConstruction.Affine.OverFunctoriality.affineOverMap_comp, HilbertConstruction.Affine.OverFunctoriality.affineOverMap_comp] at H
  exact H

theorem familyMorphismTensorCoordinates_square :
    (FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R T X t).comp (TensorCoordinates.familyMorphismTensorCoordinates R T f V W h) =
      (TensorCoordinates.familyMorphismTensorCoordinates R T f V' W' h').comp (FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R T Y s) := by
  apply AlgHom.ext
  intro u
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul c a =>
    exact congrArg (fun b => c ⊗ₜ[R] b) (AlgHom.congr_fun (familyMorphismAffineCoordinates_square R f V V' W W' t s h h') a)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.TensorRestrictionSquare
