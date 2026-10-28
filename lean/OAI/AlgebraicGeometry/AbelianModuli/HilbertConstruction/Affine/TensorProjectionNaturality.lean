import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorProjection

/-! # Tensor Projection Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorProjectionNaturality

noncomputable section

/-! Tensor-product maps commute with the actual affine base-change projections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u

variable {C : Type u} [CommRing C]

theorem affineOverMap_spec_inv {X Y : Over (Spec (.of C))}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    Spec.map (CommRingCat.ofHom (OverMorphisms.affineOverMap C f).toRingHom) ≫ (OverChartPoints.affineOverIso C Y).inv.left =
      (OverChartPoints.affineOverIso C X).inv.left ≫ f.left := by
  let d : Spec (.of (OverChartPoints.affineOverAlgebra C X)) ⟶ X.left := (OverChartPoints.affineOverIso C X).inv.left
  let e : Y.left ⟶ Spec (.of (OverChartPoints.affineOverAlgebra C Y)) := (OverChartPoints.affineOverIso C Y).hom.left
  let d' : Spec (.of (OverChartPoints.affineOverAlgebra C Y)) ⟶ Y.left := (OverChartPoints.affineOverIso C Y).inv.left
  have he : e ≫ d' = 𝟙 Y.left := congrArg (fun k => k.left) (OverChartPoints.affineOverIso C Y).hom_inv_id
  have hf : Spec.map (CommRingCat.ofHom (OverMorphisms.affineOverMap C f).toRingHom) = d ≫ f.left ≫ e :=
    OverMorphisms.affineOverMap_spec C f
  change Spec.map (CommRingCat.ofHom (OverMorphisms.affineOverMap C f).toRingHom) ≫ d' = d ≫ f.left
  rw [hf, Category.assoc, Category.assoc, he, Category.comp_id]

theorem affineTensorProjection_natural (R : Type u) [CommRing R] [Algebra C R]
    {X Y : Over (Spec (.of C))} [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R R) (OverMorphisms.affineOverMap C f)).toRingHom) ≫
        TensorProjection.affineTensorProjection C R Y = TensorProjection.affineTensorProjection C R X ≫ f.left := by
  let pX := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
    (R := C) (A := R) (B := OverChartPoints.affineOverAlgebra C X)).toRingHom)
  let pY := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
    (R := C) (A := R) (B := OverChartPoints.affineOverAlgebra C Y)).toRingHom)
  let dX : Spec (.of (OverChartPoints.affineOverAlgebra C X)) ⟶ X.left := (OverChartPoints.affineOverIso C X).inv.left
  let dY : Spec (.of (OverChartPoints.affineOverAlgebra C Y)) ⟶ Y.left := (OverChartPoints.affineOverIso C Y).inv.left
  have hi : Spec.map (CommRingCat.ofHom (OverMorphisms.affineOverMap C f).toRingHom) ≫ dY = dX ≫ f.left :=
    affineOverMap_spec_inv f
  have h := (NaturalTensorMapCartesian.naturalTensorMap_isPullback (R := R) (OverMorphisms.affineOverMap C f)).w
  change Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id R R) (OverMorphisms.affineOverMap C f)).toRingHom) ≫
    (pY ≫ dY) = (pX ≫ dX) ≫ f.left
  rw [← Category.assoc, h, Category.assoc, hi, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorProjectionNaturality
