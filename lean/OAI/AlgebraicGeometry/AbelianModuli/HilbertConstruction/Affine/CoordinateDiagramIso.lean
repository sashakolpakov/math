import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSchemeDiagrams

/-! # Coordinate Diagram Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateDiagramIso

noncomputable section

/-! The affine coordinate presentations give a natural isomorphism of entire affine diagrams. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

theorem affineOverIso_natural (C : Type u) [CommRing C]
    {X Y : Over (Spec (.of C))} [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    f ≫ (OverChartPoints.affineOverIso C Y).hom = (OverChartPoints.affineOverIso C X).hom ≫
      (algSpec (.of C)).map (CommAlgCat.ofHom
        (X := ↥(OverChartPoints.affineOverAlgebra C Y)) (Y := ↥(OverChartPoints.affineOverAlgebra C X)) (OverMorphisms.affineOverMap C f)).op := by
  let ex : X.left ⟶ Spec (.of (OverChartPoints.affineOverAlgebra C X)) := (OverChartPoints.affineOverIso C X).hom.left
  let dx : Spec (.of (OverChartPoints.affineOverAlgebra C X)) ⟶ X.left := (OverChartPoints.affineOverIso C X).inv.left
  let ey : Y.left ⟶ Spec (.of (OverChartPoints.affineOverAlgebra C Y)) := (OverChartPoints.affineOverIso C Y).hom.left
  have he : ex ≫ dx = 𝟙 X.left := congrArg (fun k => k.left) (OverChartPoints.affineOverIso C X).hom_inv_id
  have hf : Spec.map (CommRingCat.ofHom (OverMorphisms.affineOverMap C f).toRingHom) = dx ≫ f.left ≫ ey :=
    OverMorphisms.affineOverMap_spec C f
  apply Over.OverMorphism.ext
  change f.left ≫ ey = ex ≫ Spec.map (CommRingCat.ofHom (OverMorphisms.affineOverMap C f).toRingHom)
  rw [hf, ← Category.assoc, he, Category.id_comp]

def affineCoordinateDiagramIso (C : Type u) [CommRing C]
    {J : Type v} [Category.{w} J] (F : J ⥤ Over (Spec (.of C)))
    [∀ i, IsAffine (F.obj i).left] : F ≅ AlgebraSchemeDiagrams.algebraSchemeDiagram C (CoordinateFunctor.affineCoordinateFunctor C F) :=
  NatIso.ofComponents (fun i => OverChartPoints.affineOverIso C (F.obj i)) (fun h => affineOverIso_natural C (F.map h))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateDiagramIso
