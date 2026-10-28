import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackCartesianMap

/-! # Coordinate Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection

noncomputable section

section

/-! The images of the actual fixed-fiber affine charts are exactly
the inverse images of the original affine opens. Tensor coordinates
preserve those same open images. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R k : Type) [CommRing R] [CommRing k] [Algebra R k]
    (X : Over (Spec (.of R)))

def fixedFamilyProjection :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X).left ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R k)))

def fixedFiberAffineOpen (V : X.left.affineOpens) :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X).left.Opens :=
  (fixedFamilyProjection R k X) ⁻¹ᵁ V.1

theorem fixedFiberAffineInclusion_range (V : X.left.affineOpens) :
    (AffineDiagram.fixedFiberAffineInclusion R k X V).left.opensRange = fixedFiberAffineOpen R k X V := by
  have h := OverPullbackOpenCover.overPullback_map_opensRange (Spec.map (CommRingCat.ofHom (algebraMap R k)))
    (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X V.1)
  change (AffineDiagram.fixedFiberAffineInclusion R k X V).left.opensRange =
    (fixedFamilyProjection R k X) ⁻¹ᵁ (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X V.1).left.opensRange at h
  exact h.trans (congrArg (fun U => (fixedFamilyProjection R k X) ⁻¹ᵁ U) V.1.opensRange_ι)

theorem fixedFiberTensorInclusion_range (V : X.left.affineOpens) :
    (AffineDiagram.fixedFiberTensorInclusion R k X V).left.opensRange = fixedFiberAffineOpen R k X V := by
  have : IsIso ((AffineDiagram.fixedFiberAffineCoordinates R k X).inv.app V).left :=
    (Over.forget _).map_isIso ((AffineDiagram.fixedFiberAffineCoordinates R k X).inv.app V)
  change (((AffineDiagram.fixedFiberAffineCoordinates R k X).inv.app V).left ≫
    (AffineDiagram.fixedFiberAffineInclusion R k X V).left).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact fixedFiberAffineInclusion_range R k X V

end

/-! The tensor coordinate charts of a fixed fiber commute with the
original projection to the family. The resulting coordinate map is the
literal right inclusion into the base-change tensor algebra. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R k : Type) [CommRing R] [CommRing k] [Algebra R k]

theorem affineBaseChangeCoordinates_inv_fst
    (X : Over (Spec (.of R))) [IsAffine X.left] :
    (Affine.BaseChangeCoordinates.affineBaseChangeCoordinates R k X).inv.left ≫
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R X →ₐ[R]
        k ⊗[R] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R X).toRingHom) ≫
      (HilbertConstruction.Affine.OverChartPoints.affineOverIso R X).inv.left := by
  let A := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R X
  let a : X ≅ EtaleSplittingAt.EtaleSplitting.affineOver R A := HilbertConstruction.Affine.OverChartPoints.affineOverIso R X
  let f := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let b := (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R A k).hom.left
  change (b ≫ ((Over.pullback f).map a.inv).left) ≫ pullback.fst X.hom f = _
  calc
    _ = b ≫ (((Over.pullback f).map a.inv).left ≫ pullback.fst X.hom f) :=
      Category.assoc _ _ _
    _ = b ≫ (pullback.fst (EtaleSplittingAt.EtaleSplitting.affineOver R A).hom f ≫ a.inv.left) :=
      congrArg (fun m => b ≫ m) (OverPullbackCartesianMap.overPullback_map_isPullback f a.inv).w
    _ = (b ≫ pullback.fst (EtaleSplittingAt.EtaleSplitting.affineOver R A).hom f) ≫ a.inv.left :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun m => m ≫ a.inv.left) (Affine.AlgebraAutomorphismNaturality.affineBaseChangeIso_hom_fst R A k)

theorem fixedFiberTensorInclusion_projection
    (X : Over (Spec (.of R))) (V : X.left.affineOpens) :
    (AffineDiagram.fixedFiberTensorInclusion R k X V).left ≫ fixedFamilyProjection R k X =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj V) →ₐ[R]
          k ⊗[R] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj V)).toRingHom) ≫
        (HilbertConstruction.Affine.OverChartPoints.affineOverIso R ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj V)).inv.left ≫ V.1.ι := by
  let Y := (Affine.OpenDiagram.familyAffineOpenDiagram X).obj V
  let i : Y ⟶ X := HilbertConstruction.Open.ParameterPoints.openParameterInclusion X V.1
  let f := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let b := (Affine.BaseChangeCoordinates.affineBaseChangeCoordinates R k Y).inv.left
  change (b ≫ ((Over.pullback f).map i).left) ≫ pullback.fst X.hom f =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R Y →ₐ[R]
        k ⊗[R] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R Y).toRingHom) ≫
      (HilbertConstruction.Affine.OverChartPoints.affineOverIso R Y).inv.left ≫ i.left
  have hmap := (OverPullbackCartesianMap.overPullback_map_isPullback f i).w
  have hcoord := affineBaseChangeCoordinates_inv_fst R k Y
  exact (Category.assoc b ((Over.pullback f).map i).left (pullback.fst X.hom f)).trans
    ((congrArg (fun m => b ≫ m) hmap).trans
      ((Category.assoc b (pullback.fst Y.hom f) i.left).symm.trans
        ((congrArg (fun m => m ≫ i.left) hcoord).trans (Category.assoc _ _ _))))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection
