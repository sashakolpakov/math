import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.TopSingle
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopSingleEdge

/-! # Top Single Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.TopSingleEdge.Intrinsic

noncomputable section

/-! The original native edge and the ordered single-coefficient map
agree after the actual ordinary-to-ordered projection, with their sign. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  {ι : Type u} [LinearOrder ι] (U : ι → X.left.Opens)

omit [SmoothOfRelativeDimension g X.hom] [IsProper X.hom] in
theorem source_coordinate (x : IntrinsicDeRham.TopEdge.Intrinsic.source R X U g) :
    homologyMap (TopSingle.Intrinsic.sourceProjection R X g U) (g+g)
      ((IntrinsicDeRham.TopSingleCoordinates.Intrinsic.sourceIso R X g U g).inv x) =
    (TopSingle.Intrinsic.sourceIso R X g U g).inv
      (homologyMap (OrderedCech.Projection.map U
        (IntrinsicDeRham.TopSingleCoordinates.Intrinsic.module R X g)) g x) := by
  have h := congrArg
    (fun a => (IntrinsicDeRham.TopSingleCoordinates.Intrinsic.sourceIso R X g U g).inv ≫ a ≫
      (TopSingle.Intrinsic.sourceIso R X g U g).inv)
    (TopSingle.Intrinsic.sourceProjection_coordinate R X g U g)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at h
  exact ConcreteCategory.congr_hom h x

theorem map_apply (x : IntrinsicDeRham.TopEdge.Intrinsic.source R X U g) :
    homologyMap (TopSingle.Intrinsic.map R X g U) (g+g)
      ((TopSingle.Intrinsic.sourceIso R X g U g).inv
        (homologyMap (OrderedCech.Projection.map U
          (IntrinsicDeRham.TopSingleCoordinates.Intrinsic.module R X g)) g x)) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      homologyMap (TopSingle.Intrinsic.targetProjection R X U) (g+g)
        (IntrinsicDeRham.TopEdge.Intrinsic.map R X U g x) := by
  have h := ConcreteCategory.congr_hom (TopSingle.Intrinsic.naturality R X g U (g+g))
    ((IntrinsicDeRham.TopSingleCoordinates.Intrinsic.sourceIso R X g U g).inv x)
  rw [← source_coordinate R X g U x]
  calc
    _ = homologyMap (TopSingle.Intrinsic.targetProjection R X U) (g+g)
        (homologyMap (IntrinsicDeRham.TopSingle.Intrinsic.totalMap R X g U) (g+g)
          ((IntrinsicDeRham.TopSingleCoordinates.Intrinsic.sourceIso R X g U g).inv x)) := h.symm
    _ = homologyMap (TopSingle.Intrinsic.targetProjection R X U) (g+g)
        (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g • IntrinsicDeRham.TopEdge.Intrinsic.map R X U g x) := by
      rw [IntrinsicDeRham.TopSingleEdge.Intrinsic.map_apply]
    _ = _ := by
      change homologyMap (TopSingle.Intrinsic.targetProjection R X U) (g+g)
        ((ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g : ℤ) • IntrinsicDeRham.TopEdge.Intrinsic.map R X U g x) = _
      exact map_zsmul (homologyMap (TopSingle.Intrinsic.targetProjection R X U) (g+g)).hom _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.TopSingleEdge.Intrinsic
