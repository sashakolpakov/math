import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopSingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTopEdge

/-! # Top Single Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopSingleEdge.Intrinsic

noncomputable section

/-! The actual top-form single map induces the original native top-row
edge, with exactly the sign from the original total-flip comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex.Intrinsic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  {ι : Type u} (U : ι → X.left.Opens)

theorem row :
    (Functor.SingleTotal.rowIso (TopSingleCoordinates.Intrinsic.functor R X U)
      (TopSingleCoordinates.Intrinsic.module R X g) g).inv ≫
        (TopSingle.Intrinsic.bicomplexMap R X g U).f g =
      (TopEdge.Intrinsic.rowIso R X U g).hom := by
  rw [TopSingleCoordinates.Intrinsic.bicomplexMap_row]
  simp only [Iso.inv_hom_id_assoc]

theorem map_apply (x : TopEdge.Intrinsic.source R X U g) :
    homologyMap (TopSingle.Intrinsic.totalMap R X g U) (g+g)
      ((TopSingleCoordinates.Intrinsic.sourceIso R X g U g).inv x) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      TopEdge.Intrinsic.map R X U g x := by
  have h := Functor.SingleTopEdge.map_apply
    (TopSingleCoordinates.Intrinsic.functor R X U)
    (TopSingleCoordinates.Intrinsic.module R X g) g
    (CechComplex.Intrinsic.bicomplex R X U) (TopEdge.Intrinsic.outgoing R X U g)
    (TopSingle.Intrinsic.bicomplexMap R X g U) x
  rw [row] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopSingleEdge.Intrinsic
