import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopSingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjection

/-! # Top Single -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.TopSingle.Intrinsic

noncomputable section

/-! The actual top-form single map commutes with ordinary-to-ordered
Čech projection, with the original single-degree coordinates retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex.Intrinsic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  {ι : Type u} [LinearOrder ι] (U : ι → X.left.Opens)

abbrev source := (single _ (.up ℕ) g).obj (IntrinsicDeRham.TopSingleCoordinates.Intrinsic.module R X g)

abbrev sourceIso (n : ℕ) := Functor.SingleTotal.homologyIso
  (OrderedCech.Functor.Projection.functor U) (IntrinsicDeRham.TopSingleCoordinates.Intrinsic.module R X g) g n

def map := (OrderedCech.TotalProjection.ordered U).map (IntrinsicDeRham.TopSingle.Intrinsic.presheafMap R X g)

def sourceProjection := OrderedCech.TotalProjection.map U (source R X g)

def targetProjection := OrderedCech.TotalProjection.map U (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex R X)

theorem naturality (n : ℕ) :
    homologyMap (IntrinsicDeRham.TopSingle.Intrinsic.totalMap R X g U) n ≫
        homologyMap (targetProjection R X U) n =
      homologyMap (sourceProjection R X g U) n ≫ homologyMap (Intrinsic.map R X g U) n :=
  OrderedCech.TotalProjection.homology_naturality U (IntrinsicDeRham.TopSingle.Intrinsic.presheafMap R X g) n

omit [SmoothOfRelativeDimension g X.hom] [IsProper X.hom] in
theorem sourceProjection_coordinate (n : ℕ) :
    homologyMap (sourceProjection R X g U) (n+g) ≫ (sourceIso R X g U n).hom =
      (IntrinsicDeRham.TopSingleCoordinates.Intrinsic.sourceIso R X g U n).hom ≫
        homologyMap (OrderedCech.Projection.map U (IntrinsicDeRham.TopSingleCoordinates.Intrinsic.module R X g)) n :=
  OrderedCech.TotalProjection.single U (IntrinsicDeRham.TopSingleCoordinates.Intrinsic.module R X g) g n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.TopSingle.Intrinsic
