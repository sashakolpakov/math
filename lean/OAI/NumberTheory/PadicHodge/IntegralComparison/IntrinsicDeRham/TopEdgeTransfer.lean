import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer

/-! # Top Edge Transfer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdgeTransfer.Intrinsic

noncomputable section

/-! The native top-form edge commutes with actual finite étale
pullback and trace. The maps on top forms are the corresponding
degree rows of those genuine de Rham maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdge.Intrinsic

universe u

private theorem homology_hom_inv {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (e : K ≅ L) (n : ℕ) (x : L.homology n) :
    HomologicalComplex.homologyMap e.hom n (HomologicalComplex.homologyMap e.inv n x) = x :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyMapIso e n).inv_hom_id x

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  {ι : Type u} (U : ι → Y.left.Opens) (g : ℕ)
  [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  [SmoothOfRelativeDimension g Y.hom] [IsProper Y.hom]

local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R X Y f U

def pullback : TopEdge.Intrinsic.source R Y U g →ₗ[R] TopEdge.Intrinsic.source R X V g :=
  (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R X V g).inv g).hom.comp
    ((HomologicalComplex.homologyMap ((CechTransfer.Intrinsic.pullback R X Y f U).f g) g).hom.comp
      (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R Y U g).hom g).hom)

theorem pullback_edge (x : TopEdge.Intrinsic.source R Y U g) :
    HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map (CechTransfer.Intrinsic.pullback R X Y f U) (.up ℕ)) (g + g)
        (TopEdge.Intrinsic.map R Y U g x) =
      TopEdge.Intrinsic.map R X V g (pullback R X Y f U g x) := by
  have h := TopRowEdgeNaturality.naturality (CechComplex.Intrinsic.bicomplex R Y U) (CechComplex.Intrinsic.bicomplex R X V) g
    (TopEdge.Intrinsic.outgoing R Y U g) (TopEdge.Intrinsic.outgoing R X V g) (CechTransfer.Intrinsic.pullback R X Y f U) g
    (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R Y U g).hom g x)
  change _ = TopRowEdge.map (CechComplex.Intrinsic.bicomplex R X V) g (TopEdge.Intrinsic.outgoing R X V g) g
    (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R X V g).hom g
      (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R X V g).inv g
        (HomologicalComplex.homologyMap ((CechTransfer.Intrinsic.pullback R X Y f U).f g) g
          (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R Y U g).hom g x))))
  rw [homology_hom_inv]
  exact h

variable [IsFinite f.left] [Etale f.left]

def trace : TopEdge.Intrinsic.source R X V g →ₗ[R] TopEdge.Intrinsic.source R Y U g := by
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth g Y.hom
  exact (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R Y U g).inv g).hom.comp
    ((HomologicalComplex.homologyMap ((CechTransfer.Intrinsic.trace R X Y f U).f g) g).hom.comp
      (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R X V g).hom g).hom)

theorem trace_edge (x : TopEdge.Intrinsic.source R X V g) :
    letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth g Y.hom
    HomologicalComplex.homologyMap
        (CechTransfer.Intrinsic.totalTrace R X Y f U) (g + g)
        (TopEdge.Intrinsic.map R X V g x) =
      TopEdge.Intrinsic.map R Y U g (trace R X Y f U g x) := by
  let : Smooth Y.hom := SmoothOfRelativeDimension.smooth g Y.hom
  have h := TopRowEdgeNaturality.naturality (CechComplex.Intrinsic.bicomplex R X V) (CechComplex.Intrinsic.bicomplex R Y U) g
    (TopEdge.Intrinsic.outgoing R X V g) (TopEdge.Intrinsic.outgoing R Y U g) (CechTransfer.Intrinsic.trace R X Y f U) g
    (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R X V g).hom g x)
  change _ = TopRowEdge.map (CechComplex.Intrinsic.bicomplex R Y U) g (TopEdge.Intrinsic.outgoing R Y U g) g
    (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R Y U g).hom g
      (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R Y U g).inv g
        (HomologicalComplex.homologyMap ((CechTransfer.Intrinsic.trace R X Y f U).f g) g
          (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R X V g).hom g x))))
  rw [homology_hom_inv]
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdgeTransfer.Intrinsic
