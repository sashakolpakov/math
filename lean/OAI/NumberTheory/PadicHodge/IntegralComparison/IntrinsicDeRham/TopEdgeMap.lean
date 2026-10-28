import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdge

/-! # Top Edge Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdgeMap.Intrinsic

noncomputable section

/-! A morphism of the actual de Rham Čech bicomplexes preserves
the top-form edge, including maps between different affine covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdge.Intrinsic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R)))
  {ι κ : Type u} (U : ι → X.left.Opens) (V : κ → Y.left.Opens) (g : ℕ)
  [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  [SmoothOfRelativeDimension g Y.hom] [IsProper Y.hom]
  (φ : CechComplex.Intrinsic.bicomplex R Y V ⟶ CechComplex.Intrinsic.bicomplex R X U)

def rowMap : TopEdge.Intrinsic.source R Y V g →ₗ[R] TopEdge.Intrinsic.source R X U g :=
  (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R X U g).inv g).hom.comp
    ((HomologicalComplex.homologyMap (φ.f g) g).hom.comp
      (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R Y V g).hom g).hom)

theorem naturality (x : TopEdge.Intrinsic.source R Y V g) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map φ (.up ℕ)) (g + g)
      (TopEdge.Intrinsic.map R Y V g x) = TopEdge.Intrinsic.map R X U g (rowMap R X Y U V g φ x) := by
  have h := TopRowEdgeNaturality.naturality (CechComplex.Intrinsic.bicomplex R Y V) (CechComplex.Intrinsic.bicomplex R X U) g
    (TopEdge.Intrinsic.outgoing R Y V g) (TopEdge.Intrinsic.outgoing R X U g) φ g
    (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R Y V g).hom g x)
  have hi (z : ((CechComplex.Intrinsic.bicomplex R X U).X g).homology g) :
      HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R X U g).hom g
        (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R X U g).inv g z) = z :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyMapIso (TopEdge.Intrinsic.rowIso R X U g) g).inv_hom_id z
  change _ = TopRowEdge.map (CechComplex.Intrinsic.bicomplex R X U) g (TopEdge.Intrinsic.outgoing R X U g) g
    (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R X U g).hom g
      (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R X U g).inv g
        (HomologicalComplex.homologyMap (φ.f g) g
          (HomologicalComplex.homologyMap (TopEdge.Intrinsic.rowIso R Y V g).hom g x))))
  rw [hi]
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdgeMap.Intrinsic
