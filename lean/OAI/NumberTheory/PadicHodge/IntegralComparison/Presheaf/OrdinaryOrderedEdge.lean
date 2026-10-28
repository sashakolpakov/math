import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.TopCone
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjection
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge

/-! # Ordinary Ordered Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrdinaryOrderedEdge.Ordinary

noncomputable section

/-! The literal global-section edge into the ordinary Čech total
projects to the global-section edge into the ordered Čech total. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v
variable {X : TopCat.{0}} {ι : Type} [LinearOrder ι] (V : ι → Opens X)
  {D : Type v} [Category D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ)

def ordinary : OrderedCechEdge.sections K ⟶ (OrderedCech.TotalProjection.ordinary V).obj K :=
  GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map V K (OrderedCechEdge.sections K) (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) K)

omit [HasCoproducts D] in
theorem component (q : ℕ) :
    GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.component V K (OrderedCechEdge.sections K)
        (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) K) q ≫
      (OrderedCech.Projection.map V (K.X q)).f 0 = OrderedCechEdge.augmentation V (K.X q) := by
  apply Pi.hom_ext
  intro (a : OrderedCech.Projection.Index (ι := ι) 0)
  change (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.component V K (OrderedCechEdge.sections K)
      (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) K) q ≫
      OrderedCech.Projection.mapF V (K.X q) 0) ≫
        OrderedCech.Projection.projection V (K.X q) 0 a =
    OrderedCechEdge.augmentation V (K.X q) ≫ OrderedCech.Projection.projection V (K.X q) 0 a
  rw [Category.assoc, OrderedCech.Projection.mapF_projection]
  change Pi.lift (fun t : Fin 1 → ι =>
    (K.X q).map (homOfLE (le_top : (∏ᶜ (V ∘ t)) ≤ ⊤)).op) ≫
      Pi.π (fun t : Fin 1 → ι => (K.X q).obj (op (∏ᶜ (V ∘ t)))) a.val = _
  rw [Pi.lift_comp_π]
  exact (OrderedCechEdge.augmentation_projection V (K.X q) a).symm

theorem comparison :
    ordinary V K ≫ OrderedCech.TotalProjection.map V K = OrderedCechEdge.edge V K := by
  have h := BicomplexHorizontalEdge.naturality
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V K) (OrderedCechEdge.sections K)
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.component V K (OrderedCechEdge.sections K) (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) K))
    (fun q q' _ => GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.comm V K (OrderedCechEdge.sections K)
      (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) K) q q')
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.cocycle V K (OrderedCechEdge.sections K) (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) K))
    (OrderedCechEdge.bicomplex V K) (OrderedCechEdge.sections K)
    (fun q => OrderedCechEdge.augmentation V (K.X q))
    (fun q q' _ => OrderedCechEdge.augmentation_comm V K q q') (OrderedCechEdge.augmentation_cocycle V K)
    (OrderedCech.TotalProjection.bicomplexMap V K) (𝟙 _) (fun q => by
      change GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.component V K (OrderedCechEdge.sections K)
          (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) K) q ≫
        (OrderedCech.Projection.map V (K.X q)).f 0 = 𝟙 _ ≫ OrderedCechEdge.augmentation V (K.X q)
      rw [Category.id_comp]
      exact component V K q)
  simpa only [ordinary, GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map, OrderedCech.TotalProjection.map,
    OrderedCechEdge.edge, Category.id_comp] using h

theorem homology (q : ℕ) :
    homologyMap (ordinary V K) q ≫ homologyMap (OrderedCech.TotalProjection.map V K) q =
      homologyMap (OrderedCechEdge.edge V K) q := by
  rw [← homologyMap_comp, comparison]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrdinaryOrderedEdge.Ordinary
