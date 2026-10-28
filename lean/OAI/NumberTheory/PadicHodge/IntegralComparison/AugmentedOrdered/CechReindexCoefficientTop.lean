import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoefficientTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTopTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality

/-! # Cech Reindex Coefficient Top -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexCoefficientTop

noncomputable section

/-! Coefficient change followed by reindexing carries the original
full-intersection class to the class of its literal coefficient image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {R : Type v} [CommRing R] [HasProducts.{u} (ModuleCat.{w} R)]
  (L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ)
  (K : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{w} R) ℕ)
  (f : L ⟶ CechReindexTopTotal.pulled r K)

def map : (CechFunctor.bicomplex U L).total (.up ℕ) ⟶ (CechFunctor.bicomplex (r.obj ∘ U) K).total (.up ℕ) :=
  CechForgetNaturality.map U f ≫
    (CechReindexTotal.totalIso r U K).hom

variable (g : ℕ) (hg : Fintype.card ι = g) (q : ℕ)
  (x : (L.X q).obj (op (CechCoordinates.topObject U g hg)))
  (hx : (L.d q (q+1)).app (op (CechCoordinates.topObject U g hg)) x = 0)

def image : (K.X q).obj (op (CechCoordinates.topObject (r.obj ∘ U) g hg)) :=
  CechReindexTop.coefficient r U g hg (K.X q)
    ((f.f q).app (op (CechCoordinates.topObject U g hg)) x)

include hx in
omit [HasProducts (ModuleCat R)] in
theorem image_closed : (K.d q (q+1)).app (op (CechCoordinates.topObject (r.obj ∘ U) g hg))
    (image r U L K f g hg q x) = 0 :=
  CechReindexTopTotal.coefficient_closed r U K g hg q _
    (CechCoefficientTop.mapped_coefficient_closed U f g hg q x hx)

theorem homology :
    HomologicalComplex.homologyMap (map r U L K f) (q+g)
      (CechLargeTop.topTotalClass U L g hg q x hx) =
    CechLargeTop.topTotalClass (r.obj ∘ U) K g hg q (image r U L K f g hg q x)
      (image_closed r U L K f g hg q x hx) := by
  rw [map, HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply]
  change HomologicalComplex.homologyMap
      (CechReindexTotal.totalIso r U K).hom (q+g)
      (HomologicalComplex.homologyMap
        (CechCoefficientTop.totalMap U f) (q+g)
        (CechLargeTop.topTotalClass U L g hg q x hx)) = _
  rw [CechCoefficientTop.topTotalClass_naturality]
  exact CechReindexTopTotal.homology r U K g hg q _ _

theorem homology_of_image_eq
    (y : (K.X q).obj (op (CechCoordinates.topObject (r.obj ∘ U) g hg)))
    (hy : (K.d q (q+1)).app (op (CechCoordinates.topObject (r.obj ∘ U) g hg)) y = 0)
    (hxy : image r U L K f g hg q x = y) :
    HomologicalComplex.homologyMap (map r U L K f) (q+g)
      (CechLargeTop.topTotalClass U L g hg q x hx) = CechLargeTop.topTotalClass (r.obj ∘ U) K g hg q y hy := by
  subst y
  exact homology r U L K f g hg q x hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexCoefficientTop
