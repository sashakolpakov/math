import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechLargeTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality

/-! # Cech Reindex Top Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTopTotal

noncomputable section

/-! The actual full-intersection residue cycle and its total
cohomology class are natural under principal-index reindexing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechLargeTop
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {R : Type v} [CommRing R] [HasProducts.{u} (ModuleCat.{w} R)]
  (K : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{w} R) ℕ)

abbrev pulled := ((CechReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K

variable (g : ℕ) (hg : Fintype.card ι = g)

theorem inclusion (q N : ℕ) (hN : q + g = N) :
    CechLargeTop.topTotalInclusion U (pulled r K) g hg q N hN ≫
      (CechReindexTotal.totalIso r U K).hom.f N =
    CechReindexTop.coefficient r U g hg (K.X q) ≫
      CechLargeTop.topTotalInclusion (r.obj ∘ U) K g hg q N hN := by
  simp only [CechLargeTop.topTotalInclusion]
  erw [Category.assoc, CechReindexTotal.totalIso,
    HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  change (CechCoordinates.topInclusion U (r.op ⋙ K.X q) g hg ≫ (CechReindex.componentIso r U (K.X q) g).hom) ≫ _ = _
  rw [CechReindexTop.inclusion, Category.assoc]

variable (q : ℕ) (x : ((pulled r K).X q).obj (op (CechCoordinates.topObject U g hg)))
  (hx : ((pulled r K).d q (q+1)).app (op (CechCoordinates.topObject U g hg)) x = 0)

include hx in
omit [HasProducts (ModuleCat R)] in
theorem coefficient_closed :
    (K.d q (q+1)).app (op (CechCoordinates.topObject (r.obj ∘ U) g hg))
      (CechReindexTop.coefficient r U g hg (K.X q) x) = 0 := by
  have h := ConcreteCategory.congr_hom
    ((K.d q (q+1)).naturality (CechReindexTop.objectIso r U g hg).inv.op) x
  change (K.d q (q+1)).app (op (CechCoordinates.topObject (r.obj ∘ U) g hg))
      (CechReindexTop.coefficient r U g hg (K.X q) x) =
    CechReindexTop.coefficient r U g hg (K.X (q+1))
      (((pulled r K).d q (q+1)).app (op (CechCoordinates.topObject U g hg)) x) at h
  rw [hx, map_zero] at h
  exact h

theorem cycle :
    Module.CochainClassNaturality.cycleMap
      (CechReindexTotal.totalIso r U K).hom (q+g)
      (CechLargeTop.topTotalCycle U (pulled r K) g hg q x hx) =
    CechLargeTop.topTotalCycle (r.obj ∘ U) K g hg q
      (CechReindexTop.coefficient r U g hg (K.X q) x)
      (coefficient_closed r U K g hg q x hx) := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (inclusion r U K g hg q (q+g) rfl) x

theorem homology :
    HomologicalComplex.homologyMap
      (CechReindexTotal.totalIso r U K).hom (q+g)
      (CechLargeTop.topTotalClass U (pulled r K) g hg q x hx) =
    CechLargeTop.topTotalClass (r.obj ∘ U) K g hg q
      (CechReindexTop.coefficient r U g hg (K.X q) x)
      (coefficient_closed r U K g hg q x hx) := by
  have h := Module.CochainClassNaturality.naturality_apply
    (CechReindexTotal.totalIso r U K).hom (q+g)
    (CechLargeTop.topTotalCycle U (pulled r K) g hg q x hx)
  rw [cycle] at h
  exact h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTopTotal
