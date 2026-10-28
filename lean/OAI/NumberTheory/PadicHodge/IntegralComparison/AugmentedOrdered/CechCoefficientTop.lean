import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechLargeTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality

/-! # Cech Coefficient Top -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoefficientTop

noncomputable section

/-! Maps of the actual coefficient complexes preserve the
full-intersection residue cycles and their native total homology classes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechLargeTop
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {R : Type v} [CommRing R] [HasProducts.{u} (ModuleCat.{w} R)]
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} (f : K ⟶ L)

def bicomplexMap : CechFunctor.bicomplex U K ⟶ CechFunctor.bicomplex U L :=
  ((CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map f

def totalMap : (CechFunctor.bicomplex U K).total (.up ℕ) ⟶ (CechFunctor.bicomplex U L).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap U f) (.up ℕ)

theorem topTotalInclusion_naturality (g : ℕ) (hg : Fintype.card ι = g)
    (q N : ℕ) (hN : q + g = N) :
    CechLargeTop.topTotalInclusion U K g hg q N hN ≫ (totalMap U f).f N =
      (f.f q).app (op (CechCoordinates.topObject U g hg)) ≫ CechLargeTop.topTotalInclusion U L g hg q N hN := by
  rw [CechLargeTop.topTotalInclusion, Category.assoc, totalMap, HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc]
  change (CechCoordinates.topInclusion U (K.X q) g hg ≫ CechFunctor.objectMap U (f.f q) g) ≫ _ = _
  rw [CechCoordinates.topInclusion_naturality]
  rfl

omit [HasProducts (ModuleCat R)] in
theorem mapped_coefficient_closed (g : ℕ) (hg : Fintype.card ι = g)
    (q : ℕ) (x : (K.X q).obj (op (CechCoordinates.topObject U g hg)))
    (hx : (K.d q (q + 1)).app (op (CechCoordinates.topObject U g hg)) x = 0) :
    (L.d q (q + 1)).app (op (CechCoordinates.topObject U g hg))
      ((f.f q).app (op (CechCoordinates.topObject U g hg)) x) = 0 := by
  have h := congrArg (fun e => (e.app (op (CechCoordinates.topObject U g hg))) x) (f.comm q (q + 1))
  change (L.d q (q + 1)).app _ ((f.f q).app _ x) =
    (f.f (q + 1)).app _ ((K.d q (q + 1)).app _ x) at h
  exact h.trans (by rw [hx, map_zero])

theorem topTotalCycle_naturality (g : ℕ) (hg : Fintype.card ι = g)
    (q : ℕ) (x : (K.X q).obj (op (CechCoordinates.topObject U g hg)))
    (hx : (K.d q (q + 1)).app (op (CechCoordinates.topObject U g hg)) x = 0) :
    Module.CochainClassNaturality.cycleMap (totalMap U f) (q + g)
        (CechLargeTop.topTotalCycle U K g hg q x hx) =
      CechLargeTop.topTotalCycle U L g hg q ((f.f q).app (op (CechCoordinates.topObject U g hg)) x)
        (mapped_coefficient_closed U f g hg q x hx) := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (topTotalInclusion_naturality U f g hg q (q + g) rfl) x

theorem topTotalClass_naturality (g : ℕ) (hg : Fintype.card ι = g)
    (q : ℕ) (x : (K.X q).obj (op (CechCoordinates.topObject U g hg)))
    (hx : (K.d q (q + 1)).app (op (CechCoordinates.topObject U g hg)) x = 0) :
    HomologicalComplex.homologyMap (totalMap U f) (q + g)
        (CechLargeTop.topTotalClass U K g hg q x hx) =
      CechLargeTop.topTotalClass U L g hg q ((f.f q).app (op (CechCoordinates.topObject U g hg)) x)
        (mapped_coefficient_closed U f g hg q x hx) := by
  have h := Module.CochainClassNaturality.naturality_apply (totalMap U f) (q + g)
    (CechLargeTop.topTotalCycle U K g hg q x hx)
  rw [topTotalCycle_naturality] at h
  exact h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoefficientTop
