import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoefficientTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechScalarTop

/-! # Weighted Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.WeightedIso

noncomputable section

/-! An isomorphism carrying the literal weighted top coefficient to a
fraction carries its supported class back to the same weighted residue. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechScalarTop.Large

universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {R : Type v} [CommRing R] [HasProducts.{u} (ModuleCat.{w} R)]
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ}
  (e : K ≅ L) (g : ℕ) (hg : Fintype.card ι = g) (q : ℕ)
  (x : (K.X q).obj (op (AugmentedOrdered.CechCoordinates.topObject U g hg)))
  (hx : (K.d q (q + 1)).app (op (AugmentedOrdered.CechCoordinates.topObject U g hg)) x = 0)
  (r : R) (y : (L.X q).obj (op (AugmentedOrdered.CechCoordinates.topObject U g hg)))
  (hy : (L.d q (q + 1)).app (op (AugmentedOrdered.CechCoordinates.topObject U g hg)) y = 0)
  (hxy : (e.hom.f q).app (op (AugmentedOrdered.CechCoordinates.topObject U g hg)) (r • x) = y)

include hxy in
omit [HasProducts (ModuleCat R)] in
theorem inverse_coefficient :
    (e.inv.f q).app (op (AugmentedOrdered.CechCoordinates.topObject U g hg)) y = r • x := by
  rw [← hxy]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun a => a.f q) e.hom_inv_id)
      (op (AugmentedOrdered.CechCoordinates.topObject U g hg))) (r • x)

include hxy in
theorem inverse_class :
    HomologicalComplex.homologyMap
        (AugmentedOrdered.CechCoefficientTop.totalMap U e.inv) (q + g)
        (AugmentedOrdered.CechLargeTop.topTotalClass U L g hg q y hy) =
      r • AugmentedOrdered.CechLargeTop.topTotalClass U K g hg q x hx := by
  have h := AugmentedOrdered.CechCoefficientTop.topTotalClass_naturality
    U e.inv g hg q y hy
  have hv := inverse_coefficient U e g hg q x r y hxy
  have hr : (K.d q (q + 1)).app (op (AugmentedOrdered.CechCoordinates.topObject U g hg)) (r • x) = 0 := by
    rw [map_smul, hx, smul_zero]
  refine h.trans ?_
  simpa only [hv] using AugmentedOrdered.CechScalarTop.Large.topTotalClass_smul U K g hg q x hx r hr

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.WeightedIso
