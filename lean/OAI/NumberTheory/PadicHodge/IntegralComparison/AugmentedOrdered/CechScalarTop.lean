import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechLargeTop

/-! # Cech Scalar Top -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechScalarTop.Large

noncomputable section

/-! The literal full-intersection cocycle and its original homology
class retain the scalar coefficient of the numerator. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {R : Type v} [CommRing R] [HasProducts.{u} (ModuleCat.{w} R)]
  (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ)
  (g : ℕ) (hg : Fintype.card ι = g) (q : ℕ)
  (x : (K.X q).obj (op (CechCoordinates.topObject U g hg)))
  (hx : (K.d q (q+1)).app (op (CechCoordinates.topObject U g hg)) x = 0)
  (r : R)
  (hr : (K.d q (q+1)).app (op (CechCoordinates.topObject U g hg)) (r • x) = 0)

theorem topTotalCycle_smul :
    CechLargeTop.topTotalCycle U K g hg q (r • x) hr = r • CechLargeTop.topTotalCycle U K g hg q x hx := by
  apply Subtype.ext
  exact map_smul (CechLargeTop.topTotalInclusion U K g hg q (q+g) rfl).hom r x

theorem topTotalClass_smul :
    CechLargeTop.topTotalClass U K g hg q (r • x) hr = r • CechLargeTop.topTotalClass U K g hg q x hx := by
  dsimp only [CechLargeTop.topTotalClass]
  rw [topTotalCycle_smul, map_smul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechScalarTop.Large
