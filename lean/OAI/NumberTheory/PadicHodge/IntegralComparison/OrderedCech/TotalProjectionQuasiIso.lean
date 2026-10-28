import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjection

/-! # Total Projection Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjectionQuasiIso

noncomputable section

/-! The actual ordinary-to-ordered projection is a quasi-isomorphism
on the total of every nonnegative complex of module presheaves. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {R : Type v} [Ring R]
  (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u w} R) ℕ)

theorem quasiIso : QuasiIso (TotalProjection.map U K) := by
  apply AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex.total_map_quasiIso_of_columns
  intro q
  exact Refinement.projection_quasiIso U (K.X q)

def homologyIso (q : ℕ) : ((TotalProjection.ordinary U).obj K).homology q ≅ ((TotalProjection.ordered U).obj K).homology q := by
  letI := quasiIso U K
  exact asIso (homologyMap (TotalProjection.map U K) q)

theorem homology_injective (q : ℕ) : Function.Injective (homologyMap (TotalProjection.map U K) q) :=
  (homologyIso U K q).toLinearEquiv.injective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjectionQuasiIso
