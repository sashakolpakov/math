import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Slice
import OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticCoordinateSlice

/-! # Slice Analytic -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic.Constructions

noncomputable section

/-! The actual normal slice is holomorphic whenever the immersion coordinates have holomorphic inverse. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Slice.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  {c : ℕ} {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)

def normalSliceAmbientMap : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) ⟶ TopCat.of N :=
  SliceDetection.Constructions.normalSliceMap P ≫ Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood

omit [NormedSpace ℂ E] in
theorem normalSliceAmbientMap_apply (u : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) :
    normalSliceAmbientMap P u = P.ambientChart.symm (0, u.val) := rfl

theorem normalSliceAmbient_analytic
    (hP : ContMDiffOn 𝓘(ℂ, E × (Fin c → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target) :
    ContMDiff 𝓘(ℂ, Fin c → ℂ) 𝓘(ℂ, G) ω (normalSliceAmbientMap P) := by
  have he : (normalSliceAmbientMap P : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P → N) =
      fun u => P.ambientChart.symm ((0 : E), u.val) := funext (normalSliceAmbientMap_apply P)
  rw [he]
  exact AnalyticCoordinateSlice.Constructions.inverse_chart_slice P.ambientChart (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) hP
    (fun u => P.product_subset_target ⟨Metric.mem_ball_self P.radius_pos, u.property⟩)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic.Constructions
