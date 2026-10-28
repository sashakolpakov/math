import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalChartPurity

/-! # Differential -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.Differential.Constructions

noncomputable section

/-! The actual normal-coordinate map of a differentiable normal pair
is a submersion at every point of its neighborhood. -/

open _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold

set_option backward.isDefEq.respectTransparency false

variable {M N E F G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

local instance : ChartedSpace G P.neighborhood :=
  inferInstanceAs (ChartedSpace G P.openNeighborhood)

theorem normalCoordinate_mfderiv
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F)) (y : P.neighborhood) :
    mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) P.normalCoordinate y =
      (ContinuousLinearMap.snd ℂ E F).comp
        (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, E × F) P.ambientChart y.val) := by
  have hv : MDifferentiableAt 𝓘(ℂ, G) 𝓘(ℂ, G) (Subtype.val : P.openNeighborhood → N) y :=
    (show ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, G) 1 (Subtype.val : P.openNeighborhood → N) from
      contMDiff_subtype_val).mdifferentiableAt one_ne_zero
  have hd := (hP.mdifferentiableAt (P.neighborhood_subset_source y.property)).hasMFDerivAt.comp y
    hv.hasMFDerivAt
  have hs := (ContinuousLinearMap.snd ℂ E F).hasMFDerivAt.comp y hd
  have he := hs.mfderiv
  change mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) P.normalCoordinate y =
    (ContinuousLinearMap.snd ℂ E F).comp
      ((mfderiv 𝓘(ℂ, G) 𝓘(ℂ, E × F) P.ambientChart y.val).comp
        (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, G) (Subtype.val : P.openNeighborhood → N) y)) at he
  rw [Open.InclusionDifferential.Constructions.Manifold.mfderiv_subtypeVal] at he
  exact he.trans (by ext z; rfl)

theorem normalCoordinate_submersion
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F)) (y : P.neighborhood) :
    Function.Surjective (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) P.normalCoordinate y) := by
  rw [normalCoordinate_mfderiv P hP y]
  exact (show Function.Surjective (ContinuousLinearMap.snd ℂ E F) from
    fun z => ⟨(0, z), rfl⟩).comp (hP.mfderiv_bijective (P.neighborhood_subset_source y.property)).2

theorem normalCoordinate_analytic
    (hP : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E × F) ω P.ambientChart P.ambientChart.source) :
    ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, F) ω P.normalCoordinate := by
  intro y
  have hy := P.neighborhood_subset_source y.property
  have hv : ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, G) ω (Subtype.val : P.openNeighborhood → N) :=
    contMDiff_subtype_val
  have hc := ((hP y.val hy).contMDiffAt (P.ambientChart.open_source.mem_nhds hy)).comp y (hv y)
  exact ((ContinuousLinearMap.snd ℂ E F).contDiff (n := ω)).contMDiff.contMDiffAt.comp y hc

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.Differential.Constructions
