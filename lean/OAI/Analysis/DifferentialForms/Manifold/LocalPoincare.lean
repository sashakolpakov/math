import OAI.Analysis.DifferentialForms.Manifold.ChartEquiv
import OAI.AlgebraicTopology.DeRham.Comparison.LocalPoincare

/-! # Local Poincare -/

namespace OAI.Analysis.DifferentialForms.Manifold.LocalPoincare

noncomputable section

/-!
# Local primitives of actual smooth manifold forms

The proved Euclidean local Poincare theorem is transported through an actual
atlas chart. All domains, restrictions and coordinate changes are those of the
previously constructed smooth tangent-covector sections.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

/-- Every closed positive-degree smooth manifold form has a primitive near each point. -/
theorem manifold_local_poincare (U : Opens M)
    (form : Open.SmoothOpenManifoldForm E U (n + 1))
    (hclosed : Open.SmoothOpenManifoldForm.d form = 0) (x : U) :
    ∃ (W : Opens M) (hWU : W ≤ U), (x : M) ∈ W ∧
      ∃ primitive : Open.SmoothOpenManifoldForm E W n,
        Open.SmoothOpenManifoldForm.d primitive = Open.SmoothOpenManifoldForm.restrict hWU form := by
  let e := chartAt E (x : M)
  have he : e ∈ atlas E M := chart_mem_atlas E (x : M)
  let V := ChartEquiv.chartImageOpen e U
  have hV : V ≤ ChartEquiv.chartTargetOpen e := ChartEquiv.chartImageOpen_le_target e U
  have hpre : ChartEquiv.chartPreimageOpen e V ≤ U := ChartEquiv.chartPreimage_image_le e U
  let formLocal := Open.SmoothOpenManifoldForm.restrict hpre form
  let coord := ChartEquiv.manifoldChartOpenFormEquiv e he V hV (n + 1) formLocal
  have hlocalClosed : Open.SmoothOpenManifoldForm.d formLocal = 0 := by
    dsimp only [formLocal]
    rw [← Open.SmoothOpenManifoldForm.restrict_d, hclosed, map_zero]
  have hcoordClosed : OpenD.SmoothOpenForm.d coord = 0 := by
    dsimp only [coord]
    rw [ChartEquiv.manifoldChartOpenFormEquiv_d, hlocalClosed, map_zero]
  have hxV : e (x : M) ∈ V :=
    ChartEquiv.mem_chartImageOpen e U (mem_chart_source E (x : M)) x.property
  obtain ⟨W, hWV, hxW, primitive, hprimitive⟩ :=
    AlgebraicTopology.DeRham.Comparison.LocalPoincare.local_poincare V coord hcoordClosed ⟨e (x : M), hxV⟩
  let localW := ChartEquiv.chartPreimageOpen e W
  let hWU : localW ≤ U := (ChartEquiv.chartPreimageOpen_mono e hWV).trans hpre
  refine ⟨localW, hWU, ⟨mem_chart_source E (x : M), hxW⟩,
    (ChartEquiv.manifoldChartOpenFormEquiv e he W (hWV.trans hV) n).symm primitive, ?_⟩
  apply (ChartEquiv.manifoldChartOpenFormEquiv e he W (hWV.trans hV) (n + 1)).injective
  calc
    ChartEquiv.manifoldChartOpenFormEquiv e he W (hWV.trans hV) (n + 1)
        (Open.SmoothOpenManifoldForm.d
          ((ChartEquiv.manifoldChartOpenFormEquiv e he W (hWV.trans hV) n).symm primitive)) =
        OpenD.SmoothOpenForm.d primitive := by
      simpa only [LinearEquiv.apply_symm_apply] using
        (ChartEquiv.manifoldChartOpenFormEquiv_d e he W (hWV.trans hV)
          ((ChartEquiv.manifoldChartOpenFormEquiv e he W (hWV.trans hV) n).symm primitive)).symm
    _ = OpenD.SmoothOpenForm.restrict hWV coord := hprimitive
    _ = ChartEquiv.manifoldChartOpenFormEquiv e he W (hWV.trans hV) (n + 1)
        (Open.SmoothOpenManifoldForm.restrict (ChartEquiv.chartPreimageOpen_mono e hWV) formLocal) :=
      (Open.SmoothOpenManifoldForm.toChartOn_restrict e he hV hWV formLocal).symm
    _ = ChartEquiv.manifoldChartOpenFormEquiv e he W (hWV.trans hV) (n + 1)
        (Open.SmoothOpenManifoldForm.restrict hWU form) := by
      congr 1

end

end OAI.Analysis.DifferentialForms.Manifold.LocalPoincare
