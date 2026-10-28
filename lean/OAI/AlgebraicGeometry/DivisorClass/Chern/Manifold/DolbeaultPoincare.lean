import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts
import OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare

/-! # Dolbeault Poincare -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultPoincare

noncomputable section

/-! Constructed local Dolbeault primitives on actual finite-dimensional complex manifolds. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem manifoldLocalDolbeaultPoincare_one (U : Opens M)
    (a : Open.ManifoldBidegree.AntiOpenManifoldForm E U 1) (ha : DolbeaultCharts.pureOpenManifoldDolbeaultD U 1 a = 0) (x : U) :
    ∃ V : Opens M, x.val ∈ V ∧ ∃ hV : V ≤ U,
      ∃ t : Open.ManifoldBidegree.AntiOpenManifoldForm E V 0,
        DolbeaultCharts.pureOpenManifoldDolbeaultD V 0 t = Open.ManifoldBidegree.antiOpenManifoldFormRestrict hV a := by
  let e := chartAt E (x : M)
  have he : e ∈ atlas E M := chart_mem_atlas E (x : M)
  let W := Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U
  have hW : W ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e := Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen_le_target e U
  have hU := Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimage_image_le e U
  let b := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hU a.1
  have hb : Open.ManifoldBidegree.OpenManifoldHasBidegree 0 1 b := Open.ManifoldBidegree.openManifoldHasBidegree_restrict hU a.2
  let A := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he W hW b
  have hA : Open.DolbeaultPrime.OpenFormHasBidegree 0 1 A := Open.ManifoldBidegree.openManifoldHasBidegree_toChartOn e he W hW hb
  have hclosed : DolbeaultOpen.openDolbeaultD 1 A = 0 := by
    rw [← DolbeaultCharts.openManifoldDolbeaultD_toChartOn e he W hW (by omega) hb]
    have hd : Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 b = 0 := by
      rw [← Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict hU a.1]
      have hzero : Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 a.1 = 0 := congrArg Subtype.val ha
      rw [hzero, map_zero]
    rw [hd, map_zero]
  let y : W := ⟨e x, Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e U (mem_chart_source E (x : M)) x.property⟩
  obtain ⟨Z, hyZ, hZ, t, ht⟩ := CoordinatePolydiscDolbeaultPoincare.localDolbeaultPoincare_one W A hclosed hA y
  let V := Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e Z
  have hV : V ≤ U := (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen_mono e hZ).trans hU
  let T := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.fromChartOn e he Z t
  have hT : Open.ManifoldBidegree.OpenManifoldHasBidegree 0 0 T :=
    Open.ManifoldBidegree.openManifoldHasBidegree_fromChartOn e he Z (hZ.trans hW) rfl
      (fun z => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E (t z))
  refine ⟨V, ⟨mem_chart_source E (x : M), hyZ⟩, hV, ⟨T, hT⟩, ?_⟩
  apply Subtype.ext
  change Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 T = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a.1
  apply (Analysis.DifferentialForms.Manifold.ChartEquiv.manifoldChartOpenFormEquiv e he Z (hZ.trans hW) 1).injective
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he Z (hZ.trans hW)
    (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 T) = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he Z (hZ.trans hW)
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a.1)
  rw [DolbeaultCharts.openManifoldDolbeaultD_toChartOn e he Z (hZ.trans hW) rfl hT,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn_fromChartOn, ht]
  have hrest : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a.1 =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen_mono e hZ) b :=
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_trans hU (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen_mono e hZ) a.1).symm
  rw [hrest, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn_restrict]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultPoincare
