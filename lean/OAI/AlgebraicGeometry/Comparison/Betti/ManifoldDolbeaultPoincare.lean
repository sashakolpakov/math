import OAI.AlgebraicGeometry.Comparison.Betti.LocalDolbeaultPoincare
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts

/-! # Manifold Dolbeault Poincare -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ManifoldDolbeaultPoincare

noncomputable section

/-! Genuine local Dolbeault primitives of every positive antiholomorphic
bidegree on finite-dimensional complex manifolds, with the original operator. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem manifoldLocalDolbeaultPoincare (U : Opens M) (n p q : ℕ) (hn : n = p + q)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1))
    (ha : DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD p (q + 1) (n + 1) a = 0)
    (hpure : DivisorClass.Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree p (q + 1) a) (x : U) :
    ∃ V : Opens M, x.val ∈ V ∧ ∃ hV : V ≤ U,
      ∃ t : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V n, DivisorClass.Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree p q t ∧
        DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD p q n t = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a := by
  let e := chartAt E (x : M)
  have he : e ∈ atlas E M := chart_mem_atlas E (x : M)
  let W := Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U
  have hW : W ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e := Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen_le_target e U
  have hU := Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimage_image_le e U
  let b := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hU a
  have hb : DivisorClass.Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree p (q + 1) b := DivisorClass.Chern.Open.ManifoldBidegree.openManifoldHasBidegree_restrict hU hpure
  let A := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he W hW b
  have hA : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) A := DivisorClass.Chern.Open.ManifoldBidegree.openManifoldHasBidegree_toChartOn e he W hW hb
  have hclosed : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) A = 0 := by
    rw [← DivisorClass.Chern.Manifold.DolbeaultCharts.openManifoldDolbeaultD_toChartOn e he W hW (by omega) hb]
    have hd : DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD p (q + 1) (n + 1) b = 0 := by
      rw [← DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict hU a, ha, map_zero]
    rw [hd, map_zero]
  let y : W := ⟨e x, Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e U (mem_chart_source E (x : M)) x.property⟩
  obtain ⟨Z, hyZ, hZ, t, htp, ht⟩ := LocalDolbeaultPoincare.localDolbeaultPoincare W n p q hn A hclosed hA y
  let V := Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e Z
  have hV : V ≤ U := (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen_mono e hZ).trans hU
  let T := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.fromChartOn e he Z t
  have hT : DivisorClass.Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree p q T :=
    DivisorClass.Chern.Open.ManifoldBidegree.openManifoldHasBidegree_fromChartOn e he Z (hZ.trans hW) hn htp
  refine ⟨V, ⟨mem_chart_source E (x : M), hyZ⟩, hV, T, hT, ?_⟩
  apply (Analysis.DifferentialForms.Manifold.ChartEquiv.manifoldChartOpenFormEquiv e he Z (hZ.trans hW) (n + 1)).injective
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he Z (hZ.trans hW)
    (DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD p q n T) = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he Z (hZ.trans hW)
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a)
  rw [DivisorClass.Chern.Manifold.DolbeaultCharts.openManifoldDolbeaultD_toChartOn e he Z (hZ.trans hW) hn hT,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn_fromChartOn, ht]
  have hrest : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen_mono e hZ) b :=
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_trans hU (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen_mono e hZ) a).symm
  rw [hrest, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn_restrict]

end

end OAI.AlgebraicGeometry.Comparison.Betti.ManifoldDolbeaultPoincare
