import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldDolbeault
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.DolbeaultSquared

/-! # Dolbeault Charts -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts

noncomputable section

/-! Chart transport and square-zero for the actual manifold Dolbeault operator. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {n p q : ℕ} {U V : Opens M}

theorem openManifoldDolbeaultD_toChartOn
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (W : Opens E) (hW : W ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e)
    {form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e W) n}
    (hn : n = p + q) (hf : Open.ManifoldBidegree.OpenManifoldHasBidegree p q form) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he W hW (Open.ManifoldDolbeault.openManifoldDolbeaultD p q n form) =
      DolbeaultOpen.openDolbeaultD n (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he W hW form) := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro y
  change (Open.ManifoldDolbeault.openManifoldDolbeaultD p q n form).extension.inChart e y =
    Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he W hW form).extension y
  rw [Open.ManifoldDolbeault.openManifoldDolbeaultD_eq_local hn hf e he
    ⟨hW y.property, Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartPreimageOpen_symm e W hW y.property⟩]
  have heq : (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he W hW form).extension =ᶠ[𝓝 (y : E)]
      form.extension.inChart e := by
    filter_upwards [W.isOpen.mem_nhds y.property] with t ht
    exact Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_apply _ ⟨t, ht⟩
  unfold Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime
  rw [heq.fderiv_eq]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem openManifold_ext_on_chart_preimages
    {a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n}
    (h : ∀ e ∈ atlas E M,
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimage_image_le e U) a =
        Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimage_image_le e U) b) : a = b := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  let e := chartAt E (x : M)
  have hx : (x : M) ∈ Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) :=
    ⟨mem_chart_source E (x : M), Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e U (mem_chart_source E (x : M)) x.property⟩
  exact congrArg (fun c : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U)) n =>
    c ⟨x, hx⟩) (h e (chart_mem_atlas E (x : M)))

theorem openManifoldDolbeaultD_squared {form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n}
    (hn : n = p + q) (hf : Open.ManifoldBidegree.OpenManifoldHasBidegree p q form) :
    Open.ManifoldDolbeault.openManifoldDolbeaultD p (q + 1) (n + 1) (Open.ManifoldDolbeault.openManifoldDolbeaultD p q n form) = 0 := by
  apply openManifold_ext_on_chart_preimages
  intro e he
  let W := Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U
  have hW : W ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e := Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen_le_target e U
  have hU := Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimage_image_le e U
  rw [Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict, Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict, map_zero]
  apply (Analysis.DifferentialForms.Manifold.ChartEquiv.manifoldChartOpenFormEquiv e he W hW (n + 1 + 1)).injective
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he W hW
    (Open.ManifoldDolbeault.openManifoldDolbeaultD p (q + 1) (n + 1)
      (Open.ManifoldDolbeault.openManifoldDolbeaultD p q n (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hU form))) =
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he W hW 0
  have hrest := Open.ManifoldBidegree.openManifoldHasBidegree_restrict hU hf
  rw [openManifoldDolbeaultD_toChartOn e he W hW (by omega)
    (Open.ManifoldDolbeault.openManifoldDolbeaultD_hasBidegree hn hrest),
    openManifoldDolbeaultD_toChartOn e he W hW hn hrest, map_zero]
  exact Open.DolbeaultSquared.openDolbeaultD_squared_of_bidegree _ hn
    (Open.ManifoldBidegree.openManifoldHasBidegree_toChartOn e he W hW hrest)

def pureOpenManifoldDolbeaultD (U : Opens M) (q : ℕ) :
    Open.ManifoldBidegree.AntiOpenManifoldForm E U q →ₗ[ℂ] Open.ManifoldBidegree.AntiOpenManifoldForm E U (q + 1) where
  toFun form := ⟨Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q form.1,
    Open.ManifoldDolbeault.openManifoldDolbeaultD_hasBidegree (by omega) form.2⟩
  map_add' f g := Subtype.ext ((Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q).map_add f.1 g.1)
  map_smul' c f := Subtype.ext ((Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q).map_smul c f.1)

theorem pureOpenManifoldDolbeaultD_restrict (h : V ≤ U) (form : Open.ManifoldBidegree.AntiOpenManifoldForm E U q) :
    Open.ManifoldBidegree.antiOpenManifoldFormRestrict h (pureOpenManifoldDolbeaultD U q form) =
      pureOpenManifoldDolbeaultD V q (Open.ManifoldBidegree.antiOpenManifoldFormRestrict h form) :=
  Subtype.ext (Open.ManifoldDolbeault.openManifoldDolbeaultD_restrict h form.1)

theorem pureOpenManifoldDolbeaultD_squared (U : Opens M) (q : ℕ)
    (form : Open.ManifoldBidegree.AntiOpenManifoldForm E U q) :
    pureOpenManifoldDolbeaultD U (q + 1) (pureOpenManifoldDolbeaultD U q form) = 0 :=
  Subtype.ext (openManifoldDolbeaultD_squared (by omega) form.2)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts
