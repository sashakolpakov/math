import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarOneFormDerivative
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarExterior

/-! # One Form Product -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.OneFormProduct

noncomputable section

/-! The actual scalar-times-one-form product rule on the original ambient manifold opens. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {U : Opens M}

theorem smoothScalarOpenOneForm_d_mul (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenFormMul f a) =
      ManifoldWedge.openManifoldWedge (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f)) a +
        SmoothScalarForm.smoothScalarOpenFormMul f (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a) := by
  apply sub_eq_zero.mp
  apply (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.eq_zero_iff_inChartOn U _).mpr
  intro e he
  rw [map_sub]
  apply sub_eq_zero.mpr
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro y
  change (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenFormMul f a)).extension.inChart e y =
    (ManifoldWedge.openManifoldWedge (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f)) a +
      SmoothScalarForm.smoothScalarOpenFormMul f (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a)).extension.inChart e y
  simp only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Pi.add_apply,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_inChart _ e he y.property,
    ManifoldWedge.openManifoldWedge_inChart _ _ e y.property.2, SmoothScalarForm.smoothScalarOpenFormMul_inChart _ _ e y.property.2]
  have heq : (SmoothScalarForm.smoothScalarOpenFormMul f a).extension.inChart e =ᶠ[𝓝 (y : E)]
      (fun z => Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f (e.symm z) • a.extension.inChart e z) := by
    filter_upwards [(Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property] with z hz
    exact SmoothScalarForm.smoothScalarOpenFormMul_inChart f a e hz.2
  rw [heq.extDeriv_eq]
  have hf := ((SmoothScalarForm.smoothOpenScalarExtension_chart_contDiff f e he).contDiffAt
    ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property)).differentiableAt (by simp)
  have ha := ((a.smooth e he).contDiffAt
    ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property)).differentiableAt (by simp)
  have hz := (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_inChart (SmoothScalarForm.smoothScalarOpenZeroForm f) e he y.property).symm.trans
    (SmoothScalarExterior.smoothScalarOpenZeroForm_d_inChart f e he y.property)
  rw [hz]
  exact ScalarOneFormDerivative.extDeriv_scalar_one (Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f ∘ e.symm) (a.extension.inChart e) y hf ha

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.OneFormProduct
