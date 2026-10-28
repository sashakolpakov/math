import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothHolomorphicScalar
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Smooth Scalar Dolbeault Product -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarDolbeaultProduct

noncomputable section

/-! The genuine degree-zero Dolbeault operator obeys the product rule and commutes with holomorphic scalar transition functions. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] OAI.Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U : Opens M}

theorem smoothScalarOpenZeroForm_dbar_inChart (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ OAI.Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set M)) :
    (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (SmoothScalarForm.smoothScalarOpenZeroForm f)).extension.inChart e y =
      ofSubsingleton ℝ E ℂ (0 : Fin 1)
        (OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (fderiv ℝ (OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f ∘ e.symm) y)) := by
  rw [Open.ManifoldDolbeault.openManifoldDolbeaultD_eq_local rfl (fun _ _ _ _ => OAI.Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E _) e he hy]
  have heq : (SmoothScalarForm.smoothScalarOpenZeroForm f).extension.inChart e =ᶠ[𝓝 y]
      (fun z => constOfIsEmpty ℝ E (Fin 0) (OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f (e.symm z))) := by
    filter_upwards [(OAI.Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds hy] with z hz
    exact SmoothScalarForm.smoothScalarOpenZeroForm_inChart f e hz.2
  unfold OAI.Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime
  rw [heq.fderiv_eq]
  exact DolbeaultZeroForms.extDerivDoublePrime_constOfIsEmpty (OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f ∘ e.symm) y

theorem smoothScalarOpenZeroForm_dbar_mul (f g : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothScalarForm.smoothComplexOpenFunctionMul f g)) =
      SmoothScalarForm.smoothScalarOpenFormMul f (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (SmoothScalarForm.smoothScalarOpenZeroForm g)) +
        SmoothScalarForm.smoothScalarOpenFormMul g (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (SmoothScalarForm.smoothScalarOpenZeroForm f)) := by
  apply sub_eq_zero.mp
  apply (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.eq_zero_iff_inChartOn U _).mpr
  intro e he
  rw [map_sub]
  apply sub_eq_zero.mpr
  apply OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro y
  change (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothScalarForm.smoothComplexOpenFunctionMul f g))).extension.inChart e y =
    (SmoothScalarForm.smoothScalarOpenFormMul f (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (SmoothScalarForm.smoothScalarOpenZeroForm g)) +
      SmoothScalarForm.smoothScalarOpenFormMul g (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (SmoothScalarForm.smoothScalarOpenZeroForm f))).extension.inChart e y
  simp only [OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Pi.add_apply,
    SmoothScalarForm.smoothScalarOpenFormMul_inChart _ _ e y.property.2,
    smoothScalarOpenZeroForm_dbar_inChart _ e he y.property]
  have hf := ((SmoothScalarForm.smoothOpenScalarExtension_chart_contDiff f e he).contDiffAt
    ((OAI.Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property)).differentiableAt (by simp)
  have hg := ((SmoothScalarForm.smoothOpenScalarExtension_chart_contDiff g e he).contDiffAt
    ((OAI.Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property)).differentiableAt (by simp)
  have hprod : (OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U (SmoothScalarForm.smoothComplexOpenFunctionMul f g) ∘ e.symm) =ᶠ[𝓝 (y : E)]
      (fun z => OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f (e.symm z) * OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U g (e.symm z)) := by
    filter_upwards [(OAI.Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property] with z hz
    change OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U (SmoothScalarForm.smoothComplexOpenFunctionMul f g) (e.symm z) = _
    rw [OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U _ ⟨e.symm z, hz.2⟩,
      OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U f ⟨e.symm z, hz.2⟩,
      OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U g ⟨e.symm z, hz.2⟩]
    rfl
  have hder := fderiv_fun_mul hf hg
  simp only [Function.comp_apply] at hder
  rw [hprod.fderiv_eq, hder, map_add, map_smul, map_smul]
  ext v
  rfl

theorem smoothHolomorphicScalar_dbar_mul (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U))
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0
      (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothScalarForm.smoothComplexOpenFunctionMul (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) f)) =
        SmoothScalarForm.smoothScalarOpenFormMul (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g)
          (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (SmoothScalarForm.smoothScalarOpenZeroForm f)) := by
  rw [smoothScalarOpenZeroForm_dbar_mul, SmoothHolomorphicScalar.smoothHolomorphicScalar_dbar_zero, _root_.map_zero, add_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarDolbeaultProduct
