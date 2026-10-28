import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultProduct
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothHolomorphicScalar

/-! # Holomorphic Product -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.HolomorphicProduct

noncomputable section

/-! Higher-degree pure manifold Dolbeault forms respect multiplication by the actual holomorphic transition functions. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U : Opens M} {n p q : ℕ}

theorem openManifoldHasBidegree_smoothScalarMul (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    {a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n} (ha : Open.ManifoldBidegree.OpenManifoldHasBidegree p q a) :
    Open.ManifoldBidegree.OpenManifoldHasBidegree p q (SmoothScalarForm.smoothScalarOpenFormMul f a) := by
  intro e he y hy z v
  rw [SmoothScalarForm.smoothScalarOpenFormMul_inChart f a e hy.2]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [ha e he y hy z v]
  ring

theorem holomorphicScalarExtension_chart_differentiableAt
    (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U))
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set M)) :
    DifferentiableAt ℂ (Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) ∘ e.symm) y := by
  have hg := ((Holomorphic.ManifoldCoordinates.holomorphicOpenExtend_chart_contDiff g e he).contDiffAt
    ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds hy)).differentiableAt (by simp)
  apply hg.congr_of_eventuallyEq
  filter_upwards [(Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds hy] with z hz
  change Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) (e.symm z) =
    Holomorphic.OpenExtension.holomorphicOpenExtend g (e.symm z)
  rw [Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) ⟨e.symm z, hz.2⟩,
    Holomorphic.OpenExtension.holomorphicOpenExtend_apply g (e.symm z) hz.2]
  rfl

theorem openManifoldDolbeaultD_holomorphic_mul
    (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (hn : n = p + q) (ha : Open.ManifoldBidegree.OpenManifoldHasBidegree p q a) :
    Open.ManifoldDolbeault.openManifoldDolbeaultD p q n (SmoothScalarForm.smoothScalarOpenFormMul (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) a) =
      SmoothScalarForm.smoothScalarOpenFormMul (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) (Open.ManifoldDolbeault.openManifoldDolbeaultD p q n a) := by
  apply sub_eq_zero.mp
  apply (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.eq_zero_iff_inChartOn U _).mpr
  intro e he
  rw [map_sub]
  apply sub_eq_zero.mpr
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro y
  change (Open.ManifoldDolbeault.openManifoldDolbeaultD p q n
    (SmoothScalarForm.smoothScalarOpenFormMul (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) a)).extension.inChart e y =
      (SmoothScalarForm.smoothScalarOpenFormMul (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g)
        (Open.ManifoldDolbeault.openManifoldDolbeaultD p q n a)).extension.inChart e y
  rw [Open.ManifoldDolbeault.openManifoldDolbeaultD_eq_local hn (openManifoldHasBidegree_smoothScalarMul _ ha) e he y.property,
    SmoothScalarForm.smoothScalarOpenFormMul_inChart _ _ e y.property.2,
    Open.ManifoldDolbeault.openManifoldDolbeaultD_eq_local hn ha e he y.property]
  have hprod : (SmoothScalarForm.smoothScalarOpenFormMul (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) a).extension.inChart e =ᶠ[𝓝 (y : E)]
      (fun z => Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) (e.symm z) • a.extension.inChart e z) := by
    filter_upwards [(Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property] with z hz
    exact SmoothScalarForm.smoothScalarOpenFormMul_inChart _ a e hz.2
  have hg := holomorphicScalarExtension_chart_differentiableAt g e he y.property
  have ha' := ((a.smooth e he).contDiffAt ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property)).differentiableAt (by simp)
  have h := Holomorphic.DolbeaultProduct.extDerivDoublePrime_holomorphic_smul hg ha'
  simp only [Function.comp_apply] at h
  unfold Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime at h ⊢
  rw [hprod.fderiv_eq]
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.HolomorphicProduct
