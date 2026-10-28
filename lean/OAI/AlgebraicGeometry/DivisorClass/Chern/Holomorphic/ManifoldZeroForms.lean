import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ManifoldCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts

/-! # Manifold Zero Forms -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ManifoldZeroForms

noncomputable section

/-! Original holomorphic functions give their actual nullary manifold covectors. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U V : Opens M}

theorem holomorphicManifoldZeroForm_smooth (g : Exponential.HolomorphicFunction (E := E) (M := U)) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar (E := E) (OpenExtension.holomorphicOpenExtend g)) (U : Set M) := by
  intro e he
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar_inChart]
  exact (constOfIsEmptyLIE ℝ E ℂ (Fin 0)).contDiff.comp_contDiffOn
    ((ManifoldCoordinates.holomorphicOpenExtend_chart_contDiff g e he).restrict_scalars ℝ)

def holomorphicManifoldZeroForm (g : Exponential.HolomorphicFunction (E := E) (M := U)) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ofRaw U (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar (OpenExtension.holomorphicOpenExtend g))
    (holomorphicManifoldZeroForm_smooth g)

theorem holomorphicManifoldZeroForm_apply (g : Exponential.HolomorphicFunction (E := E) (M := U))
    (x : U) (v : Fin 0 → TangentSpace 𝓘(ℝ, E) (x : M)) :
    holomorphicManifoldZeroForm g x v = g x := OpenExtension.holomorphicOpenExtend_apply g x x.property

theorem holomorphicManifoldZeroForm_inChart (g : Exponential.HolomorphicFunction (E := E) (M := U))
    (e : OpenPartialHomeomorph M E) {y : E} (hy : e.symm y ∈ U) :
    (holomorphicManifoldZeroForm g).extension.inChart e y =
      constOfIsEmpty ℝ E (Fin 0) (OpenExtension.holomorphicOpenExtend g (e.symm y)) := by
  unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hy⟩]
  ext v
  rfl

theorem holomorphicManifoldZeroForm_d (g : Exponential.HolomorphicFunction (E := E) (M := U)) :
    Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (holomorphicManifoldZeroForm g) = 0 := by
  apply (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.eq_zero_iff_inChartOn U _).mpr
  intro e he
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro y
  change (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (holomorphicManifoldZeroForm g)).extension.inChart e y = 0
  rw [Open.ManifoldDolbeault.openManifoldDolbeaultD_eq_local rfl (fun _ _ _ _ => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E _) e he y.property]
  have heq : (holomorphicManifoldZeroForm g).extension.inChart e =ᶠ[𝓝 (y : E)]
      (fun z => constOfIsEmpty ℝ E (Fin 0) (OpenExtension.holomorphicOpenExtend g (e.symm z))) := by
    filter_upwards [(Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property] with z hz
    exact holomorphicManifoldZeroForm_inChart g e hz.2
  have hc : DifferentiableAt ℂ (OpenExtension.holomorphicOpenExtend g ∘ e.symm) (y : E) :=
    ((ManifoldCoordinates.holomorphicOpenExtend_chart_contDiff g e he).contDiffAt
      ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property)).differentiableAt (by simp)
  have hz := (DolbeaultZeroForms.extDerivDoublePrime_zeroForm_eq_zero_iff (hc.restrictScalars ℝ)).mpr hc
  unfold Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime
  rw [heq.fderiv_eq]
  exact hz

def holomorphicManifoldZeroFormLinear (U : Opens M) :
    Exponential.HolomorphicFunction (E := E) (M := U) →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0 where
  toFun := holomorphicManifoldZeroForm
  map_add' f g := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    ext v
    simp only [holomorphicManifoldZeroForm_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.add_apply,
      ContinuousAlternatingMap.add_apply]
    rfl
  map_smul' c f := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    ext v
    simp only [holomorphicManifoldZeroForm_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smul_apply,
      ContinuousAlternatingMap.smul_apply]
    rfl

theorem holomorphicManifoldZeroFormLinear_injective (U : Opens M) :
    Function.Injective (holomorphicManifoldZeroFormLinear (E := E) U) := by
  intro f g h
  apply ContMDiffMap.ext
  intro x
  have hv := congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0 => a x 0) h
  exact (holomorphicManifoldZeroForm_apply f x 0).symm.trans
    (hv.trans (holomorphicManifoldZeroForm_apply g x 0))

theorem holomorphicManifoldZeroForm_restrict (h : V ≤ U)
    (g : Exponential.HolomorphicFunction (E := E) (M := U))
    (g' : Exponential.HolomorphicFunction (E := E) (M := V))
    (hg : ∀ x : V, g' x = g (Opens.inclusion h x)) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (holomorphicManifoldZeroForm g) =
      holomorphicManifoldZeroForm g' := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  change holomorphicManifoldZeroForm g (Opens.inclusion h x) v = holomorphicManifoldZeroForm g' x v
  rw [holomorphicManifoldZeroForm_apply, holomorphicManifoldZeroForm_apply, hg]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ManifoldZeroForms
