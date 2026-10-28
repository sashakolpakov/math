import OAI.Analysis.DifferentialForms.Manifold.TangentCoordinates
import OAI.Analysis.DifferentialForms.Manifold.ComplexCharts
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Complex Action -/

namespace OAI.Analysis.DifferentialForms.Manifold.ComplexAction

noncomputable section

/-! The complex scalar action on actual real tangent spaces, transported
through the genuine holomorphic atlas and proved independent of the chart. -/

open scoped _root_.Manifold ContDiff

attribute [local instance] ComplexCharts.complexManifold_isRealSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

/-- Transport complex multiplication through the actual differential of a chart. -/
def chartComplexSMul (e : OpenPartialHomeomorph M E) (x : M) (z : ℂ)
    (v : TangentSpace 𝓘(ℝ, E) x) : TangentSpace 𝓘(ℝ, E) x :=
  Charts.chartInverseTangentMap e (e x) (z • Charts.chartTangentMap e x v)

/-- The complex action on the real tangent space, initially specified in the
preferred chart. Independence from that choice is proved below. -/
def complexTangentSMul (x : M) (z : ℂ) (v : TangentSpace 𝓘(ℝ, E) x) :
    TangentSpace 𝓘(ℝ, E) x := chartComplexSMul (chartAt E x) x z v

/-- The transported action is a genuine complex module structure and preserves
the existing additive group on the actual real tangent space. -/
@[instance_reducible]
def complexTangentModule (x : M) : Module ℂ (TangentSpace 𝓘(ℝ, E) x) :=
  (TangentCoordinates.preferredTangentEquiv (E := E) x).toLinearEquiv.toAddEquiv.module ℂ

theorem complexTangentModule_smul (x : M) (z : ℂ) (v : TangentSpace 𝓘(ℝ, E) x) :
    letI := complexTangentModule (E := E) x
    z • v = complexTangentSMul x z v := rfl

/-- The transported complex action extends the original real scalar action. -/
theorem complexTangentModule_isScalarTower (x : M) :
    letI := complexTangentModule (E := E) x
    IsScalarTower ℝ ℂ (TangentSpace 𝓘(ℝ, E) x) :=
  (TangentCoordinates.preferredTangentEquiv (E := E) x).toLinearEquiv.isScalarTower ℂ

/-- Multiplication by a complex number is continuous real-linear on each tangent space. -/
def complexTangentScalarMap (x : M) (z : ℂ) :
    TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x :=
  (TangentCoordinates.preferredTangentEquiv (E := E) x).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.lsmul ℝ ℂ z : E →L[ℝ] E).comp
      (TangentCoordinates.preferredTangentEquiv (E := E) x).toContinuousLinearMap)

@[simp]
theorem complexTangentScalarMap_apply (x : M) (z : ℂ) (v : TangentSpace 𝓘(ℝ, E) x) :
    complexTangentScalarMap x z v = complexTangentSMul x z v := rfl

/-- Complex multiplication is jointly continuous on each actual tangent space. -/
theorem continuous_complexTangentSMul (x : M) :
    Continuous (fun p : ℂ × TangentSpace 𝓘(ℝ, E) x => complexTangentSMul x p.1 p.2) := by
  let e := TangentCoordinates.preferredTangentEquiv (E := E) x
  change Continuous (fun p : ℂ × TangentSpace 𝓘(ℝ, E) x => e.symm (p.1 • e p.2))
  exact e.symm.continuous.comp (continuous_fst.smul (e.continuous.comp continuous_snd))

/-- The real derivative of a holomorphic transition is the restriction of
its complex derivative, expressed in actual tangent coordinates. -/
theorem chartTransition_tangent_eq_complex (e f : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (hf : f ∈ atlas E M) (x : M)
    (hex : x ∈ e.source) (hfx : x ∈ f.source) :
    (Charts.chartTangentMap f x).comp (Charts.chartInverseTangentMap e (e x)) =
      (fderiv ℂ (f ∘ e.symm) (e x)).restrictScalars ℝ := by
  have hx : e.symm (e x) ∈ f.source := by simpa only [e.left_inv hex] using hfx
  have hhol :=
    (ComplexCharts.complexContDiffAt_chart_transition e f he hf (e.map_source hex) hx).differentiableAt (by simp)
  calc
    (Charts.chartTangentMap f x).comp (Charts.chartInverseTangentMap e (e x)) =
        fderiv ℝ (f ∘ e.symm) (e x) := by
      have h := Charts.fderiv_chart_transition e f he hf (e.map_source hex) hx
      rw [e.left_inv hex] at h
      exact h.symm
    _ = (fderiv ℂ (f ∘ e.symm) (e x)).restrictScalars ℝ := hhol.fderiv_restrictScalars ℝ

theorem chartTangentMap_inverse_smul (e f : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (hf : f ∈ atlas E M) (x : M)
    (hex : x ∈ e.source) (hfx : x ∈ f.source) (z : ℂ) (w : E) :
    Charts.chartTangentMap f x (Charts.chartInverseTangentMap e (e x) (z • w)) =
      z • Charts.chartTangentMap f x (Charts.chartInverseTangentMap e (e x) w) := by
  change ((Charts.chartTangentMap f x).comp (Charts.chartInverseTangentMap e (e x))) (z • w) =
    z • ((Charts.chartTangentMap f x).comp (Charts.chartInverseTangentMap e (e x))) w
  rw [chartTransition_tangent_eq_complex e f he hf x hex hfx]
  exact map_smul (fderiv ℂ (f ∘ e.symm) (e x)) z w

/-- Holomorphic transition derivatives prove that the transported complex
action is independent of the actual chart chosen at the point. -/
theorem chartComplexSMul_eq (e f : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (hf : f ∈ atlas E M) (x : M)
    (hex : x ∈ e.source) (hfx : x ∈ f.source) (z : ℂ)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    chartComplexSMul e x z v = chartComplexSMul f x z v := by
  apply (TangentCoordinates.chartTangentEquiv f hf x hfx).injective
  change Charts.chartTangentMap f x (chartComplexSMul e x z v) =
    Charts.chartTangentMap f x (chartComplexSMul f x z v)
  calc
    Charts.chartTangentMap f x (chartComplexSMul e x z v) =
        z • Charts.chartTangentMap f x (Charts.chartInverseTangentMap e (e x) (Charts.chartTangentMap e x v)) :=
      chartTangentMap_inverse_smul e f he hf x hex hfx z (Charts.chartTangentMap e x v)
    _ = z • Charts.chartTangentMap f x v := by
      rw [show Charts.chartInverseTangentMap e (e x) (Charts.chartTangentMap e x v) = v from
        (TangentCoordinates.chartTangentEquiv e he x hex).symm_apply_apply v]
    _ = Charts.chartTangentMap f x (chartComplexSMul f x z v) :=
      ((TangentCoordinates.chartTangentEquiv f hf x hfx).apply_symm_apply (z • Charts.chartTangentMap f x v)).symm

theorem complexTangentSMul_eq_chart (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (x : M) (hx : x ∈ e.source) (z : ℂ)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    complexTangentSMul x z v = chartComplexSMul e x z v :=
  chartComplexSMul_eq (chartAt E x) e (chart_mem_atlas E x) he x (mem_chart_source E x) hx z v

/-- In each actual holomorphic chart, the tangent action is ordinary complex multiplication. -/
theorem complexTangentSMul_inChart (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (x : M) (hx : x ∈ e.source) (z : ℂ)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    Charts.chartTangentMap e x (complexTangentSMul x z v) = z • Charts.chartTangentMap e x v := by
  rw [complexTangentSMul_eq_chart e he x hx z v]
  exact (TangentCoordinates.chartTangentEquiv e he x hx).apply_symm_apply (z • Charts.chartTangentMap e x v)

/-- The tangent action varies smoothly in the actual bundle coordinates,
including its scalar and tangent-vector arguments. -/
theorem complexTangentSMul_smooth_inChart (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) :
    ContDiffOn ℝ ∞ (fun p : E × (ℂ × E) =>
      Charts.chartTangentMap e (e.symm p.1)
        (complexTangentSMul (e.symm p.1) p.2.1
          (Charts.chartInverseTangentMap e p.1 p.2.2))) {p | p.1 ∈ e.target} := by
  have hs : ContDiff ℝ ∞ (fun p : E × (ℂ × E) => p.2.1 • p.2.2) :=
    (contDiff_fst.comp contDiff_snd).smul (contDiff_snd.comp contDiff_snd)
  apply hs.contDiffOn.congr
  intro p hp
  rw [complexTangentSMul_inChart e he (e.symm p.1) (e.map_target hp)]
  exact congrArg (fun w : E => p.2.1 • w)
    (congrArg (fun f => f p.2.2) (Charts.chartTangentMap_comp_inverse e he hp))

end

end OAI.Analysis.DifferentialForms.Manifold.ComplexAction
