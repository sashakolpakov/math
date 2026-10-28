import OAI.Analysis.DifferentialForms.Manifold.Charts
import OAI.Analysis.DifferentialForms.Manifold.Transition
import OAI.Analysis.DifferentialForms.Manifold.Algebra
import OAI.Analysis.DifferentialForms.Manifold.ComplexLinearity

/-! # Derivative -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
The chart construction of the exterior derivative on actual manifold covectors.
Chart agreement and the resulting global operator are proved below.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

section

/-- Differentiate in a chart and return the result to the actual tangent space. -/
def Algebra.RawManifoldForm.chartExteriorDerivative (form : Algebra.RawManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) : Algebra.RawManifoldForm E M (n + 1) :=
  fun x => (extDeriv (form.inChart e) (e x)).compContinuousLinearMap (Charts.chartTangentMap e x)

/-- A globally specified exterior derivative, using the distinguished chart at
each point. Independence of this choice is a theorem, not an input field. -/
def Algebra.RawManifoldForm.exteriorDerivative (form : Algebra.RawManifoldForm E M n) : Algebra.RawManifoldForm E M (n + 1) :=
  fun x => form.chartExteriorDerivative (chartAt E x) x

theorem Algebra.RawManifoldForm.chartExteriorDerivative_inChart (form : Algebra.RawManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ e.target) :
    (form.chartExteriorDerivative e).inChart e y = extDeriv (form.inChart e) y := by
  ext v
  change extDeriv (form.inChart e) (e (e.symm y))
      (fun i => Charts.chartTangentMap e (e.symm y) (Charts.chartInverseTangentMap e y (v i))) =
    extDeriv (form.inChart e) y v
  rw [e.right_inv hy]
  have hv : (fun i => Charts.chartTangentMap e (e.symm y) (Charts.chartInverseTangentMap e y (v i))) = v := by
    funext i
    exact congrArg (fun f => f (v i)) (Charts.chartTangentMap_comp_inverse e he hy)
  rw [hv]

end

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem Derivative.smoothForm_contDiffAt_inChart {form : Algebra.RawManifoldForm E M n}
    (hform : Algebra.IsSmoothManifoldFormOn form univ)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ e.target) : ContDiffAt ℝ ∞ (form.inChart e) y := by
  apply (hform e he).contDiffAt
  apply (Algebra.isOpen_manifoldFormChartDomain e isOpen_univ).mem_nhds
  exact ⟨hy, mem_univ _⟩

theorem Derivative.chartTangentMap_transition_comp (e f : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (hf : f ∈ atlas E M) {x : M}
    (hex : x ∈ e.source) (hfx : x ∈ f.source) :
    (fderiv ℝ (f ∘ e.symm) (e x)).comp (Charts.chartTangentMap e x) =
      Charts.chartTangentMap f x := by
  rw [Charts.fderiv_chart_transition e f he hf (e.map_source hex)
    (by simpa only [e.left_inv hex] using hfx), e.left_inv hex]
  ext v
  change Charts.chartTangentMap f x (Charts.chartInverseTangentMap e (e x) (Charts.chartTangentMap e x v)) =
    Charts.chartTangentMap f x v
  exact congrArg (Charts.chartTangentMap f x)
    (congrArg (fun g => g v) (Charts.chartInverseTangentMap_comp e he hex))

section

/-- The chartwise derivative is independent of the chart on every overlap. -/
theorem Algebra.RawManifoldForm.chartExteriorDerivative_eq (form : Algebra.RawManifoldForm E M n)
    (hform : Algebra.IsSmoothManifoldFormOn form univ)
    (e f : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (hf : f ∈ atlas E M)
    {x : M} (hex : x ∈ e.source) (hfx : x ∈ f.source) :
    form.chartExteriorDerivative e x = form.chartExteriorDerivative f x := by
  have htrans := form.extDeriv_inChart_transition hform e f he hf
    (e.map_source hex) (by simpa only [e.left_inv hex] using hfx)
  rw [e.left_inv hex] at htrans
  ext v
  change extDeriv (form.inChart e) (e x) (fun i => Charts.chartTangentMap e x (v i)) =
    extDeriv (form.inChart f) (f x) (fun i => Charts.chartTangentMap f x (v i))
  rw [htrans]
  apply congrArg (extDeriv (form.inChart f) (f x))
  funext i
  exact congrArg (fun g => g (v i)) (Derivative.chartTangentMap_transition_comp e f he hf hex hfx)

/-- The preferred-chart definition agrees with the derivative in any atlas chart. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_eq_chart (form : Algebra.RawManifoldForm E M n)
    (hform : Algebra.IsSmoothManifoldFormOn form univ)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {x : M}
    (hx : x ∈ e.source) :
    form.exteriorDerivative x = form.chartExteriorDerivative e x :=
  form.chartExteriorDerivative_eq hform (chartAt E x) e
    (chart_mem_atlas E x) he (mem_chart_source E x) hx

/-- Every chart expression of the global derivative is the ordinary exterior derivative. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_inChart (form : Algebra.RawManifoldForm E M n)
    (hform : Algebra.IsSmoothManifoldFormOn form univ)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ e.target) :
    form.exteriorDerivative.inChart e y = extDeriv (form.inChart e) y := by
  calc
    form.exteriorDerivative.inChart e y = (form.chartExteriorDerivative e).inChart e y := by
      unfold Algebra.RawManifoldForm.inChart
      rw [form.exteriorDerivative_eq_chart hform e he (e.map_target hy)]
    _ = extDeriv (form.inChart e) y := form.chartExteriorDerivative_inChart e he hy

/-- Chart independence proves that the global derivative is smooth. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_smooth (form : Algebra.RawManifoldForm E M n)
    (hform : Algebra.IsSmoothManifoldFormOn form univ) :
    Algebra.IsSmoothManifoldFormOn form.exteriorDerivative univ := by
  intro e he
  have hs : ContDiffOn ℝ ∞ (form.inChart e) e.target := by
    simpa only [Algebra.manifoldFormChartDomain, preimage_univ, inter_univ] using hform e he
  have hd : ContDiffOn ℝ ∞ (extDeriv (form.inChart e)) e.target :=
    ExteriorDerivativeSmooth.contDiffOn_extDeriv_of_isOpen hs e.open_target (by simp)
  have hfinal : ContDiffOn ℝ ∞ (form.exteriorDerivative.inChart e) e.target :=
    hd.congr (fun y hy => form.exteriorDerivative_inChart hform e he hy)
  simpa only [Algebra.manifoldFormChartDomain, preimage_univ, inter_univ] using hfinal

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem Algebra.RawManifoldForm.exteriorDerivative_add (form other : Algebra.RawManifoldForm E M n)
    (hform : Algebra.IsSmoothManifoldFormOn form univ)
    (hother : Algebra.IsSmoothManifoldFormOn other univ) :
    (form + other).exteriorDerivative = form.exteriorDerivative + other.exteriorDerivative := by
  funext x
  let e := chartAt E x
  have hx : e x ∈ e.target := e.map_source (mem_chart_source E x)
  have hf := (Derivative.smoothForm_contDiffAt_inChart hform e (chart_mem_atlas E x) hx).differentiableAt
    (by simp)
  have hg := (Derivative.smoothForm_contDiffAt_inChart hother e (chart_mem_atlas E x) hx).differentiableAt
    (by simp)
  ext v
  change extDeriv ((form + other).inChart e) (e x) (fun i => Charts.chartTangentMap e x (v i)) =
    (extDeriv (form.inChart e) (e x) + extDeriv (other.inChart e) (e x))
      (fun i => Charts.chartTangentMap e x (v i))
  rw [Algebra.RawManifoldForm.inChart_add, extDeriv_add hf hg]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem Algebra.RawManifoldForm.exteriorDerivative_smul (c : ℂ) (form : Algebra.RawManifoldForm E M n) :
    (c • form).exteriorDerivative = c • form.exteriorDerivative := by
  funext x
  let e := chartAt E x
  ext v
  change extDeriv ((c • form).inChart e) (e x) (fun i => Charts.chartTangentMap e x (v i)) =
    (c • extDeriv (form.inChart e) (e x)) (fun i => Charts.chartTangentMap e x (v i))
  rw [Algebra.RawManifoldForm.inChart_smul, ComplexLinearity.extDeriv_complex_smul]

/-- The global derivative squares to zero, proved in an actual chart neighborhood. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_squared (form : Algebra.RawManifoldForm E M n)
    (hform : Algebra.IsSmoothManifoldFormOn form univ) :
    form.exteriorDerivative.exteriorDerivative = 0 := by
  funext x
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hx : e x ∈ e.target := e.map_source (mem_chart_source E x)
  have heq : form.exteriorDerivative.inChart e =ᶠ[𝓝 (e x)] extDeriv (form.inChart e) := by
    filter_upwards [e.open_target.mem_nhds hx] with y hy
    exact form.exteriorDerivative_inChart hform e he hy
  change (extDeriv (form.exteriorDerivative.inChart e) (e x)).compContinuousLinearMap
    (Charts.chartTangentMap e x) = 0
  rw [heq.extDeriv_eq, SquareZero.extDeriv_extDeriv_of_contDiffAt
    (Derivative.smoothForm_contDiffAt_inChart hform e he hx)]
  ext v
  rfl

end

/-- The complex-linear exterior derivative on genuine smooth manifold forms. -/
def Algebra.SmoothManifoldForm.d : Algebra.SmoothManifoldForm E M n →ₗ[ℂ] Algebra.SmoothManifoldForm E M (n + 1) where
  toFun form :=
    ⟨(form : Algebra.RawManifoldForm E M n).exteriorDerivative,
      (form : Algebra.RawManifoldForm E M n).exteriorDerivative_smooth form.smooth⟩
  map_add' form other := by
    apply Algebra.SmoothManifoldForm.ext
    intro x
    exact congrFun ((form : Algebra.RawManifoldForm E M n).exteriorDerivative_add
      (other : Algebra.RawManifoldForm E M n) form.smooth other.smooth) x
  map_smul' c form := by
    apply Algebra.SmoothManifoldForm.ext
    intro x
    exact congrFun ((form : Algebra.RawManifoldForm E M n).exteriorDerivative_smul c) x

@[simp]
theorem Algebra.SmoothManifoldForm.d_apply (form : Algebra.SmoothManifoldForm E M n) (x : M) :
    Algebra.SmoothManifoldForm.d form x = (form : Algebra.RawManifoldForm E M n).exteriorDerivative x := rfl

theorem Algebra.SmoothManifoldForm.d_inChart (form : Algebra.SmoothManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ e.target) :
    (Algebra.SmoothManifoldForm.d form : Algebra.RawManifoldForm E M (n + 1)).inChart e y =
      extDeriv ((form : Algebra.RawManifoldForm E M n).inChart e) y :=
  (form : Algebra.RawManifoldForm E M n).exteriorDerivative_inChart form.smooth e he hy

@[simp]
theorem Algebra.SmoothManifoldForm.d_squared (form : Algebra.SmoothManifoldForm E M n) : Algebra.SmoothManifoldForm.d (Algebra.SmoothManifoldForm.d form) = 0 := by
  apply Algebra.SmoothManifoldForm.ext
  intro x
  exact congrFun ((form : Algebra.RawManifoldForm E M n).exteriorDerivative_squared form.smooth) x

end

end OAI.Analysis.DifferentialForms.Manifold
