import OAI.Analysis.DifferentialForms.Manifold.Derivative

/-! # Local Derivative -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Local exterior differentiation of actual manifold covectors

These results require smoothness only on the specified open domain. In
particular they do not assert that a section extended by zero across its
boundary is globally smooth. Chart independence, regularity, locality and
square-zero all hold on the original domain.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ} {U : Set M}

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Smoothness in a chart near a point needs only smoothness on its open domain. -/
theorem LocalDerivative.smoothManifoldFormOn_contDiffAt_inChart {form : Algebra.RawManifoldForm E M n}
    (hU : IsOpen U) (hform : Algebra.IsSmoothManifoldFormOn form U)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ Algebra.manifoldFormChartDomain e U) : ContDiffAt ℝ ∞ (form.inChart e) y :=
  (hform e he).contDiffAt ((Algebra.isOpen_manifoldFormChartDomain e hU).mem_nhds hy)

/-- Two chart derivatives agree at every point where the form is smooth. -/
theorem Algebra.RawManifoldForm.chartExteriorDerivative_eq_on (form : Algebra.RawManifoldForm E M n)
    (hU : IsOpen U) (hform : Algebra.IsSmoothManifoldFormOn form U)
    (e f : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (hf : f ∈ atlas E M)
    {x : M} (hex : x ∈ e.source) (hfx : x ∈ f.source) (hxU : x ∈ U) :
    form.chartExteriorDerivative e x = form.chartExteriorDerivative f x := by
  have hlocal : ContDiffAt ℝ ∞ (form.inChart f) (f x) :=
    LocalDerivative.smoothManifoldFormOn_contDiffAt_inChart hU hform f hf
      ⟨f.map_source hfx, by
        change f.symm (f x) ∈ U
        simpa only [f.left_inv hfx] using hxU⟩
  have htrans := form.extDeriv_inChart_transition_of_differentiableAt e f he hf
    (e.map_source hex) (by simpa only [e.left_inv hex] using hfx)
    (by simpa only [e.left_inv hex] using hlocal.differentiableAt (by simp))
  rw [e.left_inv hex] at htrans
  ext v
  change extDeriv (form.inChart e) (e x) (fun i => Charts.chartTangentMap e x (v i)) =
    extDeriv (form.inChart f) (f x) (fun i => Charts.chartTangentMap f x (v i))
  rw [htrans]
  apply congrArg (extDeriv (form.inChart f) (f x))
  funext i
  exact congrArg (fun g => g (v i)) (Derivative.chartTangentMap_transition_comp e f he hf hex hfx)

/-- The preferred chart gives the same derivative as every atlas chart on U. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_eq_chart_on (form : Algebra.RawManifoldForm E M n)
    (hU : IsOpen U) (hform : Algebra.IsSmoothManifoldFormOn form U)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {x : M}
    (hx : x ∈ e.source) (hxU : x ∈ U) :
    form.exteriorDerivative x = form.chartExteriorDerivative e x :=
  form.chartExteriorDerivative_eq_on hU hform (chartAt E x) e
    (chart_mem_atlas E x) he (mem_chart_source E x) hx hxU

/-- The derivative has the ordinary exterior-derivative expression on the chart domain. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_inChart_on (form : Algebra.RawManifoldForm E M n)
    (hU : IsOpen U) (hform : Algebra.IsSmoothManifoldFormOn form U)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ Algebra.manifoldFormChartDomain e U) :
    form.exteriorDerivative.inChart e y = extDeriv (form.inChart e) y := by
  calc
    form.exteriorDerivative.inChart e y = (form.chartExteriorDerivative e).inChart e y := by
      unfold Algebra.RawManifoldForm.inChart
      rw [form.exteriorDerivative_eq_chart_on hU hform e he (e.map_target hy.1) hy.2]
    _ = extDeriv (form.inChart e) y := form.chartExteriorDerivative_inChart e he hy.1

/-- Exterior differentiation preserves smoothness on the original open domain. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_smooth_on (form : Algebra.RawManifoldForm E M n)
    (hU : IsOpen U) (hform : Algebra.IsSmoothManifoldFormOn form U) :
    Algebra.IsSmoothManifoldFormOn form.exteriorDerivative U := by
  intro e he
  have hd : ContDiffOn ℝ ∞ (extDeriv (form.inChart e)) (Algebra.manifoldFormChartDomain e U) :=
    ExteriorDerivativeSmooth.contDiffOn_extDeriv_of_isOpen (hform e he)
    (Algebra.isOpen_manifoldFormChartDomain e hU) (by simp)
  exact hd.congr (fun y hy => form.exteriorDerivative_inChart_on hU hform e he hy)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative at a point depends only on the field in its open neighborhood. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_congr_on (form other : Algebra.RawManifoldForm E M n)
    (hU : IsOpen U) (heq : ∀ x ∈ U, form x = other x) {x : M} (hx : x ∈ U) :
    form.exteriorDerivative x = other.exteriorDerivative x := by
  let e := chartAt E x
  have heqChart : form.inChart e =ᶠ[𝓝 (e x)] other.inChart e := by
    have hex : e x ∈ Algebra.manifoldFormChartDomain e U :=
      ⟨e.map_source (mem_chart_source E x), by
        change e.symm (e x) ∈ U
        simpa only [e.left_inv (mem_chart_source E x)] using hx⟩
    filter_upwards [(Algebra.isOpen_manifoldFormChartDomain e hU).mem_nhds hex] with y hy
    unfold Algebra.RawManifoldForm.inChart
    rw [heq (e.symm y) hy.2]
  change (extDeriv (form.inChart e) (e x)).compContinuousLinearMap (Charts.chartTangentMap e x) =
    (extDeriv (other.inChart e) (e x)).compContinuousLinearMap (Charts.chartTangentMap e x)
  rw [heqChart.extDeriv_eq]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Additivity of the derivative at every point of a smoothness domain. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_add_on (form other : Algebra.RawManifoldForm E M n)
    (hU : IsOpen U) (hform : Algebra.IsSmoothManifoldFormOn form U)
    (hother : Algebra.IsSmoothManifoldFormOn other U) {x : M} (hx : x ∈ U) :
    (form + other).exteriorDerivative x = form.exteriorDerivative x + other.exteriorDerivative x := by
  let e := chartAt E x
  have hex : e x ∈ Algebra.manifoldFormChartDomain e U :=
    ⟨e.map_source (mem_chart_source E x), by
      change e.symm (e x) ∈ U
      simpa only [e.left_inv (mem_chart_source E x)] using hx⟩
  have hf := (LocalDerivative.smoothManifoldFormOn_contDiffAt_inChart hU hform e
    (chart_mem_atlas E x) hex).differentiableAt (by simp)
  have hg := (LocalDerivative.smoothManifoldFormOn_contDiffAt_inChart hU hother e
    (chart_mem_atlas E x) hex).differentiableAt (by simp)
  ext v
  change extDeriv ((form + other).inChart e) (e x) (fun i => Charts.chartTangentMap e x (v i)) =
    (extDeriv (form.inChart e) (e x) + extDeriv (other.inChart e) (e x))
      (fun i => Charts.chartTangentMap e x (v i))
  rw [Algebra.RawManifoldForm.inChart_add, extDeriv_add hf hg]

/-- The exterior derivative squares to zero at every point of the smoothness domain. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_squared_on (form : Algebra.RawManifoldForm E M n)
    (hU : IsOpen U) (hform : Algebra.IsSmoothManifoldFormOn form U) {x : M} (hx : x ∈ U) :
    form.exteriorDerivative.exteriorDerivative x = 0 := by
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hex : e x ∈ Algebra.manifoldFormChartDomain e U :=
    ⟨e.map_source (mem_chart_source E x), by
      change e.symm (e x) ∈ U
      simpa only [e.left_inv (mem_chart_source E x)] using hx⟩
  have heq : form.exteriorDerivative.inChart e =ᶠ[𝓝 (e x)] extDeriv (form.inChart e) := by
    filter_upwards [(Algebra.isOpen_manifoldFormChartDomain e hU).mem_nhds hex] with y hy
    exact form.exteriorDerivative_inChart_on hU hform e he hy
  change (extDeriv (form.exteriorDerivative.inChart e) (e x)).compContinuousLinearMap
    (Charts.chartTangentMap e x) = 0
  rw [heq.extDeriv_eq, SquareZero.extDeriv_extDeriv_of_contDiffAt
    (LocalDerivative.smoothManifoldFormOn_contDiffAt_inChart hU hform e he hex)]
  ext v
  rfl

end

end OAI.Analysis.DifferentialForms.Manifold
