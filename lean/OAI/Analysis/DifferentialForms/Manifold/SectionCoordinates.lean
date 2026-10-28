import OAI.Analysis.DifferentialForms.Manifold.ChartEquiv

/-! # Section Coordinates -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Coordinates of an arbitrary open-domain manifold form

The domain in a chart is the intersection of the chart target with the
inverse image of the section domain. Coordinates determine the actual
tangent covectors and intertwine both constructed exterior derivatives.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Nullary tangent covectors evaluate independently of the coordinate tangent map. -/
theorem Algebra.RawManifoldForm.inChart_zero_apply (form : Algebra.RawManifoldForm E M 0)
    (e : OpenPartialHomeomorph M E) (y : E) :
    form.inChart e y 0 = form (e.symm y) 0 := by
  unfold Algebra.RawManifoldForm.inChart
  change form (e.symm y) _ = form (e.symm y) 0
  congr 1
  exact Subsingleton.elim _ _

/-- The coordinate expression of a section on an arbitrary open domain. -/
def Open.SmoothOpenManifoldForm.inChartOn (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (U : Opens M) :
    Open.SmoothOpenManifoldForm E U n →ₗ[ℂ] OpenD.SmoothOpenForm (ChartEquiv.chartImageOpen e U) n where
  toFun form := OpenD.SmoothOpenForm.ofRaw (ChartEquiv.chartImageOpen e U) (form.extension.inChart e)
    (form.smooth e he)
  map_add' form other := by
    apply OpenD.SmoothOpenForm.ext
    intro y
    change (form + other).extension.inChart e (y : E) =
      form.extension.inChart e (y : E) + other.extension.inChart e (y : E)
    rw [Open.SmoothOpenManifoldForm.extension_add, Algebra.RawManifoldForm.inChart_add]
    rfl
  map_smul' c form := by
    apply OpenD.SmoothOpenForm.ext
    intro y
    change (c • form).extension.inChart e (y : E) = c • form.extension.inChart e (y : E)
    rw [Open.SmoothOpenManifoldForm.extension_smul, Algebra.RawManifoldForm.inChart_smul]
    rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
@[simp]
theorem Open.SmoothOpenManifoldForm.inChartOn_apply (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (U : Opens M) (form : Open.SmoothOpenManifoldForm E U n) (y : ChartEquiv.chartImageOpen e U) :
    Open.SmoothOpenManifoldForm.inChartOn e he U form y = form.extension.inChart e (y : E) := rfl

/-- Coordinate expressions recover the covector after the genuine chart tangent map. -/
theorem Open.SmoothOpenManifoldForm.inChartOn_apply_chart (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (U : Opens M) (form : Open.SmoothOpenManifoldForm E U n) (x : U)
    (hx : (x : M) ∈ e.source) :
    (Open.SmoothOpenManifoldForm.inChartOn e he U form ⟨e x, ChartEquiv.mem_chartImageOpen e U hx x.property⟩).compContinuousLinearMap
      (Charts.chartTangentMap e x) = form x := by
  change Algebra.RawManifoldForm.fromChart e (form.extension.inChart e) (x : M) = form x
  exact (Algebra.RawManifoldForm.fromChart_inChart_apply e he form.extension hx).trans
    (Open.SmoothOpenManifoldForm.extension_apply form x)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Coordinate expressions of zero-forms are the ordinary scalar composition. -/
theorem Open.SmoothOpenManifoldForm.inChartOn_zero_apply (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (U : Opens M) (form : Open.SmoothOpenManifoldForm E U 0) (y : ChartEquiv.chartImageOpen e U) :
    Open.SmoothOpenManifoldForm.inChartOn e he U form y 0 = form ⟨e.symm y, y.property.2⟩ 0 := by
  rw [Open.SmoothOpenManifoldForm.inChartOn_apply, Algebra.RawManifoldForm.inChart_zero_apply]
  rw [Open.SmoothOpenManifoldForm.extension_apply form ⟨e.symm y, y.property.2⟩]

/-- The constructed manifold derivative becomes the ordinary coordinate derivative. -/
theorem Open.SmoothOpenManifoldForm.inChartOn_d (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (U : Opens M) (form : Open.SmoothOpenManifoldForm E U n) :
    OpenD.SmoothOpenForm.d (Open.SmoothOpenManifoldForm.inChartOn e he U form) = Open.SmoothOpenManifoldForm.inChartOn e he U (Open.SmoothOpenManifoldForm.d form) := by
  apply OpenD.SmoothOpenForm.ext
  intro y
  change OpenD.SmoothOpenForm.d (OpenD.SmoothOpenForm.ofRaw (ChartEquiv.chartImageOpen e U)
    (form.extension.inChart e) (form.smooth e he)) y =
      (Open.SmoothOpenManifoldForm.d form).extension.inChart e (y : E)
  exact (OpenD.SmoothOpenForm.d_ofRaw_apply (form.extension.inChart e)
    (form.smooth e he) y).trans (Open.SmoothOpenManifoldForm.d_inChart form e he y.property).symm

/-- Vanishing in all genuine coordinate domains is equivalent to vanishing of the section. -/
theorem Open.SmoothOpenManifoldForm.eq_zero_iff_inChartOn (U : Opens M) (form : Open.SmoothOpenManifoldForm E U n) :
    form = 0 ↔ ∀ (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M),
      Open.SmoothOpenManifoldForm.inChartOn e he U form = 0 := by
  constructor
  · rintro rfl e he
    exact map_zero _
  · intro h
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    let e := chartAt E (x : M)
    have he : e ∈ atlas E M := chart_mem_atlas E (x : M)
    have hx : (x : M) ∈ e.source := mem_chart_source E (x : M)
    have hcoeff : Open.SmoothOpenManifoldForm.inChartOn e he U form ⟨e x, ChartEquiv.mem_chartImageOpen e U hx x.property⟩ = 0 := by
      rw [h e he]
      rfl
    calc
      form x = (Open.SmoothOpenManifoldForm.inChartOn e he U form
          ⟨e x, ChartEquiv.mem_chartImageOpen e U hx x.property⟩).compContinuousLinearMap
          (Charts.chartTangentMap e x) :=
        (Open.SmoothOpenManifoldForm.inChartOn_apply_chart e he U form x hx).symm
      _ = 0 := by
        rw [hcoeff]
        rfl

end

end OAI.Analysis.DifferentialForms.Manifold
