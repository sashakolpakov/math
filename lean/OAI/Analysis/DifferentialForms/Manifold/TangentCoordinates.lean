import OAI.Analysis.DifferentialForms.Manifold.Charts

/-! # Tangent Coordinates -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-! Actual chart differentials as continuous real-linear tangent equivalences. -/

open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The differential of a genuine chart at a point of its source, with its
inverse proved to be the differential of the inverse chart. -/
def TangentCoordinates.chartTangentEquiv (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E where
  toFun := Charts.chartTangentMap e x
  invFun := Charts.chartInverseTangentMap e (e x)
  left_inv v := congrArg (fun f => f v) (Charts.chartInverseTangentMap_comp e he hx)
  right_inv v := by
    have h := Charts.chartTangentMap_comp_inverse e he (e.map_source hx)
    rw [e.left_inv hx] at h
    exact congrArg (fun f => f v) h
  map_add' := (Charts.chartTangentMap e x).map_add
  map_smul' := (Charts.chartTangentMap e x).map_smul
  continuous_toFun := (Charts.chartTangentMap e x).continuous
  continuous_invFun := (Charts.chartInverseTangentMap e (e x)).continuous

@[simp]
theorem TangentCoordinates.chartTangentEquiv_apply (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) (v : TangentSpace 𝓘(ℝ, E) x) :
    TangentCoordinates.chartTangentEquiv e he x hx v = Charts.chartTangentMap e x v := rfl

@[simp]
theorem TangentCoordinates.chartTangentEquiv_symm_apply (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) (v : E) :
    (TangentCoordinates.chartTangentEquiv e he x hx).symm v = Charts.chartInverseTangentMap e (e x) v := rfl

/-- The preferred chart gives a genuine tangent-coordinate equivalence. -/
def TangentCoordinates.preferredTangentEquiv (x : M) : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E :=
  TangentCoordinates.chartTangentEquiv (chartAt E x) (chart_mem_atlas E x) x (mem_chart_source E x)

/-- The chart expression at the image of a point is the covector transported
by the inverse of the actual chart differential. -/
theorem Algebra.RawManifoldForm.inChart_at {n : ℕ} (form : Algebra.RawManifoldForm E M n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (x : M) (hx : x ∈ e.source)
    (v : Fin n → E) :
    form.inChart e (e x) v = form x (fun i => (TangentCoordinates.chartTangentEquiv e he x hx).symm (v i)) := by
  change form (e.symm (e x)) (fun i => Charts.chartInverseTangentMap e (e x) (v i)) = _
  rw [e.left_inv hx]
  rfl

end

end OAI.Analysis.DifferentialForms.Manifold
