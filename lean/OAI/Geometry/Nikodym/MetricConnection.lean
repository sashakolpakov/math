import Mathlib

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The first-kind Christoffel vector obtained from the actual derivative of
a coordinate metric. This is the Koszul formula in commuting coordinates. -/
def metricKoszulVector (D : E →L[ℝ] E →L[ℝ] E) (u v : E) : E :=
  (1/2 : ℝ) • (D u v + D v u - (D.flip u).adjoint v)

theorem inner_metricKoszulVector (D : E →L[ℝ] E →L[ℝ] E) (u v w : E) :
    ⟪metricKoszulVector D u v,w⟫ =
      (⟪D u v,w⟫ + ⟪D v u,w⟫ - ⟪D w u,v⟫)/2 := by
  simp only [metricKoszulVector,real_inner_smul_left,inner_sub_left,inner_add_left,
    ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.flip_apply]
  rw [real_inner_comm v (D w u)]
  ring

theorem metricKoszulVector_symmetric (D : E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ w u v, ⟪D w u,v⟫ = ⟪u,D w v⟫) (u v : E) :
    metricKoszulVector D u v = metricKoszulVector D v u := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_metricKoszulVector,inner_metricKoszulVector,hD w u v,
    real_inner_comm u (D w v)]
  ring

theorem metricKoszulVector_compatible (D : E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ w u v, ⟪D w u,v⟫ = ⟪u,D w v⟫) (u v w : E) :
    ⟪metricKoszulVector D u v,w⟫ + ⟪v,metricKoszulVector D u w⟫ = ⟪D u v,w⟫ := by
  rw [real_inner_comm (metricKoszulVector D u w) v,inner_metricKoszulVector,inner_metricKoszulVector]
  have h₁ : ⟪D u w,v⟫ = ⟪D u v,w⟫ := by
    rw [hD u w v]
    exact real_inner_comm _ _
  linarith

omit [FiniteDimensional ℝ E] in
/-- Symmetry of the derivative is proved by differentiating the actual
metric symmetry on a neighborhood, not supplied as an extra metric axiom. -/
theorem fderiv_metric_symmetric {g : E → E →L[ℝ] E} {x : E}
    (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, ∀ u v, ⟪g y u,v⟫ = ⟪u,g y v⟫) :
    ∀ w u v, ⟪fderiv ℝ g x w u,v⟫ = ⟪u,fderiv ℝ g x w v⟫ := by
  intro w u v
  have hl := (hg.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).inner ℝ
    (hasFDerivAt_const v x)
  have hr := (hasFDerivAt_const u x).inner ℝ
    (hg.hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  have he : (fun y => ⟪g y u,v⟫) =ᶠ[𝓝 x] (fun y => ⟪u,g y v⟫) := by
    filter_upwards [hs] with y hy
    exact hy u v
  have hd := (hl.congr_of_eventuallyEq he.symm).unique hr
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L w) hd
  simpa using hh

/-- The actual coordinate Christoffel operator, obtained by raising the
index in the Koszul formula with the inverse metric. -/
def metricChristoffel (g : E → E →L[ℝ] E) (x u v : E) : E :=
  (g x).inverse (metricKoszulVector (fderiv ℝ g x) u v)

end OAI.Geometry.Nikodym
