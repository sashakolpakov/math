import OAI.Geometry.Nikodym.Riemannian.Distance

noncomputable section
open Set Bundle Manifold

namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Coercivity controls ordinary coordinate velocities by the actual
Riemannian tangent norm. -/
theorem coordinate_norm_le (g : SmoothCoordinateMetric E) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ g.domain, ∀ v, c * ‖v‖^2 ≤ g.inner x v v) :
    letI := g.toRiemannianBundle
    ∀ (x : g.openDomain) (v : TangentSpace 𝓘(ℝ,E) x),
      ‖(show E from v)‖ ≤ (1 / Real.sqrt c) * ‖v‖ := by
  let := g.toRiemannianBundle
  intro x v
  let w : E := v
  rw [g.norm_tangent]
  change ‖w‖ ≤ (1 / Real.sqrt c) * Real.sqrt (g.inner x w w)
  have hs := Real.sqrt_le_sqrt (hcoer x x.property w)
  rw [Real.sqrt_mul hc.le,Real.sqrt_sq (norm_nonneg w)] at hs
  calc
    ‖w‖ ≤ Real.sqrt (g.inner x w w) / Real.sqrt c :=
      (le_div_iff₀ (Real.sqrt_pos.mpr hc)).mpr (by simpa [mul_comm] using hs)
    _ = _ := by ring

/-- Upper coefficient bounds control the genuine tangent norm. -/
theorem tangent_norm_le (g : SmoothCoordinateMetric E) {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ x ∈ g.domain, ∀ v, g.inner x v v ≤ C * ‖v‖^2) :
    letI := g.toRiemannianBundle
    ∀ (x : g.openDomain) (v : TangentSpace 𝓘(ℝ,E) x),
      ‖v‖ ≤ Real.sqrt C * ‖(show E from v)‖ := by
  let := g.toRiemannianBundle
  intro x v
  let w : E := v
  rw [g.norm_tangent]
  change Real.sqrt (g.inner x w w) ≤ Real.sqrt C * ‖w‖
  simpa only [Real.sqrt_mul hC,Real.sqrt_sq (norm_nonneg w)] using
    Real.sqrt_le_sqrt (hupper x x.property w)

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
