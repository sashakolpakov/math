import OAI.Geometry.Nikodym.IsometryConnection
import OAI.Geometry.Nikodym.MetricGeodesic

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A C² local isometry sends actual metric geodesics to metric geodesics.
The target velocity is the genuine derivative of the mapped curve. -/
theorem IsMetricGeodesic.map_local_isometry
    {g : SmoothCoordinateMetric E} {h : SmoothCoordinateMetric F}
    {γ v : ℝ → E} {I : Set ℝ} (hc : IsMetricGeodesic g γ v I)
    {Φ : E → F}
    (hdom : ∀ t ∈ I, Φ (γ t) ∈ h.domain)
    (hΦ : ∀ t ∈ I, ContDiffAt ℝ 2 Φ (γ t))
    (hsurj : ∀ t ∈ I, Function.Surjective (fderiv ℝ Φ (γ t)))
    (hmetric : ∀ t ∈ I, ∀ᶠ y in 𝓝 (γ t), ∀ u w,
      g.inner y u w = h.inner (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y w)) :
    IsMetricGeodesic h (fun t => Φ (γ t))
      (fun t => fderiv ℝ Φ (γ t) (v t)) I := by
  refine ⟨?_,?_,hdom⟩
  · intro t ht
    simpa only [Function.comp_apply] using!
      ((hΦ t ht).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
        (hc.position_derivative t ht)
  · intro t ht
    have hd := (((hΦ t ht).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hc.position_derivative t ht)
    have hv := hd.clm_apply (hc.velocity_derivative t ht)
    have he := g.local_isometry_christoffel h (hc.regular t ht) (hdom t ht)
      (hΦ t ht) (hsurj t ht) (hmetric t ht) (v t) (v t)
    convert hv using 1
    · rfl
    · simp only [Function.comp_apply,map_neg]
      rw [he]
      abel

end OAI.Geometry.Nikodym
