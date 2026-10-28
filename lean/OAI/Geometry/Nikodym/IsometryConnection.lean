import OAI.Geometry.Nikodym.IsometryKoszul
import OAI.Geometry.Nikodym.ParallelMetric

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Differentiate the actual metric pullback identity, with no connection
transformation assumed. -/
theorem local_isometry_metric_derivative
    (g : SmoothCoordinateMetric E) (h : SmoothCoordinateMetric F)
    {Φ : E → F} {x : E} (hx : x ∈ g.domain) (hy : Φ x ∈ h.domain)
    (hΦ : ContDiffAt ℝ 2 Φ x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      g.inner y u v = h.inner (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v))
    (a u v : E) :
    ⟪fderiv ℝ g.coefficient x a u,v⟫ =
      ⟪fderiv ℝ h.coefficient (Φ x) (fderiv ℝ Φ x a) (fderiv ℝ Φ x u),
        fderiv ℝ Φ x v⟫ +
      h.inner (Φ x) (fderiv ℝ (fderiv ℝ Φ) x a u) (fderiv ℝ Φ x v) +
      h.inner (Φ x) (fderiv ℝ Φ x u) (fderiv ℝ (fderiv ℝ Φ) x a v) := by
  let γ : ℝ → E := fun t => x + t • a
  have hγ : HasDerivAt γ a 0 := by
    simpa only [γ,one_smul,zero_add] using!
      (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const a)
  have hγ0 : γ 0 = x := by simp [γ]
  have hdΦ := hΦ.differentiableAt (by norm_num)
  have hddΦ := (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hΦ' : HasFDerivAt Φ (fderiv ℝ Φ x) (γ 0) := by
    simpa only [hγ0] using hdΦ.hasFDerivAt
  have hΦ'' : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) x) (γ 0) := by
    simpa only [hγ0] using hddΦ.hasFDerivAt
  have hΦγ : HasDerivAt (fun t => Φ (γ t)) (fderiv ℝ Φ x a) 0 := by
    simpa only [Function.comp_apply] using! hΦ'.comp_hasDerivAt 0 hγ
  have hU : HasDerivAt (fun t => fderiv ℝ Φ (γ t) u)
      (fderiv ℝ (fderiv ℝ Φ) x a u) 0 := by
    simpa only [hγ0,Function.comp_apply,map_zero,add_zero] using
      (hΦ''.comp_hasDerivAt 0 hγ).clm_apply (hasDerivAt_const 0 u)
  have hV : HasDerivAt (fun t => fderiv ℝ Φ (γ t) v)
      (fderiv ℝ (fderiv ℝ Φ) x a v) 0 := by
    simpa only [hγ0,Function.comp_apply,map_zero,add_zero] using
      (hΦ''.comp_hasDerivAt 0 hγ).clm_apply (hasDerivAt_const 0 v)
  have hleft : HasDerivAt (fun t => g.inner (γ t) u v)
      ⟪fderiv ℝ g.coefficient x a u,v⟫ 0 := by
    simpa only [hγ0,SmoothCoordinateMetric.inner,map_zero,inner_zero_left,inner_zero_right,add_zero] using
      g.hasDerivAt_inner (by simpa only [hγ0] using hx) hγ
        (hasDerivAt_const 0 u) (hasDerivAt_const 0 v)
  have hright := h.hasDerivAt_inner (by simpa only [hγ0] using hy) hΦγ hU hV
  have heq : (fun t => g.inner (γ t) u v) =ᶠ[𝓝 0]
      (fun t => h.inner (Φ (γ t)) (fderiv ℝ Φ (γ t) u) (fderiv ℝ Φ (γ t) v)) := by
    have hm := hγ.continuousAt.tendsto.eventually (by simpa only [hγ0] using hmetric)
    filter_upwards [hm] with t ht
    exact ht u v
  simpa only [hγ0] using hleft.unique (hright.congr_of_eventuallyEq heq)

/-- A C² local isometry intertwines the Levi-Civita connections constructed
from the two metric coefficient fields. -/
theorem local_isometry_christoffel
    (g : SmoothCoordinateMetric E) (h : SmoothCoordinateMetric F)
    {Φ : E → F} {x : E} (hx : x ∈ g.domain) (hy : Φ x ∈ h.domain)
    (hΦ : ContDiffAt ℝ 2 Φ x) (hsurj : Function.Surjective (fderiv ℝ Φ x))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      g.inner y u v = h.inner (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v))
    (u v : E) :
    fderiv ℝ Φ x (g.christoffel x u v) = fderiv ℝ (fderiv ℝ Φ) x u v +
      h.christoffel (Φ x) (fderiv ℝ Φ x u) (fderiv ℝ Φ x v) := by
  apply g.christoffel_transform_of_metric_derivative h hx hy _ hsurj
    (fun a b => fderiv ℝ (fderiv ℝ Φ) x a b)
  · exact hΦ.isSymmSndFDerivAt (by norm_num)
  · exact hmetric.self_of_nhds
  · exact g.local_isometry_metric_derivative h hx hy hΦ hmetric

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
