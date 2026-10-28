import OAI.Geometry.Nikodym.SmoothMetric
import OAI.Geometry.Nikodym.Jacobi.ODE

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open Set
open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (g : SmoothCoordinateMetric E)

omit [FiniteDimensional ℝ E] in
/-- The derivative of the metric pairing along an actual differentiable curve. -/
theorem hasDerivAt_inner {γ U V : ℝ → E} {t : ℝ} {w u v : E}
    (ht : γ t ∈ g.domain) (hγ : HasDerivAt γ w t)
    (hU : HasDerivAt U u t) (hV : HasDerivAt V v t) :
    HasDerivAt (fun s => g.inner (γ s) (U s) (V s))
      (⟪fderiv ℝ g.coefficient (γ t) w (U t),V t⟫ +
        g.inner (γ t) u (V t) + g.inner (γ t) (U t) v) t := by
  have hc := ((g.smooth (γ t) ht).contDiffAt
    (g.isOpen_domain.mem_nhds ht)).differentiableAt (by simp)
  have hd := ((hc.hasFDerivAt.comp_hasDerivAt t hγ).clm_apply hU).inner ℝ hV
  convert hd using 1
  · rfl
  · simp only [SmoothCoordinateMetric.inner,inner_add_left,Function.comp_apply]
    ring

/-- Metric compatibility in covariant-derivative form, proved from the
constructed Christoffel symbols and the ordinary chain rule. -/
theorem hasDerivAt_inner_covariant {γ U V : ℝ → E} {t : ℝ} {w u v : E}
    (ht : γ t ∈ g.domain) (hγ : HasDerivAt γ w t)
    (hU : HasDerivAt U u t) (hV : HasDerivAt V v t) :
    HasDerivAt (fun s => g.inner (γ s) (U s) (V s))
      (g.inner (γ t) (u + g.christoffel (γ t) w (U t)) (V t) +
        g.inner (γ t) (U t) (v + g.christoffel (γ t) w (V t))) t := by
  convert g.hasDerivAt_inner ht hγ hU hV using 1
  have hh := g.christoffel_compatible ht w (U t) (V t)
  simp only [SmoothCoordinateMetric.inner,map_add,inner_add_left,inner_add_right] at hh ⊢
  linarith

theorem hasDerivAt_inner_parallel {γ U V : ℝ → E} {t : ℝ} {w : E}
    (ht : γ t ∈ g.domain) (hγ : HasDerivAt γ w t)
    (hU : HasDerivAt U (-g.christoffel (γ t) w (U t)) t)
    (hV : HasDerivAt V (-g.christoffel (γ t) w (V t)) t) :
    HasDerivAt (fun s => g.inner (γ s) (U s) (V s)) 0 t := by
  simpa only [neg_add_cancel,SmoothCoordinateMetric.inner,map_zero,inner_zero_left,inner_zero_right,add_zero] using
    g.hasDerivAt_inner_covariant ht hγ hU hV

/-- Parallel transport preserves the metric on every real interval. -/
theorem parallel_inner_eq {S : Set ℝ} (hS : Convex ℝ S)
    {γ w U V : ℝ → E}
    (hγdom : ∀ t ∈ S, γ t ∈ g.domain)
    (hγ : ∀ t ∈ S, HasDerivAt γ (w t) t)
    (hU : ∀ t ∈ S, HasDerivAt U (-g.christoffel (γ t) (w t) (U t)) t)
    (hV : ∀ t ∈ S, HasDerivAt V (-g.christoffel (γ t) (w t) (V t)) t)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) :
    g.inner (γ b) (U b) (V b) = g.inner (γ a) (U a) (V a) :=
  eq_of_hasDerivAt_zero_on_convex hS
    (fun t ht => g.hasDerivAt_inner_parallel (hγdom t ht) (hγ t ht) (hU t ht) (hV t ht)) ha hb

/-- Constant speed is a consequence of the actual geodesic ODE. -/
theorem geodesic_speed_sq_eq {S : Set ℝ} (hS : Convex ℝ S)
    {γ w : ℝ → E}
    (hγdom : ∀ t ∈ S, γ t ∈ g.domain)
    (hγ : ∀ t ∈ S, HasDerivAt γ (w t) t)
    (hw : ∀ t ∈ S, HasDerivAt w (-g.christoffel (γ t) (w t) (w t)) t)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) :
    g.inner (γ b) (w b) (w b) = g.inner (γ a) (w a) (w a) :=
  g.parallel_inner_eq hS hγdom hγ hw hw ha hb

theorem parallel_nonzero {S : Set ℝ} (hS : Convex ℝ S)
    {γ w U : ℝ → E}
    (hγdom : ∀ t ∈ S, γ t ∈ g.domain)
    (hγ : ∀ t ∈ S, HasDerivAt γ (w t) t)
    (hU : ∀ t ∈ S, HasDerivAt U (-g.christoffel (γ t) (w t) (U t)) t)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hUa : U a ≠ 0) : U b ≠ 0 := by
  have he := g.parallel_inner_eq hS hγdom hγ hU hU ha hb
  have hp := g.positive (γ a) (hγdom a ha) (U a) hUa
  intro hz
  simp only [hz,SmoothCoordinateMetric.inner,map_zero,inner_zero_left] at he
  linarith

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
