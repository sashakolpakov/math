import OAI.Geometry.Nikodym.MetricCurvature
import OAI.Geometry.Nikodym.ParallelMetric

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Affine geodesics of the actual metric, expressed in coordinates. -/
structure IsMetricGeodesic (g : SmoothCoordinateMetric E)
    (γ v : ℝ → E) (I : Set ℝ) : Prop where
  position_derivative : ∀ t ∈ I, HasDerivAt γ (v t) t
  velocity_derivative : ∀ t ∈ I,
    HasDerivAt v (-g.christoffel (γ t) (v t) (v t)) t
  regular : ∀ t ∈ I, γ t ∈ g.domain

namespace IsMetricGeodesic

variable {g : SmoothCoordinateMetric E} {γ v : ℝ → E} {I : Set ℝ}

theorem of_spray {c : ℝ → E × E}
    (hc : ∀ t ∈ I, HasDerivAt c (g.geodesicSpray (c t)) t)
    (hdom : ∀ t ∈ I, (c t).1 ∈ g.domain) :
    IsMetricGeodesic g (fun t => (c t).1) (fun t => (c t).2) I := by
  refine ⟨?_,?_,hdom⟩
  · intro t ht
    exact (hc t ht).fst
  · intro t ht
    exact (hc t ht).snd

theorem spray (h : IsMetricGeodesic g γ v I) :
    ∀ t ∈ I, HasDerivAt (fun s => (γ s,v s))
      (g.geodesicSpray (γ t,v t)) t := by
  intro t ht
  exact (h.position_derivative t ht).prodMk (h.velocity_derivative t ht)

theorem stationary {x : E} (hx : x ∈ g.domain) :
    IsMetricGeodesic g (fun _ => x) (fun _ => 0) I := by
  refine ⟨fun t _ => hasDerivAt_const t x,?_,fun _ _ => hx⟩
  intro t _
  simpa using (hasDerivAt_const t (0 : E))

theorem mono (h : IsMetricGeodesic g γ v I) {J : Set ℝ} (hJI : J ⊆ I) :
    IsMetricGeodesic g γ v J :=
  ⟨fun t ht => h.position_derivative t (hJI ht),
    fun t ht => h.velocity_derivative t (hJI ht),fun t ht => h.regular t (hJI ht)⟩

/-- Affine changes of time preserve the actual geodesic equation; the
quadratic scaling of the constructed Christoffel expression is proved. -/
theorem affine_reparam (h : IsMetricGeodesic g γ v I) (a b : ℝ) :
    IsMetricGeodesic g (fun t => γ (a*t+b)) (fun t => a • v (a*t+b))
      {t | a*t+b ∈ I} := by
  refine ⟨?_,?_,fun t ht => h.regular _ ht⟩
  · intro t ht
    have hd : HasDerivAt (fun s : ℝ => a*s+b) a t := by
      simpa using ((hasDerivAt_id t).const_mul a).add_const b
    simpa only [Function.comp_def] using (h.position_derivative _ ht).scomp t hd
  · intro t ht
    have hd : HasDerivAt (fun s : ℝ => a*s+b) a t := by
      simpa using ((hasDerivAt_id t).const_mul a).add_const b
    have hv := ((h.velocity_derivative _ ht).scomp t hd).const_smul a
    change HasDerivAt (fun s => a • v (a*s+b))
      (a • (a • (-g.christoffel (γ (a*t+b)) (v (a*t+b)) (v (a*t+b))))) t at hv
    simpa only [g.christoffel_smul_self,smul_neg,smul_smul,pow_two,
      Function.comp_def,Pi.smul_apply] using hv

theorem speed_sq_eq (h : IsMetricGeodesic g γ v I) (hI : Convex ℝ I)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    g.inner (γ b) (v b) (v b) = g.inner (γ a) (v a) (v a) :=
  g.geodesic_speed_sq_eq hI h.regular h.position_derivative h.velocity_derivative ha hb

theorem stationary_of_velocity_zero (h : IsMetricGeodesic g γ v I)
    (hI : Convex ℝ I) {a : ℝ} (ha : a ∈ I) (hva : v a = 0)
    {t : ℝ} (ht : t ∈ I) : γ t = γ a ∧ v t = 0 := by
  have hv (s : ℝ) (hs : s ∈ I) : v s = 0 := by
    by_contra hn
    have he := h.speed_sq_eq hI ha hs
    have hp := g.positive (γ s) (h.regular s hs) (v s) hn
    simp only [hva,OAI.Geometry.Nikodym.SmoothCoordinateMetric.inner,map_zero,inner_zero_left] at he
    exact hp.ne' he
  refine ⟨?_,hv t ht⟩
  exact eq_of_hasDerivAt_zero_on_convex hI
    (fun s hs => by simpa only [hv s hs] using h.position_derivative s hs) ha ht

end IsMetricGeodesic
end OAI.Geometry.Nikodym
