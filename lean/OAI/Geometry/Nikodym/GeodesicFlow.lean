import OAI.Geometry.Nikodym.MetricGeodesic
import OAI.Analysis.ODE.SmoothFlow.Local

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A common smooth family of genuine metric geodesics, with fixed base
point and varying initial velocity. It is constructed below from the
actual smooth spray, not assumed as part of a metric. -/
structure LocalGeodesicFlow (g : SmoothCoordinateMetric E) (x₀ : E) where
  radius : ℝ
  radius_pos : 0 < radius
  velocities : Set E
  isOpen_velocities : IsOpen velocities
  zero_mem : (0 : E) ∈ velocities
  state : E × ℝ → E × E
  smooth : ContDiffOn ℝ ∞ state (velocities ×ˢ Ioo (-radius) radius)
  initial : ∀ w ∈ velocities, state (w,0) = (x₀,w)
  geodesic : ∀ w ∈ velocities, IsMetricGeodesic g
    (fun t => (state (w,t)).1) (fun t => (state (w,t)).2) (Ioo (-radius) radius)

theorem exists_localGeodesicFlow (g : SmoothCoordinateMetric E) {x₀ : E}
    (hx₀ : x₀ ∈ g.domain) : Nonempty (LocalGeodesicFlow g x₀) := by
  let U : Set (E × E) := {p | p.1 ∈ g.domain}
  have hU : IsOpen U := g.isOpen_domain.preimage continuous_fst
  have hs : ContDiffOn ℝ ∞ g.geodesicSpray U := by
    intro p hp
    exact (g.contDiffAt_geodesicSpray hp).contDiffWithinAt
  obtain ⟨ε,hε,V,Φ,hV,hV0,hVU,hΦ,hinit,hmaps,hode⟩ :=
    OAI.Analysis.ODE.SmoothFlow.exists_smooth_local_flow hU g.geodesicSpray hs (show (x₀,0) ∈ U from hx₀)
  let W : Set E := {w | (x₀,w) ∈ V}
  have hW : IsOpen W := hV.preimage (continuous_const.prodMk continuous_id)
  refine ⟨⟨ε,hε,W,hW,hV0,fun p => Φ ((x₀,p.1),p.2),?_,?_,?_⟩⟩
  · apply hΦ.comp (by fun_prop)
    intro p hp
    exact ⟨hp.1,hp.2⟩
  · intro w hw
    exact hinit (x₀,w) hw
  · intro w hw
    apply OAI.Geometry.Nikodym.IsMetricGeodesic.of_spray
    · intro t ht
      exact hode (x₀,w) hw t ht
    · intro t ht
      exact hmaps ⟨hw,ht⟩

namespace LocalGeodesicFlow

variable {g : SmoothCoordinateMetric E} {x₀ : E} (F : LocalGeodesicFlow g x₀)

theorem zero_state {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius) :
    F.state (0,t) = (x₀,0) := by
  have h0 : (0 : ℝ) ∈ Ioo (-F.radius) F.radius := ⟨neg_neg_of_pos F.radius_pos,F.radius_pos⟩
  have h := (F.geodesic 0 F.zero_mem).stationary_of_velocity_zero (convex_Ioo _ _)
    h0 (by simp only [F.initial 0 F.zero_mem]) ht
  apply Prod.ext
  · simpa only [F.initial 0 F.zero_mem] using h.1
  · exact h.2

def position : E × ℝ → E := fun p => (F.state p).1
def velocity : E × ℝ → E := fun p => (F.state p).2

theorem smooth_position : ContDiffOn ℝ ∞ F.position
    (F.velocities ×ˢ Ioo (-F.radius) F.radius) := F.smooth.fst

theorem smooth_velocity : ContDiffOn ℝ ∞ F.velocity
    (F.velocities ×ˢ Ioo (-F.radius) F.radius) := F.smooth.snd

end LocalGeodesicFlow
end OAI.Geometry.Nikodym
