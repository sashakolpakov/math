import OAI.Geometry.Nikodym.GeodesicFlow
import OAI.Geometry.Nikodym.SprayDerivative
import OAI.Geometry.Nikodym.Jacobi.ODE
import OAI.Analysis.ODE.SmoothFlow.Variation

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem stationary_spray_variation_solution {I : Set ℝ} (hI : Convex ℝ I)
    (h0 : 0 ∈ I) {J : ℝ → E × E} (hJ : ∀ t ∈ I, HasDerivAt J ((J t).2,0) t)
    {w : E} (hJ0 : J 0 = (0,w)) {t : ℝ} (ht : t ∈ I) : J t = (t • w,w) := by
  have hp (s : ℝ) (hs : s ∈ I) : HasDerivAt (fun r => (J r).1) (J s).2 s := (hJ s hs).fst
  have hv (s : ℝ) (hs : s ∈ I) : HasDerivAt (fun r => (J r).2) ((-(0 : ℝ)) • (J s).1) s := by
    have hd : HasDerivAt (fun r => (J r).2) (0 : E) s := (hJ s hs).snd
    simpa only [neg_zero,zero_smul] using hd
  have hh := constant_curvature_ode_solution hI h0 0 hp hv ht
  apply Prod.ext
  · simpa only [hJ0,curvatureCos_flat,curvatureSin_flat,one_smul,zero_add] using hh.1
  · simpa only [hJ0,curvatureCos_flat,curvatureSin_flat,neg_zero,zero_mul,zero_smul,
      one_smul,zero_add] using hh.2

namespace LocalGeodesicFlow

variable {g : SmoothCoordinateMetric E} {x₀ : E} (F : LocalGeodesicFlow g x₀)

def stateVariation (w u : E) (t : ℝ) : E × E :=
  fderiv ℝ (fun v => F.state (v,t)) w u

theorem stateVariation_initial {w : E} (hw : w ∈ F.velocities) (u : E) :
    F.stateVariation w u 0 = (0,u) := by
  have he : (fun v => F.state (v,0)) =ᶠ[𝓝 w] (fun v => (x₀,v)) := by
    filter_upwards [F.isOpen_velocities.mem_nhds hw] with v hv
    exact F.initial v hv
  have hd := (hasFDerivAt_const (𝕜 := ℝ) x₀ w).prodMk (hasFDerivAt_id (𝕜 := ℝ) w)
  have hh := he.fderiv_eq.trans hd.fderiv
  exact congrArg (fun L : E →L[ℝ] E × E => L u) hh

theorem stateVariation_derivative {w : E} (hw : w ∈ F.velocities) (u : E)
    {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius) :
    HasDerivAt (F.stateVariation w u)
      (fderiv ℝ g.geodesicSpray (F.state (w,t)) (F.stateVariation w u t)) t := by
  apply OAI.Analysis.ODE.SmoothFlow.flow_parameter_variation F.isOpen_velocities isOpen_Ioo
    (F.smooth.of_le (by simp)) _ _ hw u ht
  · intro z hz s hs
    exact (g.contDiffAt_geodesicSpray ((F.geodesic z hz).regular s hs)).differentiableAt (by simp)
  · intro z hz s hs
    exact (F.geodesic z hz).spray s hs

theorem stateVariation_zero (u : E) {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius) :
    F.stateVariation 0 u t = (t • u,u) := by
  have h0 : (0 : ℝ) ∈ Ioo (-F.radius) F.radius := ⟨neg_neg_of_pos F.radius_pos,F.radius_pos⟩
  have hx : x₀ ∈ g.domain := by
    simpa only [F.initial 0 F.zero_mem] using (F.geodesic 0 F.zero_mem).regular 0 h0
  apply stationary_spray_variation_solution (convex_Ioo _ _) h0 _
    (F.stateVariation_initial F.zero_mem u) ht
  intro s hs
  have hd := F.stateVariation_derivative F.zero_mem u hs
  rw [F.zero_state hs,g.fderiv_geodesicSpray_zero hx] at hd
  exact hd

theorem contDiffAt_state_slice {w : E} (hw : w ∈ F.velocities)
    {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius) :
    ContDiffAt ℝ ∞ (fun v => F.state (v,t)) w :=
  ((F.smooth (w,t) ⟨hw,ht⟩).contDiffAt
    ((F.isOpen_velocities.prod isOpen_Ioo).mem_nhds ⟨hw,ht⟩)).comp w
      (contDiffAt_id.prodMk contDiffAt_const)

theorem hasFDerivAt_position_slice_zero {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius) :
    HasFDerivAt (fun v => F.position (v,t))
      (t • ContinuousLinearMap.id ℝ E) 0 := by
  have hd := ((F.contDiffAt_state_slice F.zero_mem ht).differentiableAt (by simp)).hasFDerivAt.fst
  convert hd using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro u
    change t • u = (F.stateVariation 0 u t).1
    rw [F.stateVariation_zero u ht]

end LocalGeodesicFlow
end OAI.Geometry.Nikodym
