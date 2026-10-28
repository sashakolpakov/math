import OAI.Geometry.Nikodym.GeodesicLinearization

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter Metric
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace LocalGeodesicFlow

variable {g : SmoothCoordinateMetric E} {x₀ : E} (F : LocalGeodesicFlow g x₀)

/-- A nonzero sufficiently short geodesic endpoint map is a genuine
local diffeomorphism at the zero velocity. This is derived from the
variational equation and inverse function theorem. -/
theorem endpoint_local_diffeomorphism {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius)
    (ht0 : t ≠ 0) :
    ∃ e : OpenPartialHomeomorph E E,
      (∀ w, e w = F.position (w,t)) ∧ 0 ∈ e.source ∧ x₀ ∈ e.target ∧
      e.symm x₀ = 0 ∧
      (∀ᶠ w in 𝓝 (0 : E), w ∈ e.source ∧ w ∈ F.velocities ∧
        ContDiffAt ℝ ∞ (e : E → E) w ∧ (fderiv ℝ (e : E → E) w).IsInvertible) ∧
      (∀ᶠ y in 𝓝 x₀, y ∈ e.target ∧ ContDiffAt ℝ ∞ (e.symm : E → E) y) := by
  let L : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E t ht0).toContinuousLinearEquiv
  have hL : (L : E →L[ℝ] E) = t • ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have hc : ContDiffAt ℝ ∞ (fun w => F.position (w,t)) 0 :=
    (F.contDiffAt_state_slice F.zero_mem ht).fst
  have hd : HasFDerivAt (fun w => F.position (w,t)) (L : E →L[ℝ] E) 0 := by
    rw [hL]
    exact F.hasFDerivAt_position_slice_zero ht
  let e := hc.toOpenPartialHomeomorph (fun w => F.position (w,t)) hd (by simp)
  have he : (e : E → E) = fun w => F.position (w,t) := rfl
  have he0 : (0 : E) ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hpos0 : F.position (0,t) = x₀ := congrArg Prod.fst (F.zero_state ht)
  have het : x₀ ∈ e.target := by
    simpa only [hpos0] using hc.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  have hei : e.symm x₀ = 0 := by
    have hh := e.left_inv he0
    simpa only [he,hpos0] using hh
  have hi0 : (fderiv ℝ (e : E → E) 0).IsInvertible := by
    rw [he,hd.fderiv]
    exact ⟨L,rfl⟩
  have hi : ∀ᶠ w in 𝓝 (0 : E), (fderiv ℝ (e : E → E) w).IsInvertible :=
    OAI.Analysis.PDE.Dirichlet.eventually_fderiv_isInvertible (he ▸ hc) hi0
  have hsource : ∀ᶠ w in 𝓝 (0 : E), w ∈ e.source ∧ w ∈ F.velocities ∧
      ContDiffAt ℝ ∞ (e : E → E) w ∧ (fderiv ℝ (e : E → E) w).IsInvertible := by
    filter_upwards [e.open_source.mem_nhds he0,F.isOpen_velocities.mem_nhds F.zero_mem,hi]
      with w hw hv hwi
    refine ⟨hw,hv,?_,hwi⟩
    rw [he]
    exact (F.contDiffAt_state_slice hv ht).fst
  refine ⟨e,fun _ => rfl,he0,het,hei,hsource,?_⟩
  have hcont : Tendsto e.symm (𝓝 x₀) (𝓝 (0 : E)) := by
    simpa only [hei] using (e.symm.continuousAt het).tendsto
  filter_upwards [e.open_target.mem_nhds het,hcont.eventually hsource] with y hy hys
  refine ⟨hy,?_⟩
  obtain ⟨A,hA⟩ := hys.2.2.2
  apply e.contDiffAt_symm hy
  · rw [hA]
    exact (hys.2.2.1.differentiableAt (by simp)).hasFDerivAt
  · exact hys.2.2.1

end LocalGeodesicFlow
end OAI.Geometry.Nikodym
