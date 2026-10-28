import OAI.Geometry.Nikodym.NormalEndpoint
import OAI.Geometry.Nikodym.ExponentialChart

noncomputable section
namespace OAI.Geometry.Nikodym.LocalGeodesicFlow

open Set Filter Metric
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {g : SmoothCoordinateMetric E} {x₀ : E} (F : LocalGeodesicFlow g x₀)

theorem normalizedEndpoint_zero (R : E ≃L[ℝ] E) {t : ℝ}
    (ht : t ∈ Ioo (-F.radius) F.radius) : F.normalizedEndpoint R t 0 = x₀ := by
  simpa only [LocalGeodesicFlow.normalizedEndpoint,map_zero,smul_zero,LocalGeodesicFlow.position] using
    congrArg Prod.fst (F.zero_state ht)

theorem hasFDerivAt_normalizedEndpoint_zero (R : E ≃L[ℝ] E) {t : ℝ}
    (ht : t ∈ Ioo (-F.radius) F.radius) (ht0 : t ≠ 0) :
    HasFDerivAt (F.normalizedEndpoint R t) (R.symm : E →L[ℝ] E) 0 := by
  have hc := F.contDiffAt_normalizedEndpoint R ht (ξ := 0) (by simpa using F.zero_mem)
  have hd := (hc.differentiableAt (by simp)).hasFDerivAt
  convert hd using 1
  apply ContinuousLinearMap.ext
  intro w
  rw [F.fderiv_normalizedEndpoint R ht (by simpa using F.zero_mem),map_zero,smul_zero,
    (F.hasFDerivAt_position_slice_zero ht).fderiv]
  simp [smul_smul,ht0]

/-- A true normal coordinate chart with smooth inverse on a common
neighborhood, obtained from the actual geodesic flow. -/
theorem normalizedEndpoint_local_diffeomorphism (R : E ≃L[ℝ] E) {t : ℝ}
    (ht : t ∈ Ioo (-F.radius) F.radius) (ht0 : t ≠ 0) :
    ∃ e : OpenPartialHomeomorph E E,
      (∀ w, e w = F.normalizedEndpoint R t w) ∧ 0 ∈ e.source ∧ x₀ ∈ e.target ∧
      e.symm x₀ = 0 ∧
      (∀ᶠ w in 𝓝 (0 : E), w ∈ e.source ∧ t⁻¹ • R.symm w ∈ F.velocities ∧
        ContDiffAt ℝ ∞ (e : E → E) w ∧ (fderiv ℝ (e : E → E) w).IsInvertible) ∧
      (∀ᶠ y in 𝓝 x₀, y ∈ e.target ∧ ContDiffAt ℝ ∞ (e.symm : E → E) y) := by
  have hvel : ∀ᶠ w in 𝓝 (0 : E), t⁻¹ • R.symm w ∈ F.velocities := by
    exact ((R.symm.continuous.const_smul t⁻¹).continuousAt.tendsto).eventually
      (by simpa using F.isOpen_velocities.mem_nhds F.zero_mem)
  have hc := F.contDiffAt_normalizedEndpoint R ht (ξ := 0) (by simpa using F.zero_mem)
  have hd := F.hasFDerivAt_normalizedEndpoint_zero R ht ht0
  let e := hc.toOpenPartialHomeomorph (F.normalizedEndpoint R t) hd (by simp)
  have he : (e : E → E) = F.normalizedEndpoint R t := rfl
  have he0 : (0 : E) ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hpos0 := F.normalizedEndpoint_zero R ht
  have het : x₀ ∈ e.target := by
    simpa only [hpos0] using hc.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  have hei : e.symm x₀ = 0 := by
    simpa only [he,hpos0] using e.left_inv he0
  have hi0 : (fderiv ℝ (e : E → E) 0).IsInvertible := by
    rw [he,hd.fderiv]
    exact ⟨R.symm,rfl⟩
  have hi := OAI.Analysis.PDE.Dirichlet.eventually_fderiv_isInvertible (he ▸ hc) hi0
  have hsource : ∀ᶠ w in 𝓝 (0 : E), w ∈ e.source ∧ t⁻¹ • R.symm w ∈ F.velocities ∧
      ContDiffAt ℝ ∞ (e : E → E) w ∧ (fderiv ℝ (e : E → E) w).IsInvertible := by
    filter_upwards [e.open_source.mem_nhds he0,hvel,hi] with w hw hv hwi
    exact ⟨hw,hv,he ▸ F.contDiffAt_normalizedEndpoint R ht hv,hwi⟩
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

end OAI.Geometry.Nikodym.LocalGeodesicFlow
