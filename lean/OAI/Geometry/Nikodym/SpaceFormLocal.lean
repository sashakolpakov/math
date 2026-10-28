import OAI.Geometry.Nikodym.NormalChart
import OAI.Geometry.Nikodym.Jacobi.RadialChart

noncomputable section
namespace OAI.Geometry.Nikodym.LocalGeodesicFlow

open Set Filter Metric
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {g : SmoothCoordinateMetric E} {x₀ : E} (F : LocalGeodesicFlow g x₀)

theorem inverse_normal_metric {κ : ℝ} (hκ : g.HasConstantCurvature κ)
    (R : E ≃L[ℝ] E) (hR : ∀ u v, g.inner x₀ u v = inner ℝ (R u) (R v))
    {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius) (ht0 : 0 < t)
    (e : OpenPartialHomeomorph E E) (he : (e : E → E) = F.normalizedEndpoint R t)
    {y : E} (hy : y ∈ e.target) (hvel : t⁻¹ • R.symm (e.symm y) ∈ F.velocities)
    (hi : ContDiffAt ℝ ∞ (e.symm : E → E) y)
    (hcos : curvatureCos κ ‖e.symm y‖ ≠ 0) (u v : E) :
    g.inner y u v = beltramiMetric κ (projectiveRadialMap κ (e.symm y))
      (fderiv ℝ (fun z => projectiveRadialMap κ (e.symm z)) y u)
      (fderiv ℝ (fun z => projectiveRadialMap κ (e.symm z)) y v) := by
  have hec : ContDiffAt ℝ ∞ (e : E → E) (e.symm y) :=
    he ▸ F.contDiffAt_normalizedEndpoint R ht hvel
  have hd := (hec.differentiableAt (by simp)).hasFDerivAt.comp y
    (hi.differentiableAt (by simp)).hasFDerivAt
  have hid : (fun z => e (e.symm z)) =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  have hc := hd.congr_of_eventuallyEq hid.symm
  have hder := hc.unique (hasFDerivAt_id y)
  have happly (w : E) : fderiv ℝ (e : E → E) (e.symm y)
      (fderiv ℝ (e.symm : E → E) y w) = w :=
    congrArg (fun L : E →L[ℝ] E => L w) hder
  have hp := (contDiffAt_projectiveRadialMap_center_included κ hcos).differentiableAt (by simp)
  have hpc : HasFDerivAt (fun z => projectiveRadialMap κ (e.symm z))
      ((fderiv ℝ (projectiveRadialMap κ) (e.symm y)).comp
        (fderiv ℝ (e.symm : E → E) y)) y :=
    hp.hasFDerivAt.comp y (hi.differentiableAt (by simp)).hasFDerivAt
  have hm := F.normalizedEndpoint_beltrami_metric hκ R hR ht ht0 hvel hcos
    (fderiv ℝ (e.symm : E → E) y u) (fderiv ℝ (e.symm : E → E) y v)
  rw [← he,e.right_inv hy,happly u,happly v] at hm
  simpa only [hpc.fderiv,ContinuousLinearMap.comp_apply] using hm

include F in
/-- Actual local Beltrami coordinates for a smooth constant-curvature metric.
Both inverse identities and the metric identity are conclusions. -/
theorem exists_local_beltrami_maps {κ : ℝ} (hκ : g.HasConstantCurvature κ)
    (R : E ≃L[ℝ] E) (hR : ∀ u v, g.inner x₀ u v = inner ℝ (R u) (R v))
    (hx₀ : x₀ ∈ g.domain) :
    ∃ φ ψ : E → E, φ x₀ = 0 ∧ ψ 0 = x₀ ∧
      (∀ᶠ y in 𝓝 x₀, y ∈ g.domain ∧ ContDiffAt ℝ ∞ φ y ∧ ψ (φ y) = y ∧
        0 < beltramiDenominator κ (φ y) ∧
        ∀ u v, g.inner y u v = beltramiMetric κ (φ y)
          (fderiv ℝ φ y u) (fderiv ℝ φ y v)) ∧
      (∀ᶠ z in 𝓝 (0 : E), ContDiffAt ℝ ∞ ψ z ∧ φ (ψ z) = z) := by
  let t := F.radius/2
  have ht0 : 0 < t := half_pos F.radius_pos
  have ht : t ∈ Ioo (-F.radius) F.radius := by constructor <;> dsimp [t] <;> linarith [F.radius_pos]
  obtain ⟨e,he,he0,het,hei,hsource,hinverse⟩ := F.normalizedEndpoint_local_diffeomorphism R ht ht0.ne'
  have hefun : (e : E → E) = F.normalizedEndpoint R t := funext he
  have hebase : e 0 = x₀ := (he 0).trans (F.normalizedEndpoint_zero R ht)
  obtain ⟨r,G,hr,hG0,hGs,hPG,hGP⟩ := projectiveRadialMap_smooth_local_inverse (E := E) κ
  let φ : E → E := fun y => projectiveRadialMap κ (e.symm y)
  let ψ : E → E := fun z => e (G z)
  have hφ0 : φ x₀ = 0 := by simp only [φ,hei,projectiveRadialMap_zero]
  have hψ0 : ψ 0 = x₀ := by simp only [ψ,hG0,hebase]
  have hcos : ∀ᶠ x : E in 𝓝 0, curvatureCos κ ‖x‖ ≠ 0 :=
    ((contDiff_curvatureCos κ).continuous.continuousAt.comp continuous_norm.continuousAt).eventually_ne (by simp)
  have hEi : Tendsto e.symm (𝓝 x₀) (𝓝 (0 : E)) := by
    simpa only [hei] using (e.symm.continuousAt het).tendsto
  have hGcont : Tendsto G (𝓝 (0 : E)) (𝓝 (0 : E)) := by
    simpa only [hG0] using ((hGs 0 (mem_ball_self hr)).contDiffAt
      (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousAt.tendsto
  refine ⟨φ,ψ,hφ0,hψ0,?_,?_⟩
  · filter_upwards [g.isOpen_domain.mem_nhds hx₀,hinverse,hEi.eventually hsource,
      hEi.eventually hcos,hEi.eventually hGP] with y hyd hy hs hcy hgyi
    have hsmooth : ContDiffAt ℝ ∞ φ y :=
      (contDiffAt_projectiveRadialMap_center_included κ hcy).comp y hy.2
    have hinv : ψ (φ y) = y := by
      dsimp only [ψ,φ]
      rw [hgyi,e.right_inv hy.1]
    have hpositive : 0 < beltramiDenominator κ (φ y) := by
      change 0 < beltramiDenominator κ (projectiveRadialMap κ (e.symm y))
      rw [beltramiDenominator_projectiveRadialMap κ _ hcy]
      exact one_div_pos.mpr (sq_pos_of_ne_zero hcy)
    exact ⟨hyd,hsmooth,hinv,hpositive,
      F.inverse_normal_metric hκ R hR ht ht0 e hefun hy.1 hs.2.1 hy.2 hcy⟩
  · filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr),hGcont.eventually hsource]
      with z hz hs
    have hg : ContDiffAt ℝ ∞ G z := (hGs z hz).contDiffAt (isOpen_ball.mem_nhds hz)
    refine ⟨hs.2.2.1.comp z hg,?_⟩
    dsimp only [φ,ψ]
    rw [e.left_inv hs.1,hPG z hz]

end OAI.Geometry.Nikodym.LocalGeodesicFlow
