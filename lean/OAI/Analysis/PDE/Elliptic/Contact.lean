import OAI.Analysis.PDE.Dirichlet.Maximum

open Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Small linear tilts of a negative interior well touch the graph from
below at an interior point. This is the geometric step in the ABP estimate. -/
theorem exists_support_point_of_small_tilt {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContinuousOn f K) {x₀ : E} (hx₀ : x₀ ∈ K)
    (_hnegative : f x₀ < 0) (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    {R : ℝ} (_hR : 0 < R) (hradius : ∀ x ∈ K, ‖x - x₀‖ ≤ R)
    (l : E →L[ℝ] ℝ) (hl : ‖l‖ * R < -f x₀) :
    ∃ y ∈ interior K, ∀ z ∈ K, f y + l (z - y) ≤ f z := by
  let g : E → ℝ := fun x ↦ f x - l (x - x₀)
  have hg : ContinuousOn g K := hf.sub (l.continuous.comp (continuous_id.sub continuous_const)).continuousOn
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn ⟨x₀, hx₀⟩ hg
  have hyi : y ∈ interior K := by
    by_contra hyn
    have hb := hboundary y hy hyn
    have hmy : f y - l (y - x₀) ≤ f x₀ := by
      have h : g y ≤ g x₀ := hmin hx₀
      simpa only [g, sub_self, map_zero, sub_zero] using h
    have hly : l (y - x₀) ≤ ‖l‖ * R :=
      (le_abs_self _).trans ((l.le_opNorm (y - x₀)).trans
        (mul_le_mul_of_nonneg_left (hradius y hy) (norm_nonneg l)))
    linarith
  refine ⟨y, hyi, ?_⟩
  intro z hz
  have h : f y - l (y - x₀) ≤ f z - l (z - x₀) := hmin hz
  simp only [map_sub] at h ⊢
  linarith

/-- At a differentiable supporting point, the supporting slope is the
actual Fréchet derivative. -/
theorem fderiv_eq_of_support {K : Set E} {f : E → ℝ} {y : E}
    (hy : y ∈ interior K) (hf : DifferentiableAt ℝ f y) (l : E →L[ℝ] ℝ)
    (hsupport : ∀ z ∈ K, f y + l (z - y) ≤ f z) : fderiv ℝ f y = l := by
  have hmin : IsLocalMin (fun z ↦ f z - l z) y := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hy] with z hz
    have h := hsupport z hz
    rw [map_sub] at h
    linarith
  have hd := hf.hasFDerivAt.sub l.hasFDerivAt
  have hz : fderiv ℝ f y - l = 0 := hd.fderiv.symm.trans hmin.fderiv_eq_zero
  exact sub_eq_zero.mp hz

/-- Interior points admitting their own tangent plane as a global lower
support over `K`. -/
def lowerContactSet (K : Set E) (f : E → ℝ) : Set E :=
  {y | y ∈ interior K ∧ ∀ z ∈ K, f y + fderiv ℝ f y (z - y) ≤ f z}

/-- A lower supporting plane forces positivity of the actual Hessian. -/
theorem hessian_nonneg_of_mem_lowerContactSet {K : Set E} {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) {y : E} (hy : y ∈ lowerContactSet K f) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) y v v := by
  let l := fderiv ℝ f y
  have hmax : IsLocalMax (fun z ↦ l z - f z) y := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hy.1] with z hz
    have h := hy.2 z hz
    change f y + l (z - y) ≤ f z at h
    rw [map_sub] at h
    linarith
  have hf₁ := hf.differentiable (by norm_num)
  have hf₂ := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hD : fderiv ℝ (fun z ↦ l z - f z) = fun z ↦ l - fderiv ℝ f z := by
    funext z
    exact (l.hasFDerivAt.sub (hf₁ z).hasFDerivAt).fderiv
  have hD₂ : fderiv ℝ (fun z ↦ l - fderiv ℝ f z) y = -fderiv ℝ (fderiv ℝ f) y := by
    have hd : HasFDerivAt (fun z ↦ l - fderiv ℝ f z)
        (0 - fderiv ℝ (fderiv ℝ f) y) y :=
      (hasFDerivAt_const l y).sub (hf₂ y).hasFDerivAt
    simpa only [zero_sub] using hd.fderiv
  have h := OAI.Analysis.PDE.Dirichlet.hessian_nonpos_of_localMax (l.contDiff.sub hf) hmax v
  rw [hD, hD₂] at h
  simpa using h

/-- The global lower supporting-plane condition is closed. -/
theorem isClosed_supporting_tangent_set {K : Set E} {f : E → ℝ}
    (hf : Continuous f) (hDf : Continuous (fderiv ℝ f)) :
    IsClosed {y | ∀ z ∈ K, f y + fderiv ℝ f y (z - y) ≤ f z} := by
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro z
  apply isClosed_iInter
  intro _
  exact isClosed_le (hf.add (hDf.clm_apply (continuous_const.sub continuous_id))) continuous_const

/-- The derivative image of the lower contact set covers a whole dual ball.
This is a genuine measure-ready slope-image inclusion, not an assumed
maximum-principle or regularity estimate. -/
theorem ball_subset_fderiv_image_lowerContactSet {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : Differentiable ℝ f) {x₀ : E} (hx₀ : x₀ ∈ K)
    (hnegative : f x₀ < 0) (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    {R : ℝ} (hR : 0 < R) (hradius : ∀ x ∈ K, ‖x - x₀‖ ≤ R) :
    Metric.ball (0 : E →L[ℝ] ℝ) (-f x₀ / R) ⊆ fderiv ℝ f '' lowerContactSet K f := by
  intro l hl
  have hl' : ‖l‖ * R < -f x₀ := (lt_div_iff₀ hR).mp (by simpa using hl)
  obtain ⟨y, hy, hsupport⟩ := exists_support_point_of_small_tilt hK hf.continuous.continuousOn
    hx₀ hnegative hboundary hR hradius l hl'
  have heq := fderiv_eq_of_support hy (hf y) l hsupport
  exact ⟨y, ⟨hy, by simpa only [heq] using hsupport⟩, heq⟩

end OAI.Analysis.PDE.Elliptic
