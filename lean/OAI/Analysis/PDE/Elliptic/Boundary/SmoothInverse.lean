import OAI.Analysis.PDE.Elliptic.Boundary.Flattening
import OAI.Analysis.PDE.Green.LocalExtension

/-! A genuinely smooth inverse chart on a fixed neighborhood.  Smoothness
at the base point alone is not used as a substitute for this assertion. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem exists_smooth_inverse_chart
    (P : E → E) (hP : ContDiff ℝ ∞ P) (x : E) (hPx : P x = 0)
    (hd : HasFDerivAt P (ContinuousLinearMap.id ℝ E) x) :
    ∃ (G : E → E) (R : ℝ) (V : Set E),
      ContDiff ℝ ∞ G ∧ 0 < R ∧ IsOpen V ∧ Bornology.IsBounded V ∧ x ∈ V ∧ G 0 = x ∧
      MapsTo G (ball 0 R) V ∧ MapsTo P V (ball 0 R) ∧
      (∀ y ∈ ball 0 R, P (G y) = y) ∧ (∀ z ∈ V, G (P z) = z) := by
  have hd' : HasFDerivAt P (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) x := hd
  let e := hP.contDiffAt.toOpenPartialHomeomorph P hd' (by simp)
  have hex : x ∈ e.source := hP.contDiffAt.mem_toOpenPartialHomeomorph_source hd' (by simp)
  have he0 : (0 : E) ∈ e.target := by
    simpa only [hPx] using hP.contDiffAt.image_mem_toOpenPartialHomeomorph_target hd' (by simp)
  have ecoe : (e : E → E) = P := rfl
  have heinv : e.symm 0 = x := by
    rw [← hPx]
    exact e.left_inv hex
  have hDP : Continuous (fderiv ℝ P) :=
    (hP.of_le (by simp) : ContDiff ℝ 1 P).continuous_fderiv one_ne_zero
  have hdeq : fderiv ℝ P x = (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) := hd.fderiv
  have hgoodx : {z : E | ∃ L : E ≃L[ℝ] E, (L : E →L[ℝ] E) = fderiv ℝ P z} ∈ 𝓝 x := by
    change (fderiv ℝ P) ⁻¹' {T : E →L[ℝ] E | ∃ L : E ≃L[ℝ] E, (L : E →L[ℝ] E) = T} ∈ 𝓝 x
    apply hDP.continuousAt.preimage_mem_nhds
    rw [hdeq]
    exact (ContinuousLinearEquiv.refl ℝ E).nhds
  have hcont : ContinuousAt e.symm (0 : E) := e.symm.continuousAt he0
  have hgood : ∀ᶠ y in 𝓝 (0 : E), y ∈ e.target ∧
      ∃ L : E ≃L[ℝ] E, (L : E →L[ℝ] E) = fderiv ℝ P (e.symm y) := by
    have hh := hcont.preimage_mem_nhds (by simpa [heinv] using hgoodx)
    exact Filter.Eventually.and (e.open_target.mem_nhds he0) hh
  obtain ⟨ε, hε, heps⟩ := Metric.mem_nhds_iff.mp hgood
  have hF : ContDiffOn ℝ ∞ e.symm (ball 0 ε) := by
    intro y hy
    obtain ⟨hyt, L, hL⟩ := heps hy
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm hyt
    · change HasFDerivAt P (L : E →L[ℝ] E) (e.symm y)
      rw [hL]
      exact (hP.differentiable (by simp) _).hasFDerivAt
    · change ContDiffAt ℝ ∞ P (e.symm y)
      exact hP.contDiffAt
  obtain ⟨χ, hχ, _, hχone, hχzero⟩ := OAI.Analysis.PDE.Green.exists_smooth_cutoff_near_compact
    (isCompact_closedBall (0 : E) (ε / 2)) (isOpen_ball : IsOpen (ball (0 : E) ε))
    (closedBall_subset_ball (by linarith)) (k := ⊤)
  let G : E → E := fun y => χ y • e.symm y
  have hG : ContDiff ℝ ∞ G := OAI.Analysis.PDE.Green.contDiff_cutoff_smul isOpen_ball hχ hχzero hF
  have hGeq (y) (hy : y ∈ closedBall (0 : E) (ε / 2)) : G y = e.symm y := by
    change χ y • e.symm y = e.symm y
    rw [(hχone y hy).eq_of_nhds, one_smul]
  let V : Set E := e.source ∩ P ⁻¹' ball 0 (ε / 2)
  have hV : IsOpen V := e.open_source.inter (isOpen_ball.preimage hP.continuous)
  have hVimage : V ⊆ G '' closedBall 0 (ε / 2) := by
    intro z hz
    refine ⟨P z, ball_subset_closedBall hz.2, ?_⟩
    rw [hGeq _ (ball_subset_closedBall hz.2)]
    exact e.left_inv hz.1
  refine ⟨G, ε / 2, V, hG, by positivity, hV,
    ((isCompact_closedBall (0 : E) (ε / 2)).image hG.continuous).isBounded.subset hVimage,
    ⟨hex, by change P x ∈ ball 0 (ε / 2); rw [hPx]; exact mem_ball_self (by positivity)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hGeq _ (mem_closedBall_self (by positivity)), heinv]
  · intro y hy
    have hyε : y ∈ ball (0 : E) ε := ball_subset_ball (by linarith) hy
    have hyt := (heps hyε).1
    rw [hGeq _ (ball_subset_closedBall hy)]
    refine ⟨e.map_target hyt, ?_⟩
    change P (e.symm y) ∈ ball 0 (ε / 2)
    rw [← ecoe, e.right_inv hyt]
    exact hy
  · exact fun z hz => hz.2
  · intro y hy
    rw [hGeq _ (ball_subset_closedBall hy)]
    exact e.right_inv (heps (ball_subset_ball (by linarith) hy)).1
  · intro z hz
    rw [hGeq _ (ball_subset_closedBall hz.2)]
    exact e.left_inv hz.1

end OAI.Analysis.PDE.Elliptic
