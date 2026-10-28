import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.SmoothShift

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

namespace ParameterDeformation

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace Z] [CompleteSpace E] in
theorem fderiv_slice_right {h : Z × E → E} (hh : Differentiable ℝ h) (t : Z) (x : E) :
    fderiv ℝ (fun y ↦ h (t, y)) x =
      (fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inr ℝ Z E) := by
  have hi : HasFDerivAt (fun y : E ↦ (t, y)) (ContinuousLinearMap.inr ℝ Z E) x := by
    change HasFDerivAt (fun y : E ↦ (t, y))
      ((0 : E →L[ℝ] Z).prod (ContinuousLinearMap.id ℝ E)) x
    simpa only [id_eq] using (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  exact ((hh (t, x)).hasFDerivAt.comp x hi).fderiv

omit [CompleteSpace Z] [CompleteSpace E] in
/-- Compact spatial support makes the smallness of the derivative uniform in
space. The parameter dependence is genuinely joint, not pointwise. -/
theorem eventually_uniform_fderiv_small
    {h : Z × E → E} (hh : ContDiff ℝ ∞ h) {K : Set E} (hK : IsCompact K)
    (hs : ∀ t x, x ∉ K → h (t, x) = 0) (hzero : ∀ x, h (0, x) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0 : Z), ∀ x, ‖fderiv ℝ (fun y ↦ h (t, y)) x‖ < ε := by
  let D : Z × E → E →L[ℝ] E := fun p ↦
    (fderiv ℝ h p).comp (ContinuousLinearMap.inr ℝ Z E)
  have hD : Continuous D :=
    (hh.continuous_fderiv (by simp)).clm_comp continuous_const
  have hslice (t : Z) (x : E) : fderiv ℝ (fun y ↦ h (t, y)) x = D (t, x) :=
    ParameterDeformation.fderiv_slice_right (hh.differentiable (by simp)) t x
  have hDzero (x : E) : D (0, x) = 0 := by
    rw [← hslice]
    have he : (fun y ↦ h (0, y)) = fun _ ↦ (0 : E) := funext hzero
    rw [he]
    exact (hasFDerivAt_const (0 : E) x).fderiv
  have hk : ∀ᶠ t in 𝓝 (0 : Z), ∀ x ∈ K, ‖D (t, x)‖ < ε := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    exact hD.norm.continuousAt.eventually_lt continuousAt_const (by simpa [hDzero] using hε)
  filter_upwards [hk] with t ht x
  by_cases hx : x ∈ K
  · simpa only [hslice] using ht x hx
  · have he : (fun y ↦ h (t, y)) =ᶠ[𝓝 x] fun _ ↦ (0 : E) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact hs t y hy
    rw [he.fderiv_eq, (hasFDerivAt_const (0 : E) x).fderiv, norm_zero]
    exact hε

/-- Compactly supported smooth deformations of the identity are actual global
smooth diffeomorphisms for a common open interval of parameters. -/
theorem exists_smooth_compact_deformation_inverse [Nontrivial E]
    {h : Z × E → E} (hh : ContDiff ℝ ∞ h) {K : Set E} (hK : IsCompact K)
    (hs : ∀ t x, x ∉ K → h (t, x) = 0) (hzero : ∀ x, h (0, x) = 0) :
    ∃ d : ℝ, 0 < d ∧
      (∀ t : Z, ‖t‖ < d → Function.Bijective (fun x ↦ x + h (t, x))) ∧
      ContDiffOn ℝ ∞
        (fun p : Z × E ↦ Function.invFun (fun x ↦ x + h (p.1, x)) p.2)
        {p | ‖p.1‖ < d} := by
  have hi : (ContinuousLinearMap.id ℝ E).IsInvertible :=
    ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hi.eventually_nhds
  let c : NNReal := ⟨min (1/2) ε, lt_min (by norm_num) hε |>.le⟩
  have hc : 0 < (c : ℝ) := lt_min (by norm_num) hε
  obtain ⟨d, hd, hb⟩ := Metric.mem_nhds_iff.mp (ParameterDeformation.eventually_uniform_fderiv_small hh hK hs hzero hc)
  have hsmall (t : Z) (ht : ‖t‖ < d) (x : E) :
      ‖fderiv ℝ (fun y ↦ h (t, y)) x‖ < (c : ℝ) := by
    apply hb
    simpa only [mem_ball, dist_zero_right] using ht
  have hbij (t : Z) (ht : ‖t‖ < d) : Function.Bijective (fun x ↦ x + h (t, x)) := by
    have hl : LipschitzWith c (fun x ↦ h (t, x)) := by
      apply lipschitzWith_of_nnnorm_fderiv_le
        ((hh.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
      intro x
      exact (hsmall t ht x).le
    have hc1 : c < 1 := by
      change min (1/2 : ℝ) ε < 1
      exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    obtain ⟨H, hH⟩ := exists_homeomorph_of_lipschitz_displacement _ hl hc1
    have he : (fun x ↦ x + h (t, x)) = H := funext (fun x ↦ (hH x).symm)
    rw [he]
    exact H.bijective
  refine ⟨d, hd, hbij, ?_⟩
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_parametric_invFun (fun p : Z × E ↦ p.2 + h p) (by simp)
  · have hopen : IsOpen {t : Z | ‖t‖ < d} := isOpen_lt continuous_norm continuous_const
    filter_upwards [hopen.mem_nhds hp] with t ht
    exact hbij t ht
  · exact (contDiff_snd.add hh).contDiffAt
  · let x := Function.invFun (fun x ↦ x + h (p.1, x)) p.2
    change (fderiv ℝ (fun y ↦ y + h (p.1, y)) x).IsInvertible
    have hsmooth : Differentiable ℝ (fun y ↦ h (p.1, y)) :=
      (hh.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    have hder : fderiv ℝ (fun y ↦ y + h (p.1, y)) x =
        ContinuousLinearMap.id ℝ E + fderiv ℝ (fun y ↦ h (p.1, y)) x :=
      ((hasFDerivAt_id x).add (hsmooth x).hasFDerivAt).fderiv
    rw [hder]
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (hsmall p.1 hp _).trans_le (min_le_right _ _)

end ParameterDeformation
end OAI.Analysis.PDE.Dirichlet
