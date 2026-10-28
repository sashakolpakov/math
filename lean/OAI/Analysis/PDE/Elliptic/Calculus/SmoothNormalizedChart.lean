import OAI.Analysis.PDE.Elliptic.Boundary.SmoothInverse
import OAI.Analysis.PDE.Elliptic.Boundary.Normal

noncomputable section
open Set Filter Metric InnerProductSpace
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Smooth doubled boundary chart. Scaling takes place inside a genuine
smooth inverse neighborhood, so global C∞ regularity is retained. -/
theorem exists_smooth_doubled_boundary_chart {r : E → ℝ} (hr : ContDiff ℝ ∞ r)
    (x : E) (hg : fderiv ℝ r x ≠ 0) {U : Set E} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (v : E) (c : ℝ) (G P : E → E), ‖v‖ = 1 ∧ 0 < c ∧
      ContDiff ℝ ∞ G ∧ ContDiff ℝ ∞ P ∧ G 0 = x ∧
      ∀ z ∈ closedBall 0 2,
        G z ∈ U ∧ (fun y => P (G y)) =ᶠ[𝓝 z] id ∧
        r (G z)-r x = -c*inner ℝ v z := by
  let g := fderiv ℝ r x
  obtain ⟨v,c₀,hv,hc₀,hnormal⟩ := exists_inward_unit_normal g hg
  obtain ⟨w,hw⟩ := LinearMap.range_eq_top.mp (OAI.Analysis.PDE.Dirichlet.real_linear_form_range_top g hg) 1
  let P₀ := flatteningMap r x g w
  have hP₀ : ContDiff ℝ ∞ P₀ := contDiff_flatteningMap hr x g w
  have hP₀x : P₀ x = 0 := flatteningMap_base r x g w
  have hdP₀ : HasFDerivAt P₀ (ContinuousLinearMap.id ℝ E) x :=
    hasFDerivAt_flatteningMap (hr.differentiable (by simp) x).hasFDerivAt w
  obtain ⟨G₀,R,W,hG₀,hR,hW,hWb,hxW,hG₀0,hG₀W,hP₀W,hPG,hGP⟩ :=
    exists_smooth_inverse_chart P₀ hP₀ x hP₀x hdP₀
  have hGU : ∀ᶠ y in 𝓝 (0:E), G₀ y ∈ U :=
    hG₀.continuous.continuousAt.tendsto.eventually (hU.mem_nhds (by simpa only [hG₀0] using hxU))
  have hgood : ∀ᶠ y in 𝓝 (0:E), y ∈ ball 0 R ∧ G₀ y ∈ U :=
    Filter.Eventually.and (ball_mem_nhds (0:E) hR) hGU
  obtain ⟨ε,hε,hεgood⟩ := Metric.mem_nhds_iff.mp hgood
  let ρ := ε/8
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  let G : E → E := fun z => G₀ (ρ • z)
  let P : E → E := fun y => ρ⁻¹ • P₀ y
  have hscaled z (hz : ‖z‖ ≤ 4) : ρ • z ∈ ball (0:E) ε := by
    simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    dsimp only [ρ]
    nlinarith
  have hin z (hz : ‖z‖ ≤ 4) : ρ • z ∈ ball (0:E) R := (hεgood (hscaled z hz)).1
  refine ⟨v,ρ*c₀,G,P,hv,mul_pos hρ hc₀,
    hG₀.comp (contDiff_const.smul contDiff_id),contDiff_const.smul hP₀,?_,?_⟩
  · simpa only [G,smul_zero] using hG₀0
  · intro z hz
    have hz2 : ‖z‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hz
    refine ⟨(hεgood (hscaled z (by linarith))).2,?_,?_⟩
    · filter_upwards [isOpen_ball.mem_nhds (show z ∈ ball (0:E) 4 by
        simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < 4 by linarith))] with y hy
      have hyn : ‖y‖ ≤ 4 := (show ‖y‖ < 4 by simpa only [mem_ball,dist_zero_right] using hy).le
      change ρ⁻¹ • P₀ (G₀ (ρ • y)) = y
      rw [hPG _ (hin y hyn),smul_smul,inv_mul_cancel₀ hρ.ne',one_smul]
    · have he := flatteningMap_level r x g w hw (G₀ (ρ • z))
      change g (P₀ (G₀ (ρ • z))) = r (G z)-r x at he
      rw [hPG _ (hin z (by linarith)),map_smul,hnormal] at he
      change ρ * (-c₀ * inner ℝ v z) = _ at he
      rw [← he]
      ring

end OAI.Analysis.PDE.Elliptic
