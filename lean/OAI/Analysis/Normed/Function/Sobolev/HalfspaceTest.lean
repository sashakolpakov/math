import OAI.Analysis.Normed.Function.Sobolev.HalfspaceTestGeometry

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

open OAI.Analysis.PDE.Weak

variable {d : ℕ}

/-- Local weak differentiation in a halfspace may be tested up to its
boundary when the test vanishes there, or in a tangential direction.
The proof cuts out a shrinking boundary strip and controls the actual
commutator, rather than postulating a boundary trace. -/
theorem halfspace_weak_test
    (k : Fin d) (v : Fin d→ℝ) {u g : (Fin d→ℝ)→ℝ}
    (hu : Integrable u) (hg : Integrable g)
    (hd : OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn volume {x|0<x k} v u g)
    (φ : (Fin d→ℝ)→ℝ) (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hboundary : v k=0 ∨ ∀x,x k=0→φ x=0) :
    (∫ x in {x|0<x k},g x*φ x) = -(∫ x in {x|0<x k},u x*fderiv ℝ φ x v) := by
  obtain ⟨B,hB⟩ := hs.exists_bound_of_continuous hφ.continuous
  obtain ⟨D,hD⟩ := (hs.fderiv (𝕜:=ℝ)).exists_bound_of_continuous (hφ.continuous_fderiv one_ne_zero)
  have hD0 : 0≤D := (norm_nonneg _).trans (hD 0)
  obtain ⟨C,hC0,hC⟩ := exists_transition_derivative_bound
  have hnormal : ∃L:ℝ,0≤L ∧ ∀x,|v k*φ x|≤L*|x k| := by
    rcases hboundary with hv|hz
    · exact ⟨0,le_rfl,fun x ↦ by simp [hv]⟩
    · refine ⟨|v k| *D,mul_nonneg (abs_nonneg _) hD0,fun x ↦ ?_⟩
      rw [abs_mul,mul_assoc]
      exact mul_le_mul_of_nonneg_left (abs_test_le_normal hφ k hz hD x) (abs_nonneg _)
  obtain ⟨L,hL0,hL⟩ := hnormal
  have htest (n : ℕ) : (∫ x,g x*halfspaceTest n k φ x) =
      -(∫ x,u x*fderiv ℝ (halfspaceTest n k φ) x v) := by
    simpa only [RCLike.inner_apply,conj_trivial,mul_comm] using
      hd (halfspaceTest n k φ) (contDiff_halfspaceTest n k hφ)
        (hasCompactSupport_halfspaceTest n k hs) (halfspaceTest_support n k φ)
  have hnormtest (n : ℕ) (x : Fin d→ℝ) : |halfspaceTest n k φ x|≤B := by
    rw [halfspaceTest,abs_mul,abs_of_nonneg (halfspaceGapCutoff_nonneg n (x k))]
    exact (mul_le_of_le_one_left (abs_nonneg _) (halfspaceGapCutoff_le_one n (x k))).trans (hB x)
  have hnormder (n : ℕ) (x : Fin d→ℝ) :
      |fderiv ℝ (halfspaceTest n k φ) x v|≤D*‖v‖+2*C*L := by
    rw [halfspaceTest_derivative n k hφ]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_mul,abs_of_nonneg (halfspaceGapCutoff_nonneg n (x k))]
      apply (mul_le_of_le_one_left (abs_nonneg _) (halfspaceGapCutoff_le_one n (x k))).trans
      exact ((fderiv ℝ φ x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hD x) (norm_nonneg _))
    · rw [mul_assoc]
      exact halfspaceGapSlope_mul_bound hC0 hL0 hC n (x k) (v k*φ x) (hL x)
  let H : Set (Fin d→ℝ) := {x|0<x k}
  have hHm : MeasurableSet H := measurableSet_lt measurable_const (measurable_pi_apply k)
  have hvlim (x : Fin d→ℝ) : Tendsto (fun n ↦ halfspaceTest n k φ x) atTop (𝓝 (H.indicator φ x)) := by
    have h := (halfspaceGapCutoff_tendsto (x k)).mul_const (φ x)
    simpa only [halfspaceTest,H,indicator,Set.mem_ofPred_eq,ite_mul,one_mul,zero_mul] using h
  have hdlim (x : Fin d→ℝ) : Tendsto (fun n ↦ fderiv ℝ (halfspaceTest n k φ) x v) atTop
      (𝓝 (H.indicator (fun y ↦ fderiv ℝ φ y v) x)) := by
    have heq : (fun n ↦ fderiv ℝ (halfspaceTest n k φ) x v) =ᶠ[atTop]
        (fun n ↦ halfspaceGapCutoff n (x k)*fderiv ℝ φ x v) := by
      filter_upwards [halfspaceGapSlope_eventually_zero (x k)] with n hn
      simp [halfspaceTest_derivative n k hφ,hn]
    apply Tendsto.congr' heq.symm
    have h := (halfspaceGapCutoff_tendsto (x k)).mul_const (fderiv ℝ φ x v)
    simpa only [H,indicator,Set.mem_ofPred_eq,ite_mul,one_mul,zero_mul] using h
  have hleft : Tendsto (fun n ↦ ∫ x,g x*halfspaceTest n k φ x) atTop
      (𝓝 (∫ x in H,g x*φ x)) := by
    rw [← integral_indicator hHm]
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖g x‖*B)
    · intro n
      exact hg.aestronglyMeasurable.mul (contDiff_halfspaceTest n k hφ).continuous.aestronglyMeasurable
    · exact hg.norm.mul_const B
    · intro n
      filter_upwards with x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hnormtest n x) (norm_nonneg _)
    · filter_upwards with x
      have h := (hvlim x).const_mul (g x)
      by_cases hx : x∈H <;> simpa [indicator,hx] using h
  have hright : Tendsto (fun n ↦ ∫ x,u x*fderiv ℝ (halfspaceTest n k φ) x v) atTop
      (𝓝 (∫ x in H,u x*fderiv ℝ φ x v)) := by
    rw [← integral_indicator hHm]
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖u x‖*(D*‖v‖+2*C*L))
    · intro n
      exact hu.aestronglyMeasurable.mul
        (((contDiff_halfspaceTest n k hφ).continuous_fderiv one_ne_zero).clm_apply
          continuous_const).aestronglyMeasurable
    · exact hu.norm.mul_const _
    · intro n
      filter_upwards with x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hnormder n x) (norm_nonneg _)
    · filter_upwards with x
      have h := (hdlim x).const_mul (u x)
      by_cases hx : x∈H <;> simpa [indicator,hx] using h
  exact tendsto_nhds_unique hleft (hright.neg.congr fun n ↦ (htest n).symm)

end OAI.Analysis.Normed.Function.Sobolev
