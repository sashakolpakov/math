import OAI.Analysis.PDE.Dirichlet.Boundary.Slope
import Mathlib.Analysis.Calculus.MeanValue

open Filter Set Metric
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A twofold mean-value estimate at a point where the first jet vanishes. -/
theorem norm_le_quadratic_of_zero_jet {f : E → F} (hf : ContDiff ℝ 2 f)
    (hf0 : f 0 = 0) (hD0 : fderiv ℝ f 0 = 0) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hbound : ∀ y ∈ closedBall (0 : E) R, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C) :
    ∀ y ∈ closedBall (0 : E) R, ‖f y‖ ≤ C * ‖y‖ ^ 2 := by
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdDf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h0 : (0 : E) ∈ closedBall 0 R := by simpa using hR
  have hgrad : ∀ y ∈ closedBall (0 : E) R, ‖fderiv ℝ f y‖ ≤ C * ‖y‖ := by
    intro y hy
    simpa only [hD0, sub_zero] using
      (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ ↦ hdDf z) hbound h0 hy
  intro y hy
  have hyR : ‖y‖ ≤ R := by simpa using hy
  have hgrad' : ∀ z ∈ closedBall (0 : E) ‖y‖, ‖fderiv ℝ f z‖ ≤ C * ‖y‖ := by
    intro z hz
    have hzy : ‖z‖ ≤ ‖y‖ := by simpa using hz
    have hzR : z ∈ closedBall (0 : E) R := by simpa using hzy.trans hyR
    exact (hgrad z hzR).trans (mul_le_mul_of_nonneg_left hzy hC)
  have h0' : (0 : E) ∈ closedBall 0 ‖y‖ := by simp
  have hy' : y ∈ closedBall (0 : E) ‖y‖ := by simp
  have h := (convex_closedBall (0 : E) ‖y‖).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hdf z) hgrad' h0' hy'
  simpa only [hf0, sub_zero, pow_two, mul_assoc] using h

/-- The quadratic constant and neighborhood are obtained from continuity of
the actual second derivative. -/
theorem exists_quadratic_bound_of_zero_jet {f : E → F} (hf : ContDiff ℝ 2 f)
    (hf0 : f 0 = 0) (hD0 : fderiv ℝ f 0 = 0) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ y ∈ closedBall (0 : E) R, ‖f y‖ ≤ C * ‖y‖ ^ 2 := by
  let C := ‖fderiv ℝ (fderiv ℝ f) 0‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : Continuous (fun y ↦ ‖fderiv ℝ (fderiv ℝ f) y‖) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuous.norm
  have hevent : ∀ᶠ y in 𝓝 (0 : E), ‖fderiv ℝ (fderiv ℝ f) y‖ < C :=
    (hc.tendsto 0).eventually (eventually_lt_nhds (by dsimp [C]; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hR : 0 < ε / 2 := by positivity
  refine ⟨C, ε / 2, hC, hR, norm_le_quadratic_of_zero_jet hf hf0 hD0 hC.le hR.le ?_⟩
  intro y hy
  have hyε : y ∈ ball (0 : E) ε := by
    have hy' : dist y 0 ≤ ε / 2 := hy
    exact lt_of_le_of_lt hy' (by linarith)
  exact (hball hyε).le

/-- A function whose first derivative is normal to a level surface is
quadratically small on that surface, with a data-only local constant. -/
theorem exists_quadratic_bound_on_level_set {f r : E → ℝ} {a : ℝ}
    (hf : ContDiff ℝ 2 f) (hr : ContDiff ℝ 2 r) (hf0 : f 0 = 0) (hr0 : r 0 = 0)
    (hD : fderiv ℝ f 0 = a • fderiv ℝ r 0) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ y ∈ closedBall (0 : E) R, r y = 0 → |f y| ≤ C * ‖y‖ ^ 2 := by
  let g : E → ℝ := fun y ↦ f y + (-a) • r y
  have hg : ContDiff ℝ 2 g := hf.add (hr.const_smul (-a))
  have hg0 : g 0 = 0 := by simp [g, hf0, hr0]
  have hDg : fderiv ℝ g 0 = 0 := by
    have hd : fderiv ℝ g 0 = fderiv ℝ f 0 + (-a) • fderiv ℝ r 0 :=
      (((hf.differentiable (by norm_num)) 0).hasFDerivAt.add
        (((hr.differentiable (by norm_num)) 0).hasFDerivAt.const_smul (-a))).fderiv
    rw [hd, hD]
    simp
  obtain ⟨C, R, hC, hR, hb⟩ := exists_quadratic_bound_of_zero_jet hg hg0 hDg
  refine ⟨C, R, hC, hR, ?_⟩
  intro y hy hry
  simpa only [g, hry, smul_zero, add_zero, Real.norm_eq_abs] using hb y hy

end OAI.Analysis.PDE.Dirichlet
