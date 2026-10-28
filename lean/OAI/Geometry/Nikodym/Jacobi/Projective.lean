import OAI.Geometry.Nikodym.Jacobi.Local

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter Metric
open scoped Topology ContDiff

/-- Projective radial coordinate associated with curvature κ. -/
def curvatureTan (κ t : ℝ) : ℝ := curvatureSin κ t / curvatureCos κ t

@[simp] theorem curvatureTan_zero (κ : ℝ) : curvatureTan κ 0 = 0 := by
  simp [curvatureTan]

theorem contDiffAt_curvatureTan (κ t : ℝ) (ht : curvatureCos κ t ≠ 0) :
    ContDiffAt ℝ ∞ (curvatureTan κ) t :=
  (contDiff_curvatureSin κ).contDiffAt.div (contDiff_curvatureCos κ).contDiffAt ht

theorem hasDerivAt_curvatureTan (κ t : ℝ) (ht : curvatureCos κ t ≠ 0) :
    HasDerivAt (curvatureTan κ) (1 / (curvatureCos κ t)^2) t := by
  have hd := (hasDerivAt_curvatureSin κ t).div (hasDerivAt_curvatureCos κ t) ht
  have he : curvatureCos κ t * curvatureCos κ t -
      curvatureSin κ t * (-κ * curvatureSin κ t) = 1 := by
    nlinarith [curvature_energy κ t]
  simpa only [he] using! hd

/-- Exact Beltrami denominator in radial coordinates. -/
theorem curvatureTan_denominator (κ t : ℝ) (ht : curvatureCos κ t ≠ 0) :
    1 + κ * (curvatureTan κ t)^2 = 1 / (curvatureCos κ t)^2 := by
  unfold curvatureTan
  field_simp
  nlinarith [curvature_energy κ t]

theorem curvatureTan_local_pos (κ : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      (∀ t : ℝ, |t| < r → 0 < curvatureCos κ t) ∧
      StrictMonoOn (curvatureTan κ) (Ioo (-r) r) ∧
      (∀ t : ℝ, 0 < t → t < r → 0 < curvatureTan κ t) := by
  obtain ⟨r,hr,hc,hs⟩ := curvature_functions_local_pos κ
  refine ⟨r,hr,hc,?_,fun t ht htr => div_pos (hs t ht htr) (hc t ?_)⟩
  · apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · intro t ht
      exact (contDiffAt_curvatureTan κ t (hc t (abs_lt.mpr ht)).ne').continuousAt.continuousWithinAt
    · intro t ht
      have habs : |t| < r := abs_lt.mpr (by simpa only [interior_Ioo,mem_Ioo] using ht)
      rw [(hasDerivAt_curvatureTan κ t (hc t habs).ne').deriv]
      exact div_pos zero_lt_one (sq_pos_of_pos (hc t habs))
  · rw [abs_of_pos ht]
    exact htr

end OAI.Geometry.Nikodym
