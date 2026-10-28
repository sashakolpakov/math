import OAI.Geometry.Nikodym.Jacobi.Functions

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter Metric
open scoped Topology

theorem curvatureSin_div_tendsto_one (κ : ℝ) :
    Tendsto (fun t : ℝ => curvatureSin κ t/t) (𝓝[≠] 0) (𝓝 1) := by
  have h := (hasDerivAt_curvatureSin κ 0).tendsto_slope_zero
  simpa only [curvatureCos_zero,curvatureSin_zero,zero_add,sub_zero,
    smul_eq_mul,mul_comm,div_eq_mul_inv] using h

/-- Both the normal Jacobi scale and the radial projective chart are
positive on a genuine neighborhood of the origin. -/
theorem curvature_functions_local_pos (κ : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      (∀ t : ℝ, |t| < r → 0 < curvatureCos κ t) ∧
      (∀ t : ℝ, 0 < t → t < r → 0 < curvatureSin κ t) := by
  have he : ∀ᶠ t in 𝓝 (0:ℝ), 0 < curvatureCos κ t :=
    ((contDiff_curvatureCos κ).continuous.continuousAt).eventually
      (lt_mem_nhds (by simp : 0 < curvatureCos κ 0))
  obtain ⟨r,hr,hrb⟩ := Metric.eventually_nhds_iff.mp he
  have hc (t : ℝ) (ht : |t| < r) : 0 < curvatureCos κ t :=
    hrb (by simpa only [Real.dist_eq,sub_zero] using ht)
  refine ⟨r,hr,hc,fun t ht htr => ?_⟩
  have hm : StrictMonoOn (curvatureSin κ) (Ioo (-r) r) :=
    strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      (contDiff_curvatureSin κ).continuous.continuousOn (fun s hs => by
        rw [(hasDerivAt_curvatureSin κ s).deriv]
        apply hc
        have hs' : -r < s ∧ s < r := by simpa only [interior_Ioo,mem_Ioo] using hs
        exact abs_lt.mpr hs')
  have h := hm (show (0:ℝ) ∈ Ioo (-r) r by constructor <;> linarith)
    (show t ∈ Ioo (-r) r by constructor <;> linarith) ht
  simpa only [curvatureSin_zero] using h

end OAI.Geometry.Nikodym
