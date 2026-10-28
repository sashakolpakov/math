import OAI.Geometry.Nikodym.SmoothMetric

noncomputable section
open Set Metric Bornology
open scoped RealInnerProductSpace

namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Strict positivity in finite dimension gives a quantitative coercive
bound in the pre-existing coordinate norm. -/
theorem positive_quadratic_coercive (A : E →L[ℝ] E)
    (hA : ∀ u : E, u ≠ 0 → 0 < ⟪A u,u⟫) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : E, c * ‖u‖^2 ≤ ⟪A u,u⟫ := by
  by_cases hss : Subsingleton E
  · let : Subsingleton E := hss
    refine ⟨1,by norm_num,fun u => ?_⟩
    have hu : u = 0 := Subsingleton.elim _ _
    simp [hu]
  · let : Nontrivial E := not_subsingleton_iff_nontrivial.mp hss
    have hcont : Continuous (fun u : E => ⟪A u,u⟫) := by fun_prop
    obtain ⟨v,hv,hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
    have hvnorm : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
    have hv0 : v ≠ 0 := by intro h; simp [h] at hvnorm
    refine ⟨⟪A v,v⟫,hA v hv0,fun u => ?_⟩
    by_cases hu : u = 0
    · simp [hu]
    · have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hunit : ‖u‖⁻¹ • u ∈ sphere (0 : E) 1 := by
        simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
          abs_inv,abs_of_pos hnorm,inv_mul_cancel₀ hnorm.ne']
      have hscale : ⟪A (‖u‖⁻¹ • u),‖u‖⁻¹ • u⟫ * ‖u‖^2 = ⟪A u,u⟫ := by
        simp only [map_smul,real_inner_smul_left,inner_smul_right]
        field_simp
      have h := mul_le_mul_of_nonneg_right (hmin hunit) (sq_nonneg ‖u‖)
      rwa [hscale] at h

/-- The unit ball of a positive coordinate metric is bounded in the
original topology. This is the non-diamond condition required by
Mathlib's Riemannian bundle constructor. -/
theorem positive_quadratic_isVonNBounded (A : E →L[ℝ] E)
    (hA : ∀ u : E, u ≠ 0 → 0 < ⟪A u,u⟫) :
    IsVonNBounded ℝ {u : E | ⟪A u,u⟫ < 1} := by
  obtain ⟨c,hc,hcoer⟩ := positive_quadratic_coercive A hA
  apply (NormedSpace.isVonNBounded_iff ℝ).mpr
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1 + 1/c,fun u hu => ?_⟩
  have hnorm : ‖u‖^2 ≤ 1/c := (le_div_iff₀ hc).mpr (by
    have h := (hcoer u).trans hu.le
    nlinarith)
  have hinv : 0 < 1/c := by positivity
  nlinarith [sq_nonneg (‖u‖-1)]

namespace SmoothCoordinateMetric

theorem coercive (g : SmoothCoordinateMetric E) {x : E} (hx : x ∈ g.domain) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : E, c * ‖u‖^2 ≤ g.inner x u u :=
  positive_quadratic_coercive (g.coefficient x) (g.positive x hx)

theorem unitBall_isVonNBounded (g : SmoothCoordinateMetric E)
    {x : E} (hx : x ∈ g.domain) :
    IsVonNBounded ℝ {u : E | g.inner x u u < 1} :=
  positive_quadratic_isVonNBounded (g.coefficient x) (g.positive x hx)

end SmoothCoordinateMetric
end OAI.Geometry.Nikodym
