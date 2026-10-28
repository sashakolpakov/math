import OAI.AlgebraicGeometry.Comparison.Betti.CircleIntegralNaturality

/-! # Separated Holomorphic Families -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SeparatedHolomorphicFamilies.Dolbeault

noncomputable section

/-! Continuous Banach-valued families satisfy the original Cauchy formula
when a separating family of continuous complex-linear coefficient maps
sends them to holomorphic functions. -/

open Set _root_.Metric _root_.Complex
open scoped Real _root_.Topology

variable {B F J : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem separatingFamily_cauchy_formula (L : J → B →L[ℂ] F)
    (hsep : ∀ x y : B, (∀ j, L j x = L j y) → x = y)
    {g : ℂ → B} {c : ℂ} {r : NNReal} (hg : ContinuousOn g (closedBall c r))
    (hhol : ∀ j : J, DifferentiableOn ℂ (fun z => L j (g z)) (closedBall c r))
    {w : ℂ} (hw : w ∈ ball c r) :
    (2 * π * I : ℂ)⁻¹ • circleIntegral (fun z => (z - w)⁻¹ • g z) c r = g w := by
  have hne : ∀ z ∈ sphere c (r : ℝ), z - w ≠ 0 := by
    intro z hz he
    have hzw := sub_eq_zero.mp he
    subst z
    have heq := mem_sphere.mp hz
    have hlt := mem_ball.mp hw
    linarith
  have hc : ContinuousOn (fun z => (z - w)⁻¹ • g z) (sphere c (r : ℝ)) :=
    ((continuousOn_id.sub continuousOn_const).inv₀ hne).smul (hg.mono sphere_subset_closedBall)
  apply hsep
  intro j
  rw [map_smul, CircleIntegralNaturality.Dolbeault.circleIntegral_map (L j) (hc.circleIntegrable r.coe_nonneg)]
  simp only [map_smul]
  exact ((hhol j).mono closure_ball_subset_closedBall).diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

theorem separatingFamily_hasFPowerSeriesOnBall (L : J → B →L[ℂ] F)
    (hsep : ∀ x y : B, (∀ j, L j x = L j y) → x = y)
    {g : ℂ → B} {c : ℂ} {r : NNReal} (hr : 0 < r) (hg : ContinuousOn g (closedBall c r))
    (hhol : ∀ j : J, DifferentiableOn ℂ (fun z => L j (g z)) (closedBall c r)) :
    HasFPowerSeriesOnBall g (cauchyPowerSeries g c r) c r := by
  apply (hasFPowerSeriesOn_cauchy_integral
    ((hg.mono sphere_subset_closedBall).circleIntegrable r.coe_nonneg) hr).congr
  intro w hw
  exact separatingFamily_cauchy_formula L hsep hg hhol (by simpa only [Metric.eball_coe] using hw)

theorem separatingFamily_holomorphic (L : J → B →L[ℂ] F)
    (hsep : ∀ x y : B, (∀ j, L j x = L j y) → x = y)
    {g : ℂ → B} {U : Set ℂ} (hU : IsOpen U) (hg : ContinuousOn g U)
    (hhol : ∀ j : J, DifferentiableOn ℂ (fun z => L j (g z)) U) :
    DifferentiableOn ℂ g U := by
  intro z hz
  obtain ⟨r, hr, hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  have hpow := separatingFamily_hasFPowerSeriesOnBall L hsep
    (r := ⟨r, hr.le⟩) hr (hg.mono hsub) (fun j => (hhol j).mono hsub)
  exact (hpow.analyticOnNhd z (mem_eball_self hpow.r_pos)).differentiableAt.differentiableWithinAt

end

end OAI.AlgebraicGeometry.Comparison.Betti.SeparatedHolomorphicFamilies.Dolbeault
