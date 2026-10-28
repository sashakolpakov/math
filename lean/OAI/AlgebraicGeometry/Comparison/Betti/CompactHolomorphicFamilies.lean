import OAI.AlgebraicGeometry.Comparison.Betti.CircleIntegralNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DiscApproximation
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Compact Holomorphic Families -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CompactHolomorphicFamilies.Dolbeault

noncomputable section

/-! Pointwise holomorphic compact families satisfy the genuine
Banach-valued Cauchy formula, giving uniform polynomial approximation
in the supremum norm of the parameter family. -/

open _root_.Metric _root_.Complex
open scoped Real

variable {K F : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {g : ℂ → C(K, F)} {r : NNReal}

theorem compactFamily_cauchy_formula
    (hg : ContinuousOn g (closedBall 0 r))
    (hhol : ∀ p : K, DifferentiableOn ℂ (fun z => g z p) (closedBall 0 r))
    {w : ℂ} (hw : w ∈ ball 0 r) :
    (2 * π * I : ℂ)⁻¹ • circleIntegral (fun z => (z - w)⁻¹ • g z) 0 r = g w := by
  have hne : ∀ z ∈ sphere 0 (r : ℝ), z - w ≠ 0 := by
    intro z hz he
    have hzw := sub_eq_zero.mp he
    subst z
    have heq := mem_sphere.mp hz
    have hlt := mem_ball.mp hw
    linarith
  have hc : ContinuousOn (fun z => (z - w)⁻¹ • g z) (sphere 0 (r : ℝ)) :=
    ((continuousOn_id.sub continuousOn_const).inv₀ hne).smul (hg.mono sphere_subset_closedBall)
  have hi := hc.circleIntegrable r.coe_nonneg
  apply ContinuousMap.ext
  intro p
  change (ContinuousMap.evalCLM ℂ p)
    ((2 * π * I : ℂ)⁻¹ • circleIntegral (fun z => (z - w)⁻¹ • g z) 0 r) = g w p
  rw [map_smul, CircleIntegralNaturality.Dolbeault.circleIntegral_map (ContinuousMap.evalCLM ℂ p) hi]
  change (2 * π * I : ℂ)⁻¹ • circleIntegral (fun z => (z - w)⁻¹ • g z p) 0 r = g w p
  exact ((hhol p).mono closure_ball_subset_closedBall).diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

theorem compactFamily_hasFPowerSeriesOnBall (hr : 0 < r)
    (hg : ContinuousOn g (closedBall 0 r))
    (hhol : ∀ p : K, DifferentiableOn ℂ (fun z => g z p) (closedBall 0 r)) :
    HasFPowerSeriesOnBall g (cauchyPowerSeries g 0 r) 0 r := by
  apply (hasFPowerSeriesOn_cauchy_integral
    ((hg.mono sphere_subset_closedBall).circleIntegrable r.coe_nonneg) hr).congr
  intro w hw
  exact compactFamily_cauchy_formula hg hhol (by simpa only [Metric.eball_coe] using hw)

theorem compactFamily_tendstoUniformly {s : NNReal} (hs : s < r) (hr : 0 < r)
    (hg : ContinuousOn g (closedBall 0 r))
    (hhol : ∀ p : K, DifferentiableOn ℂ (fun z => g z p) (closedBall 0 r)) :
    TendstoUniformlyOn (fun n z => (cauchyPowerSeries g 0 r).partialSum n z)
      g Filter.atTop (ball 0 s) := by
  simpa only [zero_add] using (compactFamily_hasFPowerSeriesOnBall hr hg hhol).tendstoUniformlyOn
    (show (s : ENNReal) < r from ENNReal.coe_lt_coe.mpr hs)

end

end OAI.AlgebraicGeometry.Comparison.Betti.CompactHolomorphicFamilies.Dolbeault
