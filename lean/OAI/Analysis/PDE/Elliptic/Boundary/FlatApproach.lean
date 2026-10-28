import OAI.Analysis.PDE.Elliptic.Boundary.NormalJet
import OAI.Analysis.PDE.Elliptic.Boundary.TangentRows

/-! The actual tangential expansion and interior Hessian oscillation imply
an interior-to-boundary estimate for all but the normal-normal Hessian
coefficient. No mixed-derivative approach estimate is assumed. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace OAI.Analysis.PDE.Dirichlet
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem flat_hessian_approach_remainder {u : E → ℝ} (hu : ContDiff ℝ 3 u)
    {ν z : E} (hν : ‖ν‖ = 1) (hz : ‖z‖ < 1) (hνz : inner ℝ ν z = 0)
    (hzero : ∀ y, ‖y‖ ≤ 1 → inner ℝ ν y = 0 → u y = 0)
    {h κ A B a b : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b)
    (hexp : ∀ e, ‖e‖ ≤ 1 → inner ℝ ν e = 0 →
      ∀ y, ‖y - z‖ ≤ 2 * h → 0 ≤ inner ℝ ν y →
        |fderiv ℝ u y e - fderiv ℝ (fderiv ℝ u) z ν e * inner ℝ ν y| ≤
          A * h ^ a * inner ℝ ν y)
    (hint : ∀ y ∈ Metric.closedBall (z + h • ν) (κ * h / 2),
      ‖fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ u) (z + h • ν)‖ ≤
        B * (‖y - (z + h • ν)‖ / h) ^ b) :
    let H := fderiv ℝ (gradient u) (z + h • ν) - fderiv ℝ (gradient u) z
    ‖H - inner ℝ (H ν) ν • rankOne ℝ ν ν‖ ≤
      8 * ((8 * A / κ ^ (1 + a) + B) * h ^ (a * b / (1 + b))) := by
  apply hessian_normal_remainder_of_tangent_differentials (hu.of_le (by norm_num)) hν
    (by positivity)
  intro e he hνe
  have hφ : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) :=
    OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) e
  have hφzero : ∀ᶠ y in 𝓝 z, inner ℝ ν y = 0 → OAI.Analysis.PDE.Dirichlet.directionalDerivative u e y = 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball (0 : E) 1 by simpa using hz)]
      with y hy hflat
    change fderiv ℝ u y e = 0
    exact flat_boundary_first_jet (hu.differentiable (by norm_num)) hν
      (by simpa using hy) hflat hνe hzero
  apply fderiv_approaches_zero_trace hν hνz hh hh1 hκ hκ1 hA hB ha hb
    (hφ.differentiable (by norm_num) z) hφzero
    (fun y _ => hφ.differentiable (by norm_num) y)
  · intro y hy hyν
    have hd : fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) z ν =
        fderiv ℝ (fderiv ℝ u) z ν e := OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice (hu.of_le (by norm_num)) ν e z
    simpa only [OAI.Analysis.PDE.Dirichlet.directionalDerivative, hd] using hexp e he hνe y hy hyν
  · intro y hy
    apply (directional_fderiv_oscillation (hu.of_le (by norm_num)) y (z + h • ν) e).trans
    exact (mul_le_mul_of_nonneg_right (hint y hy) (norm_nonneg e)).trans
      (mul_le_of_le_one_right (by positivity) he)

end OAI.Analysis.PDE.Elliptic
