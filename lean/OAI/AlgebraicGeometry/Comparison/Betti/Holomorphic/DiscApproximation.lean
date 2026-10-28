import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-! # Disc Approximation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DiscApproximation.Dolbeault

noncomputable section

/-! Actual Cauchy-series partial sums approximate a holomorphic
vector-valued function uniformly on every strictly smaller disc. -/

open Filter _root_.Metric
open scoped _root_.Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem powerSeriesPartialSum_entire (p : FormalMultilinearSeries ℂ ℂ F) (n : ℕ) :
    Differentiable ℂ (p.partialSum n) := by
  unfold FormalMultilinearSeries.partialSum
  apply Differentiable.fun_sum
  intro k hk
  exact (show ContDiff ℂ 1 (fun z => (p k) (fun _ => z)) from
    (p k).contDiff.comp (contDiff_pi.mpr (fun _ => contDiff_id))).differentiable (by simp)

def holomorphicDiscPartialSum (g : ℂ → F) (r : NNReal) (n : ℕ) : ℂ → F :=
  (cauchyPowerSeries g 0 r).partialSum n

theorem holomorphicDiscPartialSum_entire (g : ℂ → F) (r : NNReal) (n : ℕ) :
    Differentiable ℂ (holomorphicDiscPartialSum g r n) :=
  powerSeriesPartialSum_entire _ n

variable [CompleteSpace F]

theorem holomorphicDiscPartialSum_tendstoLocallyUniformly {g : ℂ → F} {r : NNReal}
    (hr : 0 < r) (hg : DifferentiableOn ℂ g (closedBall 0 r)) :
    TendstoLocallyUniformlyOn (holomorphicDiscPartialSum g r) g atTop (ball 0 r) := by
  change TendstoLocallyUniformlyOn (fun n z => (cauchyPowerSeries g 0 r).partialSum n z)
    g atTop (ball 0 r)
  simpa only [zero_add, Metric.eball_coe] using
    (hg.hasFPowerSeriesOnBall hr).tendstoLocallyUniformlyOn

theorem holomorphicDiscPartialSum_tendstoUniformly {g : ℂ → F} {r : NNReal}
    (hr : 0 < r) (hg : DifferentiableOn ℂ g (closedBall 0 r)) {s : ℝ} (hs : s < r) :
    TendstoUniformlyOn (holomorphicDiscPartialSum g r) g atTop (closedBall 0 s) :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp
    (holomorphicDiscPartialSum_tendstoLocallyUniformly hr hg) (closedBall 0 s)
    (closedBall_subset_ball hs) (isCompact_closedBall 0 s)

theorem exists_holomorphicDiscPartialSum_approx {g : ℂ → F} {r : NNReal}
    (hr : 0 < r) (hg : DifferentiableOn ℂ g (closedBall 0 r)) {s ε : ℝ}
    (hs : s < r) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ closedBall 0 s,
      ‖holomorphicDiscPartialSum g r n z - g z‖ < ε := by
  have h := Metric.tendstoUniformlyOn_iff.mp
    (holomorphicDiscPartialSum_tendstoUniformly hr hg hs) ε hε
  simpa only [Filter.eventually_atTop, dist_eq_norm, norm_sub_rev] using h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DiscApproximation.Dolbeault
