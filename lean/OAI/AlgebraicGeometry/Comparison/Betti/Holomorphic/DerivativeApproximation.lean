import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DiscApproximation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Derivative Approximation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DerivativeApproximation.Dolbeault

noncomputable section

section

/-! Locally uniform holomorphic approximation also approximates all
complex derivatives, with one approximation order for finitely many
derivatives on a fixed smaller closed disc. -/

open Filter _root_.Metric
open scoped _root_.Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem holomorphic_iteratedDeriv_on {g : ℂ → F} {U : Set ℂ}
    (hg : DifferentiableOn ℂ g U) (hU : IsOpen U) (k : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv k g) U := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hg
  | succ k hk => simpa only [iteratedDeriv_succ] using hk.deriv hU

theorem holomorphicLocallyUniform_iteratedDeriv {g : ℕ → ℂ → F} {h : ℂ → F} {U : Set ℂ}
    (hconv : TendstoLocallyUniformlyOn g h atTop U)
    (hg : ∀ n, DifferentiableOn ℂ (g n) U) (hU : IsOpen U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (g n)) (iteratedDeriv k h) atTop U := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hconv
  | succ k hk =>
      simpa only [iteratedDeriv_succ, Function.comp_def] using
        hk.deriv (Eventually.of_forall (fun n => holomorphic_iteratedDeriv_on (hg n) hU k)) hU

theorem holomorphicDiscPartialSum_iteratedDeriv_uniform {g : ℂ → F} {r : NNReal}
    (hr : 0 < r) (hg : DifferentiableOn ℂ g (closedBall 0 r)) {s : ℝ} (hs : s < r) (k : ℕ) :
    TendstoUniformlyOn (fun n => iteratedDeriv k (DiscApproximation.Dolbeault.holomorphicDiscPartialSum g r n))
      (iteratedDeriv k g) atTop (closedBall 0 s) :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp
    (holomorphicLocallyUniform_iteratedDeriv
      (DiscApproximation.Dolbeault.holomorphicDiscPartialSum_tendstoLocallyUniformly hr hg)
      (fun n => (DiscApproximation.Dolbeault.holomorphicDiscPartialSum_entire g r n).differentiableOn) isOpen_ball k)
    (closedBall 0 s) (closedBall_subset_ball hs) (isCompact_closedBall 0 s)

theorem exists_holomorphicDiscPartialSum_approx_derivatives {g : ℂ → F} {r : NNReal}
    (hr : 0 < r) (hg : DifferentiableOn ℂ g (closedBall 0 r)) {s ε : ℝ}
    (hs : s < r) (hε : 0 < ε) (m : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ m, ∀ z ∈ closedBall 0 s,
      ‖iteratedDeriv k (DiscApproximation.Dolbeault.holomorphicDiscPartialSum g r n) z - iteratedDeriv k g z‖ < ε := by
  have hk (k : ℕ) : ∀ᶠ n in atTop, ∀ z ∈ closedBall 0 s,
      ‖iteratedDeriv k (DiscApproximation.Dolbeault.holomorphicDiscPartialSum g r n) z - iteratedDeriv k g z‖ < ε := by
    have h := Metric.tendstoUniformlyOn_iff.mp
      (holomorphicDiscPartialSum_iteratedDeriv_uniform hr hg hs k) ε hε
    exact h.mono (fun n hn z hz => by simpa only [dist_eq_norm, norm_sub_rev] using hn z hz)
  have hAll : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (m + 1), ∀ z ∈ closedBall 0 s,
      ‖iteratedDeriv k (DiscApproximation.Dolbeault.holomorphicDiscPartialSum g r n) z - iteratedDeriv k g z‖ < ε := by
    rw [eventually_all_finset]
    exact fun k _ => hk k
  obtain ⟨N, hN⟩ := eventually_atTop.mp hAll
  exact ⟨N, fun n hn k hkm z hz => hN n hn k (Finset.mem_range.mpr (by omega)) z hz⟩

end

/-! Evaluation and other continuous complex-linear coefficient maps
commute with all actual derivatives of a holomorphic function. -/

open Set Filter
open scoped _root_.Topology

variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem holomorphic_iteratedDeriv_map (L : F →L[ℂ] G) {g : ℂ → F} {U : Set ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv k (fun w => L (g w)) z = L (iteratedDeriv k g z) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have he : iteratedDeriv k (fun w => L (g w)) =ᶠ[𝓝 z]
        (fun w => L (iteratedDeriv k g w)) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact ih hw
    rw [he.deriv_eq]
    exact (L.hasFDerivAt.comp_hasDerivAt z
      (((holomorphic_iteratedDeriv_on hg hU k) z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt).deriv

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DerivativeApproximation.Dolbeault
