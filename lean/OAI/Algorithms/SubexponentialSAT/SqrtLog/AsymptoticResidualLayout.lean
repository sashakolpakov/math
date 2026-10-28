import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticResidual

namespace OAI.Algorithms

/-! The layout guards hold uniformly for all half-size residuals and all
polynomially bounded branch-dependent occurrence/arity parameters. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_uniform_layout_guards (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ a b : ℕ, a ≤ L m ^ q → b ≤ L m ^ q →
      2 ≤ layoutQ m ∧
      4 * layoutCutoff m b ≤ layoutQ m ∧
      16 * layoutQ m * layoutR m ^ 2 ≤ m ∧
      4096 * (b + a) * b ^ 2 * layoutR m ^ 2 * L m ^ 4 *
        (layoutR m ^ (2 * layoutQ m)) ^ 2 ≤ m := by
  have hmax : ∀ᶠ m : ℕ in atTop, L m ^ q ≤ L m ^ q := Eventually.of_forall (fun _ => le_rfl)
  filter_upwards [eventually_layoutQ_ge 2,
    eventually_layout_fits (fun m => L m ^ q) q hmax,
    eventually_layout_small_grid,
    eventually_layout_large_grid (fun m => L m ^ q) (fun m => L m ^ q) q hmax hmax]
    with m hQ hfit hsmall hlarge a b ha hb
  refine ⟨hQ, ?_, hsmall, ?_⟩
  · exact (Nat.mul_le_mul_left 4 (layoutCutoff_mono m hb)).trans hfit
  · exact (by gcongr :
      4096 * (b + a) * b ^ 2 * layoutR m ^ 2 * L m ^ 4 *
          (layoutR m ^ (2 * layoutQ m)) ^ 2 ≤
        4096 * (L m ^ q + L m ^ q) * (L m ^ q) ^ 2 * layoutR m ^ 2 * L m ^ 4 *
          (layoutR m ^ (2 * layoutQ m)) ^ 2).trans hlarge

theorem eventually_residual_layout_guards (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m a b : ℕ, n ≤ 2 * m → a ≤ L m ^ q → b ≤ L m ^ q →
      2 ≤ layoutQ m ∧
      4 * layoutCutoff m b ≤ layoutQ m ∧
      16 * layoutQ m * layoutR m ^ 2 ≤ m ∧
      4096 * (b + a) * b ^ 2 * layoutR m ^ 2 * L m ^ 4 *
        (layoutR m ^ (2 * layoutQ m)) ^ 2 ≤ m := by
  filter_upwards [eventually_uniform_half (eventually_uniform_layout_guards q)] with n hn m a b hnm ha hb
  exact hn m hnm a b ha hb

theorem eventually_uniform_label_log (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ b : ℕ, 1 ≤ b → b ≤ L m ^ q →
      Real.log (4 * (m : ℝ) * b * (8 * (layoutQ m : ℝ)) ^
        (2 * layoutCutoff m b) + 1) ≤ 4 * (L m : ℝ) ^ 2 := by
  have hmax : ∀ᶠ m : ℕ in atTop, 1 ≤ L m ^ q ∧ L m ^ q ≤ L m ^ q :=
    Eventually.of_forall (fun m => ⟨Nat.succ_le_of_lt (pow_pos (L_pos m) q), le_rfl⟩)
  filter_upwards [eventually_layout_label_log (fun m => L m ^ q) q hmax,
    eventually_layoutQ_ge 1] with m hm hQ b hb0 hb
  have hR := layoutCutoff_mono m hb
  have hQ' : (1 : ℝ) ≤ layoutQ m := by exact_mod_cast hQ
  have harg : 4 * (m : ℝ) * b * (8 * (layoutQ m : ℝ)) ^
        (2 * layoutCutoff m b) + 1 ≤
      4 * (m : ℝ) * (L m ^ q : ℕ) * (8 * (layoutQ m : ℝ)) ^
        (2 * layoutCutoff m (L m ^ q)) + 1 := by
    gcongr
    linarith
  exact (Real.log_le_log (by positivity) harg).trans hm

theorem eventually_residual_label_log (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m b : ℕ, m ≤ n → n ≤ 2 * m → 1 ≤ b → b ≤ L m ^ q →
      Real.log (4 * (m : ℝ) * b * (8 * (layoutQ m : ℝ)) ^
        (2 * layoutCutoff m b) + 1) ≤ 4 * (L n : ℝ) ^ 2 := by
  filter_upwards [eventually_uniform_half (eventually_uniform_label_log q)] with n hn m b hmn hnm hb0 hb
  exact (hn m hnm b hb0 hb).trans (by gcongr; exact_mod_cast L_mono hmn)

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
