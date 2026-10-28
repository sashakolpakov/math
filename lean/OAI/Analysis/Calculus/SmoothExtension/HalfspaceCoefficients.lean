import OAI.Analysis.Calculus.SmoothExtension.HalfspaceMoments
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Countably many reflection coefficients matching every normal jet. -/
noncomputable section
open scoped BigOperators
open Filter
namespace OAI.Analysis.Calculus.SmoothExtension

def momentScale (n : ℕ) (c : ℝ) : ℝ :=
  (exists_scale_small_moments n c ((1/2:ℝ)^n) (by positivity)).choose

theorem momentScale_ge_one (n : ℕ) (c : ℝ) : 1 ≤ momentScale n c :=
  (exists_scale_small_moments n c ((1/2:ℝ)^n) (by positivity)).choose_spec.1

def blockWeight (n : ℕ) (c : ℝ) (j : Fin (n+1)) : ℝ :=
  scaledMomentWeight n c (momentScale n c) j

def blockNode (n : ℕ) (c : ℝ) (j : Fin (n+1)) : ℝ :=
  scaledMomentNode n (momentScale n c) j

def blockMoment (n : ℕ) (c : ℝ) (q : ℕ) : ℝ :=
  ∑ j : Fin (n+1), blockWeight n c j * blockNode n c j ^ q

theorem blockMoment_eq (n : ℕ) (c : ℝ) (q : ℕ) (hq : q ≤ n) :
    blockMoment n c q = if q=n then c else 0 :=
  scaledMomentWeight_moment n q hq c (momentScale n c)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (momentScale_ge_one n c)))

theorem block_abs_moment_small (n : ℕ) (c : ℝ) (q : ℕ) (hq : q < n) :
    (∑ j : Fin (n+1), |blockWeight n c j| * |blockNode n c j| ^ q) ≤ (1/2:ℝ)^n :=
  (exists_scale_small_moments n c ((1/2:ℝ)^n) (by positivity)).choose_spec.2 q hq

def momentResidual : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n+1, q => momentResidual n q - blockMoment n (momentResidual n n) q

theorem momentResidual_zero (n q : ℕ) (hq : q < n) : momentResidual n q = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [momentResidual]
    rw [blockMoment_eq n _ q (by omega)]
    by_cases h : q=n
    · simp [h]
    · rw [ite_eq_right h, ih (by omega), sub_zero]

def seeleyWeight (i : Σ n : ℕ, Fin (n+1)) : ℝ :=
  blockWeight i.1 (momentResidual i.1 i.1) i.2

def seeleyNode (i : Σ n : ℕ, Fin (n+1)) : ℝ :=
  blockNode i.1 (momentResidual i.1 i.1) i.2

theorem seeleyNode_le_neg_one (i : Σ n : ℕ, Fin (n+1)) : seeleyNode i ≤ -1 := by
  have hR := momentScale_ge_one i.1 (momentResidual i.1 i.1)
  have hd := one_le_abs_momentNode i.1 i.2
  rw [abs_of_neg (momentNode_neg i.1 i.2)] at hd
  dsimp [seeleyNode,blockNode,scaledMomentNode]
  nlinarith

theorem block_abs_moments_summable (q : ℕ) :
    Summable (fun n : ℕ => ∑ j : Fin (n+1),
      |blockWeight n (momentResidual n n) j| * |blockNode n (momentResidual n n) j|^q) := by
  apply Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_norm_lt_one (show ‖(1/2:ℝ)‖ < 1 by norm_num))
  filter_upwards [eventually_gt_atTop q] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => by positivity))]
  exact block_abs_moment_small n _ q hn

theorem seeley_abs_moment_summable (q : ℕ) :
    Summable (fun i : Σ n : ℕ, Fin (n+1) => |seeleyWeight i| * |seeleyNode i|^q) := by
  apply (summable_sigma_of_nonneg (fun i => by positivity)).2
  constructor
  · intro n
    exact Summable.of_finite
  · simpa only [tsum_fintype,seeleyWeight,seeleyNode] using block_abs_moments_summable q

theorem blockMoment_partial_sum (N q : ℕ) :
    (∑ n ∈ Finset.range N, blockMoment n (momentResidual n n) q) = 1-momentResidual N q := by
  induction N with
  | zero => simp [momentResidual]
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [momentResidual]
    ring

theorem seeley_moment_summable (q : ℕ) :
    Summable (fun i : Σ n : ℕ, Fin (n+1) => seeleyWeight i * seeleyNode i^q) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs,abs_mul,abs_pow] using seeley_abs_moment_summable q

theorem seeley_moment (q : ℕ) :
    (∑' i : Σ n : ℕ, Fin (n+1), seeleyWeight i * seeleyNode i^q) = 1 := by
  rw [(seeley_moment_summable q).tsum_sigma]
  have he : (fun n : ℕ => ∑' j : Fin (n+1), seeleyWeight ⟨n,j⟩ * seeleyNode ⟨n,j⟩^q) =
      fun n => blockMoment n (momentResidual n n) q := by
    funext n
    simp only [tsum_fintype,seeleyWeight,seeleyNode,blockMoment]
  rw [he, tsum_eq_sum (s := Finset.range (q+1))]
  · rw [blockMoment_partial_sum, momentResidual_zero (q+1) q (by omega),sub_zero]
  · intro n hn
    rw [Finset.mem_range] at hn
    rw [blockMoment_eq n _ q (by omega), ite_eq_right (by omega)]

end OAI.Analysis.Calculus.SmoothExtension
