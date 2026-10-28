import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBudget

namespace OAI.Algorithms

/-! A single proof-only rank parameter for finitely many nodes or queries.
The maximum is used only in the analysis of attained signatures; it does not
require a runtime row-basis computation or bound the number of stored rows. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open scoped BigOperators

/-- A finite maximum preserves an exact real-valued rank budget. -/
theorem finite_rank_budget {X : Type*} (nodes : Finset X) (rank : X → ℕ)
    (a b : ℝ) (hb : 0 ≤ b)
    (h : ∀ x ∈ nodes, a * (rank x : ℝ) ≤ b) :
    a * ((nodes.sup rank : ℕ) : ℝ) ≤ b := by
  rcases nodes.eq_empty_or_nonempty with he | hn
  · simpa only [he, Finset.sup_empty, Nat.bot_eq_zero, Nat.cast_zero, mul_zero] using hb
  · obtain ⟨x, hx, hmax⟩ := Finset.exists_mem_eq_sup nodes hn rank
    rw [hmax]
    exact h x hx

def maxTotalRank {X G : Type*} [Fintype G]
    (nodes : Finset X) (rank : X → G → ℕ) : ℕ :=
  nodes.sup (fun x => ∑ g, rank x g)

theorem totalRank_le_max {X G : Type*} [Fintype G]
    (nodes : Finset X) (rank : X → G → ℕ) {x : X} (hx : x ∈ nodes) :
    (∑ g, rank x g) ≤ maxTotalRank nodes rank := by
  change (∑ g, rank x g) ≤ nodes.sup (fun y => ∑ g, rank y g)
  exact Finset.le_sup (f := fun y => ∑ g, rank y g) hx

/-- Node- or query-dependent masses and ranks may share one exact cost
parameter whenever every mass obeys the same scheduled budget. -/
theorem scheduled_maxTotalRank_le_real {X G : Type*} [Fintype G]
    (nodes : Finset X) (n B : ℕ) (mass : X → ℕ) (rank : X → G → ℕ)
    (hB : 0 < B) (hM : ∀ x ∈ nodes, mass x ≤ B * n)
    (hrank : ∀ x ∈ nodes, (∑ g, (rank x g : ℚ)) ≤
      2 * Asymptotic.layoutEpsilon n B * mass x) :
    16 * (Asymptotic.layoutR n : ℝ) * (Asymptotic.L n : ℝ)^2 *
      (maxTotalRank nodes rank : ℝ) ≤ n := by
  apply finite_rank_budget nodes (fun x => ∑ g, rank x g)
    (16 * (Asymptotic.layoutR n : ℝ) * (Asymptotic.L n : ℝ)^2) n (by positivity)
  intro x hx
  simpa only [Nat.cast_sum] using
    LayoutBudget.scheduled_total_rank_le_real n (mass x) B (rank x)
      hB (hM x hx) (hrank x hx)

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
