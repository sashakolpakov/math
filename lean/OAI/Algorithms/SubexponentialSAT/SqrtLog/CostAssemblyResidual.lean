import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblySupport
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticResidualJet

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology BigOperators
open Asymptotic

/-- Removing variables does not increase the exact squarefree support count. -/
theorem support_count_mono {m n : ℕ} (h : m ≤ n) (J : ℕ) :
    SupportProgram.count m J ≤ SupportProgram.count n J := by
  unfold SupportProgram.count
  exact Finset.sum_le_sum (fun j _ => Nat.choose_le_choose j h)

/-- The high-incidence branch retains at least half the variables. Precision
may still use the original ambient n: the mixed-parameter jet lemma and
support monotonicity together recover the ambient target bound. -/
theorem eventually_residual_support_target (m b T : ℕ → ℕ) (k a q : ℕ)
    (hm : ∀ᶠ n:ℕ in atTop, m n ≤ n ∧ n ≤ 2*m n)
    (hb : ∀ᶠ n:ℕ in atTop, b n ≤ L (m n)^q)
    (hT : ∀ᶠ n:ℕ in atTop, T n ≤ a*n) :
    ∀ᶠ n:ℕ in atTop,
      (SupportProgram.count (m n)
        (k*layoutCutoff (m n) (b n)*T n/layoutQ (m n)+1):ℝ) ≤
      (2:ℝ)^((384*((k*a*(256*(28*q+312)):ℕ)+1)+1)*Statement.runtimeScale n) := by
  have hJ := eventually_residual_jet_functions m b T k a q hm hb hT
  have he := eventually_support_target
    (fun n => k*layoutCutoff (m n) (b n)*T n/layoutQ (m n)+1)
    (C := ((k*a*(256*(28*q+312)):ℕ):ℝ)+1)
    (by have : (0:ℝ) ≤ (k*a*(256*(28*q+312)):ℕ) := by positivity
        linarith) hJ
  filter_upwards [hm,he] with n hmn hen
  exact (show (SupportProgram.count (m n)
    (k*layoutCutoff (m n) (b n)*T n/layoutQ (m n)+1):ℝ) ≤
      (SupportProgram.count n
        (k*layoutCutoff (m n) (b n)*T n/layoutQ (m n)+1):ℝ) by
      exact_mod_cast support_count_mono hmn.1 _).trans hen

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
