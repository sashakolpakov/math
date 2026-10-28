import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

noncomputable section
namespace OAI.Analysis.PDE.Energy

/-- The finite-sum step in the rank-dependent energy comparison.
All analytic input is isolated in the nonnegative mixed masses, their
upper bound by the zeroth mass, and the exact determinant expansion. -/
theorem rank_energy_scalar_bounds (m r : ℕ) (_ : r < m)
    {Λ X E : ℝ} (hΛ : 0 < Λ) (I : ℕ → ℝ)
    (hI0 : I 0 = Λ * X)
    (hI : ∀ j ∈ Finset.range (r+1), 0 ≤ I j ∧ I j ≤ I 0)
    (hE : E = X - (∑ j ∈ Finset.range (r+1), I j) / (Λ * (m+1))) :
    ((m : ℝ)-r)/(m+1)*X ≤ E ∧ E ≤ (m : ℝ)/(m+1)*X := by
  have hm : 0 < (m : ℝ)+1 := by positivity
  have hden : 0 < Λ * ((m : ℝ)+1) := mul_pos hΛ hm
  have hzero : 0 ∈ Finset.range (r+1) := Finset.mem_range.mpr (Nat.zero_lt_succ r)
  have hlower : Λ*X ≤ ∑ j ∈ Finset.range (r+1), I j := by
    rw [← hI0]
    exact Finset.single_le_sum (fun j hj => (hI j hj).1) hzero
  have hupper : (∑ j ∈ Finset.range (r+1), I j) ≤ ((r : ℝ)+1)*(Λ*X) := by
    calc
      (∑ j ∈ Finset.range (r+1), I j) ≤ ∑ _j ∈ Finset.range (r+1), I 0 :=
        Finset.sum_le_sum (fun j hj => (hI j hj).2)
      _ = ((r : ℝ)+1)*(Λ*X) := by simp [hI0]
  have hquotlow : X / ((m : ℝ)+1) ≤
      (∑ j ∈ Finset.range (r+1), I j) / (Λ*((m : ℝ)+1)) := by
    apply (le_div_iff₀ hden).mpr
    convert hlower using 1
    field_simp
  have hquothigh : (∑ j ∈ Finset.range (r+1), I j) / (Λ*((m : ℝ)+1)) ≤
      (((r : ℝ)+1)*X) / ((m : ℝ)+1) := by
    apply (div_le_iff₀ hden).mpr
    convert hupper using 1
    field_simp
  have hidlow : X - (((r : ℝ)+1)*X)/((m : ℝ)+1) =
      ((m : ℝ)-r)/(m+1)*X := by field_simp; ring
  have hidup : X - X/((m : ℝ)+1) = (m : ℝ)/(m+1)*X := by field_simp; ring
  rw [hE]
  constructor
  · rw [← hidlow]
    exact sub_le_sub_left hquothigh X
  · rw [← hidup]
    exact sub_le_sub_left hquotlow X

end OAI.Analysis.PDE.Energy
