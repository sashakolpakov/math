import OAI.Analysis.PDE.Elliptic.FrameCompletion

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

/-- The finite-direction comparison used in the Evans--Krylov argument.
A lower bound on a positive weighted difference controls each deficit at
the first point by the sum of the deficits at the second point. -/
theorem weighted_deficit_comparison {I : Type*} [Fintype I]
    (a M x y : I → ℝ) {δ C e : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ i, δ ≤ a i ∧ a i ≤ C)
    (hx : ∀ i, x i ≤ M i) (hy : ∀ i, y i ≤ M i)
    (hrel : -e ≤ ∑ i, a i * (x i - y i)) (k : I) :
    δ * (M k - x k) ≤ C * (∑ i, (M i - y i)) + e := by
  classical
  have ha0 (i) : 0 ≤ a i := hδ.trans (ha i).1
  have hfirst : δ * (M k - x k) ≤ ∑ i, a i * (M i - x i) := by
    calc
      _ ≤ a k * (M k - x k) :=
        mul_le_mul_of_nonneg_right (ha k).1 (sub_nonneg.mpr (hx k))
      _ ≤ ∑ i, a i * (M i - x i) :=
        Finset.single_le_sum (fun i _ ↦ mul_nonneg (ha0 i) (sub_nonneg.mpr (hx i)))
          (Finset.mem_univ k)
  have hsecond : (∑ i, a i * (M i - y i)) ≤ C * (∑ i, (M i - y i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_right (ha i).2 (sub_nonneg.mpr (hy i))
  have hid : (∑ i, a i * (M i - x i)) + (∑ i, a i * (x i - y i)) =
      ∑ i, a i * (M i - y i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

end OAI.Analysis.PDE.Elliptic
