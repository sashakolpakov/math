import OAI.Analysis.PDE.Energy.Rank.Energy.Moments
import OAI.LinearAlgebra.Moore.Rank.Mixed.SegmentIntegral
import OAI.Analysis.PDE.Energy.Rank.Energy.Scalar

noncomputable section
namespace OAI.Analysis.PDE.Energy

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore

/-- Integrating the exact mixed-determinant segment formula gives the sum
of the actual mixed Hessian masses, not a formal energy proxy. -/
theorem determinantSegmentEnergy_eq_mixedHessianMass_sum {n s : ℕ}
    (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u) :
    determinantSegmentEnergy e S B u =
      -(1 / ((n : ℝ)+1)) * ∑ j ∈ Finset.range (n+1), mixedHessianMass e S B u j := by
  unfold determinantSegmentEnergy
  simp_rw [OAI.LinearAlgebra.Moore.integral_mooreDet_segment_mixed]
  exact integral_mixed_hessian_sum e hS hb hB hu _ _

/-- The normalized energy identity after the rank truncation. -/
theorem normalized_energy_eq_truncated_mixed_sum {n s r : ℕ}
    (hr : r ≤ n) (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hzero : ∀ j, r < j → j ≤ n → mixedHessianMass e S B u j = 0)
    (Λ : ℝ) :
    (determinantMass e S (fun y => B y+u y) u + determinantSegmentEnergy e S B u) / Λ =
      determinantMass e S (fun y => B y+u y) u / Λ -
        (∑ j ∈ Finset.range (r+1), mixedHessianMass e S B u j) / (Λ*((n : ℝ)+1)) := by
  rw [determinantSegmentEnergy_eq_mixedHessianMass_sum e hS hb hB hu,
    sum_mixedHessianMass_truncate hr e S B u hzero]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem rank_energy_comparison_of_mixed_moments {n s r : ℕ}
    (hr : r < n) (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hpos : ∀ j, j ≤ n → 0 ≤ mixedHessianMass e S B u j)
    (hstep : ∀ j, j < n → mixedHessianMass e S B u (j+1) ≤ mixedHessianMass e S B u j)
    (hzero : ∀ j, r < j → j ≤ n → mixedHessianMass e S B u j = 0)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    let X := determinantMass e S (fun y => B y+u y) u / Λ
    let E := (determinantMass e S (fun y => B y+u y) u + determinantSegmentEnergy e S B u) / Λ
    ((n : ℝ)-r)/((n : ℝ)+1)*X ≤ E ∧ E ≤ (n : ℝ)/((n : ℝ)+1)*X := by
  dsimp only
  have hle : ∀ j, j ≤ n → mixedHessianMass e S B u j ≤ mixedHessianMass e S B u 0 := by
    intro j
    induction j with
    | zero => intro _; exact le_rfl
    | succ j ih =>
      intro hj
      exact (hstep j (by omega)).trans (ih (by omega))
  apply rank_energy_scalar_bounds n r hr hΛ (mixedHessianMass e S B u)
  · rw [mixedHessianMass_zero]
    exact (mul_div_cancel₀ _ hΛ.ne').symm
  · intro j hj
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    exact ⟨hpos j hjn, hle j hjn⟩
  · exact normalized_energy_eq_truncated_mixed_sum hr.le e hS hb hB hu hzero Λ

end OAI.Analysis.PDE.Energy
