import OAI.Analysis.PDE.Weak.Elliptic.H1

noncomputable section
open Set _root_.MeasureTheory
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

def traceLower (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (j : Fin (m + 1)) (r t : ℝ) : OAI.Analysis.PDE.Variational.CellCoordinates m :=
  Function.update (fun i ↦ x i - r) j t

def traceUpper (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (j : Fin (m + 1)) (r t : ℝ) : OAI.Analysis.PDE.Variational.CellCoordinates m :=
  Function.update (fun i ↦ x i + r) j t

theorem traceLower_le_traceUpper (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (j : Fin (m + 1))
    {r s t : ℝ} (hr : 0 ≤ r) (hst : s ≤ t) : traceLower x j r s ≤ traceUpper x j r t := by
  intro i
  by_cases hij : i = j
  · subst i
    simpa [traceLower, traceUpper] using hst
  · simp only [traceLower, traceUpper, Function.update_of_ne hij]
    linarith

theorem traceBox_volume (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (j : Fin (m + 1))
    {r s t : ℝ} (hr : 0 ≤ r) (hst : s ≤ t) :
    volume.real (Icc (traceLower x j r s) (traceUpper x j r t)) = (t - s) * (2 * r) ^ m := by
  rw [Measure.real, Real.volume_Icc_pi_toReal (traceLower_le_traceUpper x j hr hst),
    Fin.prod_univ_succAbove _ j]
  simp only [traceLower, traceUpper, Function.update_self]
  have h (i : Fin m) : j.succAbove i ≠ j := j.succAbove_ne i
  simp only [Function.update_of_ne (h _)]
  simp_rw [show ∀ i : Fin m, x (j.succAbove i) + r - (x (j.succAbove i) - r) = 2 * r by
    intro i; ring]
  simp

theorem traceBox_subset_closedBall (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (j : Fin (m + 1))
    (hx : x j = 0) {r s t : ℝ} (hr : 0 ≤ r) (hs : -r ≤ s) (ht : t ≤ r) :
    Icc (traceLower x j r s) (traceUpper x j r t) ⊆ Metric.closedBall x r := by
  intro y hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  rw [Real.norm_eq_abs, abs_le]
  have hlo := hy.1 i
  have hhi := hy.2 i
  by_cases hij : i = j
  · subst i
    simp only [traceLower, traceUpper, Function.update_self] at hlo hhi
    simp only [Pi.sub_apply, hx, sub_zero]
    exact ⟨hs.trans hlo, hhi.trans ht⟩
  · simp only [traceLower, traceUpper, Function.update_of_ne hij] at hlo hhi
    simp only [Pi.sub_apply]
    constructor <;> linarith

theorem traceBox_positive (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (j : Fin (m + 1))
    {r s t : ℝ} (hs : 0 < s) :
    Icc (traceLower x j r s) (traceUpper x j r t) ⊆ {y | 0 < y j} := by
  intro y hy
  have hlo := hy.1 j
  simp only [traceLower, Function.update_self] at hlo
  exact hs.trans_le hlo

theorem traceBox_mono_lower (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (j : Fin (m + 1))
    {r s s' t : ℝ} (hss : s ≤ s') :
    Icc (traceLower x j r s') (traceUpper x j r t) ⊆
      Icc (traceLower x j r s) (traceUpper x j r t) := by
  apply Icc_subset_Icc _ le_rfl
  intro i
  by_cases hij : i = j
  · subst i
    simpa [traceLower] using hss
  · simp [traceLower, hij]

end OAI.Analysis.PDE.Weak
