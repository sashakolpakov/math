import OAI.Analysis.PDE.Weak.Elliptic.H1
import Mathlib.Analysis.Calculus.ContDiff.WithLp

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

theorem contDiff_cellGradient {m : ℕ} {η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hη : ContDiff ℝ ∞ η) : ContDiff ℝ ∞ (OAI.Analysis.PDE.Variational.cellGradient η) := by
  apply (contDiff_piLp 2).mpr
  intro i
  change ContDiff ℝ ∞ (fun x ↦ fderiv ℝ η x (Pi.single i 1))
  exact (hη.fderiv_right (by simp)).clm_apply contDiff_const

theorem exists_cellGradient_derivative_bound {m : ℕ} {η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ x, ‖fderiv ℝ (OAI.Analysis.PDE.Variational.cellGradient η) x‖ ≤ J := by
  have hg := contDiff_cellGradient hη
  have hgs := hasCompactSupport_cellGradient hs
  obtain ⟨J, hJ⟩ := ((hgs.fderiv (𝕜 := ℝ)).isCompact_range
    (hg.continuous_fderiv (by simp))).isBounded.exists_norm_le
  have hJ' : ∀ x, ‖fderiv ℝ (OAI.Analysis.PDE.Variational.cellGradient η) x‖ ≤ J := fun x ↦ hJ _ (mem_range_self x)
  exact ⟨J, (norm_nonneg _).trans (hJ' 0), hJ'⟩

end OAI.Analysis.PDE.Weak
