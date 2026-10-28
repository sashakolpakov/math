import OAI.Analysis.PDE.Schauder.Calculus.Boundary.MollifierEstimates

/-! The smoothing estimates in the nested Fréchet-derivative convention. -/

noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

local instance smoothingFirstGroup (m : ℕ) : NormedAddCommGroup ((ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) := inferInstance
local instance smoothingFirstSpace (m : ℕ) : NormedSpace ℝ ((ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) := inferInstance
local instance smoothingSecondGroup (m : ℕ) : NormedAddCommGroup ((ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) := inferInstance
local instance smoothingSecondSpace (m : ℕ) : NormedSpace ℝ ((ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) := inferInstance
local instance smoothingThirdGroup (m : ℕ) : NormedAddCommGroup ((ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) := inferInstance

theorem exists_regularizedTrace_three_derivative_bound (m : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    ∃ C > 0, ∀ h : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α,
      ∀ (p : ℝ × EuclideanSpace ℝ (Fin m)), p.1 ≠ 0 →
      let S := fun q : ℝ × EuclideanSpace ℝ (Fin m) => regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) q.1 q.2
      ‖fderiv ℝ S p‖ ≤ C * ‖h‖ * |p.1| ^ (α - 1) ∧
      ‖fderiv ℝ (fderiv ℝ S) p‖ ≤ C * ‖h‖ * |p.1| ^ (α - 2) ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ S)) p‖ ≤ C * ‖h‖ * |p.1| ^ (α - 3) := by
  obtain ⟨C, hC, hb⟩ := exists_regularizedTrace_holder_derivative_bound m hα
  refine ⟨C, hC, ?_⟩
  intro h p hp
  dsimp only
  have h₁ := hb h p hp 1 (by omega) (by omega)
  have h₂ := hb h p hp 2 (by omega) (by omega)
  have h₃ := hb h p hp 3 (by omega) (by omega)
  simp only [norm_iteratedFDeriv_one, Nat.cast_one] at h₁
  rw [show 2 = 1 + 1 by rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h₂
  rw [show 3 = 2 + 1 by rfl, ← norm_iteratedFDeriv_fderiv,
    show 2 = 1 + 1 by rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h₃
  exact ⟨h₁, by norm_num only [Nat.cast_add, Nat.cast_one] at h₂; exact h₂,
    by norm_num only [Nat.cast_add, Nat.cast_one] at h₃; exact h₃⟩

end OAI.Analysis.PDE.Schauder
