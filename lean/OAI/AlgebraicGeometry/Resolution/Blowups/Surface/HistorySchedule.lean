import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.AuxiliaryProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.FixedLengthBoundaryHistory

/-! # History Schedule -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface

noncomputable section

/-! A common schedule fixes all history labels, coefficient levels, and intermediate boundary label types. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

instance HistorySchedule.Construction.iteratedBoundaryLabels_decidableEq (N : ℕ) (β : Type) [DecidableEq β] :
    DecidableEq (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β) := by
  induction N generalizing β with
  | zero => exact inferInstanceAs (DecidableEq β)
  | succ N ih => exact ih (Option β)

def HistorySchedule.Construction.surfaceAuxiliaryProgramStepCount (n ℓ k : ℕ) : ℕ :=
  LogarithmicProgram.Construction.surfaceLogarithmicProgramStepCount n ℓ (k - 1)

theorem AuxiliaryProgram.Construction.SurfaceAuxiliaryProgram.stepCount
    {n ℓ : ℕ} {β : Type} [Fintype β] [DecidableEq β] {X Y : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData} {j : β}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K}
    (T : AuxiliaryProgram.Construction.SurfaceAuxiliaryProgram n ℓ β X f J D j Y g K P) :
    P.stepCount = HistorySchedule.Construction.surfaceAuxiliaryProgramStepCount n ℓ (Fintype.card β) := by
  have h := LogarithmicProgram.Construction.SurfaceLogarithmicProgram.stepCount T
  have hcard : Fintype.card {l : β // l ≠ j} = Fintype.card β - 1 := by
    have he := Fintype.card_congr (Equiv.optionSubtypeNe j)
    rw [Fintype.card_option] at he
    omega
  change P.stepCount = LogarithmicProgram.Construction.surfaceLogarithmicProgramStepCount n ℓ (Fintype.card {l : β // l ≠ j}) at h
  rw [hcard] at h
  exact h

inductive HistorySchedule.Construction.SurfaceHistorySchedule (n : ℕ) :
    {β γ : Type} → [Fintype β] → [Fintype γ] → [DecidableEq β] → (γ ↪ β) → Type 1
  | full {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] (e : γ ↪ β)
      (he : Function.Surjective e) (ℓ : ℕ) : SurfaceHistorySchedule n e
  | clear {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] (e : γ ↪ β)
      (j : β) (hj : ∀ s, j ≠ e s) (ℓ : ℕ)
      (tail : SurfaceHistorySchedule n
        (FixedLengthBoundaryHistory.Construction.iteratedExtendedBoundaryHistory (HistorySchedule.Construction.surfaceAuxiliaryProgramStepCount n ℓ (Fintype.card β)) e j hj)) :
      SurfaceHistorySchedule n e

def HistorySchedule.Construction.SurfaceHistorySchedule.stepCount {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β]
    {e : γ ↪ β} (S : HistorySchedule.Construction.SurfaceHistorySchedule n e) : ℕ := by
  induction S with
  | @full β γ _ _ _ e he ℓ => exact LogarithmicProgram.Construction.surfaceLogarithmicProgramStepCount n ℓ (Fintype.card β)
  | @clear β γ _ _ _ e j hj ℓ tail ih => exact HistorySchedule.Construction.surfaceAuxiliaryProgramStepCount n ℓ (Fintype.card β) + ih

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface
