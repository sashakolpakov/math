import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.IdealTransforms
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceLength
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.BoundaryHistoryExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceHistoryLabels

/-! # Fixed Length Boundary History -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.FixedLengthBoundaryHistory.Construction

noncomputable section

/-! Selected boundary histories use common label types after a prescribed number of steps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def iteratedBoundaryEmbedding : (N : ℕ) → {β γ : Type} → (γ ↪ β) →
    ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N γ ↪ ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β
  | 0, _, _, e => e
  | N + 1, _, _, e => iteratedBoundaryEmbedding N (Function.Embedding.optionMap e)

theorem iteratedBoundaryEmbedding_excludes_initial (N : ℕ) {β γ : Type}
    (e : γ ↪ β) (j : β) (hj : ∀ s, j ≠ e s) :
    ∀ s, ControlPrefix.IdealTransforms.Construction.iteratedInitialBoundaryEmbedding N β j ≠ Construction.iteratedBoundaryEmbedding N e s := by
  induction N generalizing β γ with
  | zero => exact hj
  | succ N ih => exact ih (Function.Embedding.optionMap e) (some j) (Finite.BoundaryHistoryExtension.Construction.excluded_boundary_label_optionMap e j hj)

def iteratedExtendedBoundaryHistory (N : ℕ) {β γ : Type} (e : γ ↪ β) (j : β) (hj : ∀ s, j ≠ e s) :
    Option (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N γ) ↪ ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β :=
  Finite.BoundaryHistoryExtension.Construction.extendSelectedBoundaryHistory (Construction.iteratedBoundaryEmbedding N e) (ControlPrefix.IdealTransforms.Construction.iteratedInitialBoundaryEmbedding N β j)
    (iteratedBoundaryEmbedding_excludes_initial N e j hj)

theorem iteratedExtendedBoundaryHistory_missing_count_lt (N : ℕ) {β γ : Type} [Fintype β] [Fintype γ]
    (e : γ ↪ β) (j : β) (hj : ∀ s, j ≠ e s) :
    Fintype.card (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β) - Fintype.card (Option (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N γ)) <
      Fintype.card β - Fintype.card γ := by
  have h := Finite.BoundaryHistoryExtension.Construction.remaining_boundary_count_extend_lt (Construction.iteratedBoundaryEmbedding N e) (ControlPrefix.IdealTransforms.Construction.iteratedInitialBoundaryEmbedding N β j)
    (iteratedBoundaryEmbedding_excludes_initial N e j hj)
  simpa only [Uniform.IncidenceSurfaceLength.Construction.card_iteratedBoundaryLabels, Fintype.card_option, Nat.add_sub_add_right] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.FixedLengthBoundaryHistory.Construction
