import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ControlBoundaryEndpoint

/-! # Sequence History Labels -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! A selected history keeps exactly the original omitted labels through every actual blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def MonomialSequence.Construction.SmoothFixedControlSequence.endpointHistoryEmbedding {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) {β γ : Type} (e : γ ↪ β) :
    T.endpointLabels γ ↪ T.endpointLabels β :=
  match T with
  | @MonomialSequence.Construction.SmoothFixedControlSequence.terminal _ _ _ _ _ _ => e
  | @MonomialSequence.Construction.SmoothFixedControlSequence.blowup _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.endpointHistoryEmbedding (Function.Embedding.optionMap e)

theorem MonomialSequence.Construction.SmoothFixedControlSequence.endpointHistoryEmbedding_initialLabel
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) {β γ : Type} (e : γ ↪ β) (j : γ) :
    T.endpointHistoryEmbedding e (T.initialLabelEmbedding γ j) = T.initialLabelEmbedding β (e j) := by
  induction T generalizing β γ with
  | terminal => rfl
  | blowup I hI hb hp hs hbl tail ih => exact ih (Function.Embedding.optionMap e) (some j)

theorem MonomialSequence.Construction.SmoothFixedControlSequence.endpointHistory_missing_count
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) (β γ : Type) [Fintype β] [Fintype γ] :
    Fintype.card (T.endpointLabels β) - Fintype.card (T.endpointLabels γ) = Fintype.card β - Fintype.card γ := by
  induction T generalizing β γ with
  | terminal => rfl
  | blowup I hI hb hp hs hbl tail ih =>
      change Fintype.card (tail.endpointLabels (Option β)) - Fintype.card (tail.endpointLabels (Option γ)) = _
      rw [ih, Fintype.card_option, Fintype.card_option]
      omega

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
