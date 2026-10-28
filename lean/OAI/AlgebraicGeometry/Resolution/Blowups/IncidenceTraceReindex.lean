import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Labels

/-! # Incidence Trace Reindex -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Injective relabelling preserves an exact incidence trace with the corresponding pulled-back finite sets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.reindex {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β) :
    (γ : Type) → [Fintype γ] → (γ ↪ β) → Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace γ := by
  induction T with
  | stop => intro γ _ _; exact .stop γ
  | step F tail ih =>
      intro γ _ e
      classical
      exact .step (Finset.univ.filter (fun j => e j ∈ F)) (ih (Option γ) (Function.Embedding.optionMap e))

theorem Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.reindex_length {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (γ : Type) [Fintype γ] (e : γ ↪ β) : (T.reindex γ e).length = T.length := by
  induction T generalizing γ with
  | stop => rfl
  | step F tail ih => exact congrArg (fun a : ℕ => a + 1) (ih (Option γ) (Function.Embedding.optionMap e))

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.reindex
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ (β γ : Type) [Fintype β] [Fintype γ] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β),
      P.HasIncidenceTrace β D T → ∀ e : γ ↪ β,
        P.HasIncidenceTrace γ (fun l => D (e l)) (T.reindex γ e) := by
  induction P with
  | stop =>
      intro β γ _ _ D T hP e
      cases T with
      | step => exact False.elim hP
      | stop =>
          obtain ⟨A⟩ := hP
          refine ⟨A.pullbackLabels (fun j => some (e j)) ?_ (fun j => D (e j)) (fun _ => rfl)⟩
          intro i j s hi hj
          exact e.injective (Option.some_injective _ (hi.trans hj.symm))
  | blowup I hI hb hp hs hbl tail ih =>
      intro β γ _ _ D T hP e
      classical
      cases T with
      | stop => exact False.elim hP
      | step F rest =>
          obtain ⟨A, hF⟩ := hP.1
          have he : ∀ i j s, some (e i) = some s → some (e j) = some s → i = j := by
            intro i j s hi hj
            exact e.injective (Option.some_injective _ (hi.trans hj.symm))
          let A' := A.pullbackLabels (fun j => some (e j)) he (fun j => D (e j)) (fun _ => rfl)
          refine ⟨⟨A', ?_⟩, ?_⟩
          · intro i
            change Finset.univ.filter (fun j => ∃ s ∈ A.divided i, some (e j) = some s) = _
            rw [hF i]
            ext j
            simp
          · let e' := Function.Embedding.optionMap e
            have ht := ih (Option β) (Option γ) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) rest hP.2 e'
            have heq : CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI (fun l => D (e l)) =
                (fun l => CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D (e' l)) := by
              funext j
              cases j <;> rfl
            change tail.HasIncidenceTrace (Option γ) _ (rest.reindex (Option γ) e')
            rw [heq]
            exact ht

end

end OAI.AlgebraicGeometry.Resolution.Blowups
