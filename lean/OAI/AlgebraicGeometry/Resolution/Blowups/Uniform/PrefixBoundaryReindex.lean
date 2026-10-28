import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceControlPrefix
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Labels

/-! # Prefix Boundary Reindex -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Injective relabelling preserves constant boundary incidence along the whole actual prefix. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible_reindex
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ (β γ : Type) [Fintype β] [Fintype γ] (D : β → X.IdealSheafData),
      P.uniformBoundaryCompatible β D → ∀ e : γ ↪ β,
        P.uniformBoundaryCompatible γ (fun l => D (e l)) := by
  induction P with
  | stop =>
      intro β γ _ _ D hP e
      obtain ⟨A⟩ := hP
      refine ⟨A.pullbackLabels (fun j => some (e j)) ?_ (fun j => D (e j)) (fun _ => rfl)⟩
      intro i j s hi hj
      exact e.injective (Option.some_injective _ (hi.trans hj.symm))
  | blowup I hI hb hp hs hbl tail ih =>
      intro β γ _ _ D hP e
      classical
      obtain ⟨A, F, hF⟩ := hP.1
      have he : ∀ i j s, some (e i) = some s → some (e j) = some s → i = j := by
        intro i j s hi hj
        exact e.injective (Option.some_injective _ (hi.trans hj.symm))
      let A' := A.pullbackLabels (fun j => some (e j)) he (fun j => D (e j)) (fun _ => rfl)
      refine ⟨⟨A', Finset.univ.filter (fun j => e j ∈ F), ?_⟩, ?_⟩
      · intro i
        change Finset.univ.filter (fun j => ∃ s ∈ A.divided i, some (e j) = some s) = _
        rw [hF i]
        ext j
        simp
      · let e' : Option γ ↪ Option β := ⟨Option.map e, Option.map_injective e.injective⟩
        have ht := ih (Option β) (Option γ) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) hP.2 e'
        have heq : CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI (fun l => D (e l)) =
            (fun l => CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D (e' l)) := by
          funext j
          cases j <;> rfl
        change tail.uniformBoundaryCompatible (Option γ) _
        rw [heq]
        exact ht

end

end OAI.AlgebraicGeometry.Resolution.Blowups
