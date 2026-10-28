import OAI.AlgebraicGeometry.Resolution.Blowups.FixedLengthBoundaryHistory
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SelectedLogarithmicBlowup

/-! # Logarithmic History -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Arbitrary contained marked ideals retain their selected logarithmic histories along actual prefixes with fixed endpoint labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_canonical_logarithmic_history
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {K : X.IdealSheafData} {L : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f K Y g L) :
    ∀ [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
      (β : Type) [Fintype β] (D : β → X.IdealSheafData), P.boundaryCompatible β D →
      ∀ (B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (γ : Type) [Fintype γ] (e : γ ↪ β)
        (H : X.IdealSheafData), H ≤ K → (B.reindex e).logarithmicIdeal H b = ⊤ →
      ∃ C : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas g (P.canonicalBoundary D),
        (C.reindex (FixedLengthBoundaryHistory.Construction.iteratedBoundaryEmbedding P.stepCount e)).logarithmicIdeal (P.transformIdeal H b) b = ⊤ := by
  induction P with
  | stop =>
      intro _ _ _ β _ D _ B γ _ e H _ hb
      exact ⟨B, hb⟩
  | @blowup X hX hNX f K I hI hb hp hs hbl Y g L tail ih =>
      intro _ _ hcompact β _ D hP B γ _ e H hHK hbound
      let : CompactSpace X := hcompact
      let : CompactSpace (GlobalBlowup.Data.Construction.globalBlowup I hI) := QuasiCompact.compactSpace_of_compactSpace (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
      obtain ⟨A⟩ := hP.1
      obtain ⟨B'⟩ := (A.blowupBoundary hI).exists_modelAtlas
      have hnew := Global.SelectedLogarithmicBlowup.Construction.globalBlowup_preserves_selected_logarithmic_order_bound I H hI D e A B B' b
        (hHK.trans hp) hbound
      exact ih (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) hP.2 B'
        (Option γ) (Function.Embedding.optionMap e) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI b)
        (Global.HomogenizedTransform.Construction.globalBlowupControlledIdeal_mono I hI b hHK) hnew

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_fixed_length_logarithmic_history
    {b : ℕ} {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : X.IdealSheafData} {L : Y.IdealSheafData}
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f K Y g L)
    {β γ : Type} [Fintype β] [Fintype γ] (D : β → X.IdealSheafData) (hP : P.boundaryCompatible β D)
    (B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (e : γ ↪ β) (H : X.IdealSheafData)
    (hHK : H ≤ K) (hbound : (B.reindex e).logarithmicIdeal H b = ⊤) (N : ℕ) (hN : P.stepCount = N) :
    ∃ C : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas g (P.boundaryAtLength D N hN),
      (C.reindex (FixedLengthBoundaryHistory.Construction.iteratedBoundaryEmbedding N e)).logarithmicIdeal (P.transformIdeal H b) b = ⊤ := by
  subst N
  exact P.exists_canonical_logarithmic_history β D hP B γ e H hHK hbound

end

end OAI.AlgebraicGeometry.Resolution.Blowups
