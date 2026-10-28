import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceReindex
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.AuxiliaryPrefixBoundary

/-! # Incidence Trace Carrier -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Retaining a distinguished carrier gives an explicit, scheme-independent update of the whole incidence trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.adjoinCarrier {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β) :
    [Fintype β] → Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace (Option β) := by
  induction T with
  | stop β => intro _; exact .stop (Option β)
  | @step β F tail ih =>
      intro _
      classical
      let R : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace (Option (Option β)) := ih
      exact .step (insert none (F.image some)) (R.reindex _ GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels.toEmbedding)

theorem Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.adjoinCarrier_length {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β) [Fintype β] :
    T.adjoinCarrier.length = T.length := by
  revert ‹Fintype β›
  induction T with
  | stop => intro _; rfl
  | @step β F tail ih =>
      intro _
      change ((tail.adjoinCarrier).reindex _ GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels.toEmbedding).length + 1 = tail.length + 1
      rw [Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.reindex_length]
      exact congrArg (fun a : ℕ => a + 1) ih

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.carrier_to_canonical
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {I H : X.IdealSheafData} (hI : I ≠ ⊥) {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    {b : ℕ} {J : (GlobalBlowup.Data.Construction.globalBlowup I hI).IdealSheafData} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) J Y g K)
    (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace (Option (Option β)))
    (hP : P.HasIncidenceTrace (Option (Option β))
      (fun j => match j with
        | none => GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
        | some l => CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l) T) :
    P.HasIncidenceTrace (Option (Option β))
      (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI (fun j : Option β => match j with | none => H | some l => D l))
      (T.reindex _ GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels.toEmbedding) := by
  let E : Option (Option β) → (GlobalBlowup.Data.Construction.globalBlowup I hI).IdealSheafData := fun j => match j with
    | none => GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
    | some l => CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l
  have ht := hP.reindex P _ _ E T GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels.toEmbedding
  change P.HasIncidenceTrace (Option (Option β)) (fun l => E (GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels l))
    (T.reindex _ GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels.toEmbedding) at ht
  have he : (fun l => E (GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels l)) =
      CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI (fun j : Option β => match j with | none => H | some l => D l) := by
    funext j
    rcases j with _ | (_ | j) <;> rfl
  rw [he] at ht
  exact ht

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.adjoin_auxiliary_carrier
    {m : ℕ} (hm : 0 < m) {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {K : X.IdealSheafData} {L : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f K Y g L) :
    ∀ [Smooth f] (J H : X.IdealSheafData), K = GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H m →
      ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β),
      P.HasIncidenceTrace β D T →
      Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f
        (fun j : Option β => match j with | none => H | some l => D l) [Finset.univ] →
      P.HasIncidenceTrace (Option β) (fun j : Option β => match j with | none => H | some l => D l) T.adjoinCarrier := by
  induction P with
  | stop =>
      intro _ _ H _ β _ D T hP A
      cases T with
      | stop => exact ⟨A⟩
      | step => exact False.elim hP
  | @blowup X hX hNX f K I hI hb hp hs hbl Y g L tail ih =>
      intro hf J H hK β _ D T hP Afull
      classical
      let : Smooth f := hf
      let : Smooth (I.subschemeι ≫ f) := hs
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
      cases T with
      | stop => exact False.elim hP
      | step F rest =>
          obtain ⟨hJ, hHI⟩ := (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_smooth_center_iff f I J H m hm).mp (hK ▸ hp)
          obtain ⟨A, hF⟩ := hP.1
          obtain ⟨AA, hAA⟩ := A.exists_adjoin_uniform_boundary_component F hF H hHI Afull
          let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D
          let J' := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m
          let H' := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
          have hnext : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I K hI m = GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J' H' m := by
            rw [hK, GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_transform I J H hI m hJ hHI]
          have htail := ih J' H' hnext (Option β) D' rest hP.2
            (by convert AA.blowupBoundaryWithCarrier hI using 1; funext j; cases j <;> rfl)
          refine ⟨⟨AA, hAA⟩, ?_⟩
          apply Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.carrier_to_canonical (H := H) hI D tail rest.adjoinCarrier
          convert htail using 1
          funext j
          cases j <;> rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups
