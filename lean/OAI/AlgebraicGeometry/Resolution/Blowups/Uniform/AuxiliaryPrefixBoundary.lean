import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.ContainedBoundaryComponent
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.PrefixBoundaryReindex
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Labels
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.AuxiliarySequence

/-! # Auxiliary Prefix Boundary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! An auxiliary prefix retains the distinguished carrier boundary with constant incidence at every actual center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible_carrier_to_canonical
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {I H : X.IdealSheafData} (hI : I ≠ ⊥) {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    {b : ℕ} {J : (GlobalBlowup.Data.Construction.globalBlowup I hI).IdealSheafData} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) J Y g K)
    (hP : P.uniformBoundaryCompatible (Option (Option β))
      (fun j => match j with
        | none => GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
        | some l => CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l)) :
    P.uniformBoundaryCompatible (Option (Option β))
      (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI (fun j : Option β => match j with | none => H | some l => D l)) := by
  let E : Option (Option β) → (GlobalBlowup.Data.Construction.globalBlowup I hI).IdealSheafData :=
    fun j => match j with
      | none => GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
      | some l => CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l
  have ht := P.uniformBoundaryCompatible_reindex (Option (Option β)) (Option (Option β)) E hP
    GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels.toEmbedding
  change P.uniformBoundaryCompatible (Option (Option β)) (fun l => E (GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels l)) at ht
  have he : (fun l => E (GlobalBoundary.Labels.Construction.swapFirstBoundaryLabels l)) =
      CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI (fun j : Option β => match j with | none => H | some l => D l) := by
    funext j
    rcases j with _ | (_ | j) <;> rfl
  rw [he] at ht
  exact ht

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible_adjoin_auxiliary_carrier
    {m : ℕ} (hm : 0 < m) {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {K : X.IdealSheafData} {L : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f K Y g L) :
    ∀ [Smooth f] (J H : X.IdealSheafData), K = GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H m →
      ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData), P.uniformBoundaryCompatible β D →
      Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f
        (fun j : Option β => match j with | none => H | some l => D l) [Finset.univ] →
      P.uniformBoundaryCompatible (Option β) (fun j : Option β => match j with | none => H | some l => D l) := by
  induction P with
  | stop =>
      intro _ _ H _ β _ D _ A
      exact ⟨A⟩
  | @blowup X hX hNX f K I hI hb hp hs hbl Y g L tail ih =>
      intro hf J H hK β _ D hB Afull
      classical
      let : Smooth f := hf
      let : Smooth (I.subschemeι ≫ f) := hs
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
      obtain ⟨hJ, hHI⟩ := (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_smooth_center_iff f I J H m hm).mp (hK ▸ hp)
      obtain ⟨A, F, hF⟩ := hB.1
      obtain ⟨AA, hAA⟩ := A.exists_adjoin_uniform_boundary_component F hF H hHI Afull
      let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D
      let J' := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m
      let H' := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
      have hnext : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I K hI m = GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J' H' m := by
        rw [hK, GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_transform I J H hI m hJ hHI]
      have htail := ih J' H' hnext (Option β) D' hB.2
        (by convert AA.blowupBoundaryWithCarrier hI using 1; funext j; cases j <;> rfl)
      refine ⟨⟨AA, insert none (F.image some), hAA⟩, ?_⟩
      apply tail.uniformBoundaryCompatible_carrier_to_canonical (H := H) hI D
      convert htail using 1
      funext j
      cases j <;> rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups
