import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.ControlPrefixOpenExtension

/-! # Incidence Trace Open Descent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The exact incidence trace descends from an order neighborhood to its ambient prefix. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.boundaryCompatible_source_atlas
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (hP : P.boundaryCompatible β D) :
    Nonempty (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) := by
  cases P with
  | stop => exact hP
  | blowup I hI hb hp hs hbl tail =>
      obtain ⟨A⟩ := hP.1
      exact ⟨A.boundaryAtlas⟩

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.hasIncidenceTrace_of_order_neighborhood
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ [Smooth f] {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) [IsOpenImmersion q] (r : W ⟶ Y),
      P.EtaleComparison Q q r →
      ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support : Set X) ⊆ Set.range q →
      ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData)
        (_A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β),
      Q.HasIncidenceTrace β (fun l => (D l).comap q) T → P.HasIncidenceTrace β D T := by
  induction P with
  | stop =>
      intro _ V W h k L M Q q _ r hc hcover β _ D A T hT
      cases Q with
      | blowup => exact False.elim hc
      | stop =>
          cases T with
          | stop => exact ⟨A⟩
          | step => exact False.elim hT
  | @blowup X hX hNX f J I hI hb hp hs hbl Y g K tail ih =>
      intro hf V W h k L M Q q _ r hc hcover β _ D A T hT
      let : Smooth f := hf
      cases Q with
      | stop => exact False.elim hc
      | blowup C hC hbC hpC hsC hblC rest =>
          cases T with
          | stop => exact False.elim hT
          | step F trace =>
              obtain ⟨hq, hstructure, hJ, he, hrest⟩ := hc
              subst h
              obtain ⟨B, hF⟩ := hT.1
              have hlocal : ∃ B' : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (q ≫ f) (I.comap q) (fun l => (D l).comap q),
                  ∀ i, B'.divided i = F := by
                rw [he]
                exact ⟨B, hF⟩
              obtain ⟨B', hF'⟩ := hlocal
              have hsupport : (I.support : Set X) ⊆ Set.range q := by
                have hTI := Global.OrderLocusPreservation.Construction.global_tangent_le_permissible_center f J I (b - 1) ((Nat.sub_add_cancel hb).symm ▸ hp)
                exact fun _ hx => hcover (Scheme.IdealSheafData.support_antitone hTI hx)
              obtain ⟨AC, hAC⟩ := B'.exists_uniform_ofSupportedOpen f q I D A F hF' hsupport
              let q' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C he hI hC
              let : IsOpenImmersion q' := GlobalBlowup.OpenComparison.Construction.globalBlowupMapTo_isOpenImmersion q I C he hI hC
              let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
              have hD : (fun l => (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l).comap q') =
                  CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary C hC (fun l => (D l).comap q) := by
                funext l
                exact GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_canonicalBoundary_etale q I C he hI hC D l
              have ht : rest.HasIncidenceTrace (Option β)
                  (fun l => (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l).comap q') trace := by
                rw [hD]
                exact hT.2
              refine ⟨⟨AC, hAC⟩, ?_⟩
              exact ih rest q' r hrest
                (GlobalBlowup.OpenComparison.Construction.globalBlowupMapTo_contains_order_support q f I J hI C hC he b hb hp hcover)
                (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) (AC.blowupBoundary hI) trace ht

end

end OAI.AlgebraicGeometry.Resolution.Blowups
