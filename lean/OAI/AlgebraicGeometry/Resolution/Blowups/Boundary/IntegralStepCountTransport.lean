import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.OrderSequenceExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceStepCountTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.SequenceCompatibility
import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBoundaryCenterExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalBoundaryOpenTransport

/-! # Integral Step Count Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Boundary-compatible integral-center extension retains the exact number of actual blowup steps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.extend_boundary_integral_from_order_neighborhood_with_stepCount
    {b : ℕ} {V : Scheme} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : V.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b V g L) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (_hJ : J ≠ ⊥)
      (j : V ⟶ X) [IsOpenImmersion j], j ≫ f = g → J.comap j = L →
      ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support : Set X) ⊆ Set.range j →
      ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData),
        Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ] → T.integralCenters →
        T.boundaryCompatible β (fun l => (D l).comap j) →
        ∃ U : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J, U.integralCenters ∧ U.boundaryCompatible β D ∧
          U.stepCount = T.stepCount := by
  induction T with
  | @terminal V g hg L ht =>
      intro X _ _ f _ J _ j _ hstructure hlocal hcover β _ D A hcenters hboundary
      subst g
      subst L
      have hterminal := Global.OrderSequenceExtension.Construction.idealSheaf_eq_top_of_support_in_open j _ hcover
        ((Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open f J (b - 1) j).trans ht)
      refine ⟨.terminal hterminal, ?_, ?_, rfl⟩
      · change True
        trivial
      · exact ⟨A⟩
  | @blowup V hV hNV g L I hI hb hp hs hbl tail ih =>
      intro X _ _ f _ J hJ j _ hstructure hlocal hcover β _ D A hcenters hboundary
      subst g
      subst L
      change IsIntegral I.subscheme ∧ tail.integralCenters at hcenters
      change Nonempty (Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (j ≫ f) I (fun l => (D l).comap j)) ∧
        tail.boundaryCompatible (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI (fun l => (D l).comap j)) at hboundary
      obtain ⟨Alocal⟩ := hboundary.1
      let : IsIntegral I.subscheme := hcenters.1
      let : Smooth (I.subschemeι ≫ (j ≫ f)) := hs
      have hb' : b - 1 + 1 = b := by omega
      have hp' : J.comap j ≤ I ^ (b - 1 + 1) := by simpa only [hb'] using hp
      let C := Global.OrderCenterExtension.Construction.openCenterExtension j I
      have hC : C ≠ ⊥ := Global.OrderCenterExtension.Construction.order_supported_center_extension_nonzero f j J hJ I (b - 1) hp' hcover
      have he : C.comap j = I := Global.OrderCenterExtension.Construction.order_supported_center_extension_restrict f j J I (b - 1) hp' hcover
      have hCs : Smooth (C.subschemeι ≫ f) :=
        Global.OrderCenterExtension.Construction.order_supported_center_extension_smooth f j J I (b - 1) hp' hcover
      let : Smooth (C.subschemeι ≫ f) := hCs
      have hCp : J ≤ C ^ b := by
        simpa only [hb'] using Global.OrderCenterExtension.Construction.order_supported_center_extension_permissible f j J I (b - 1) hp' hcover
      have hCb := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f C hC
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f) := hCb
      let q := GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo j C hC I hI he
      have hq : q ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f) =
          GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ (j ≫ f) := by
        rw [← Category.assoc, GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo_over, Category.assoc]
      have hnext := GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot C J hC b hJ
      let Aglobal := Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.extend_order_supported_center f j J I (b - 1)
        hp' hcover D A Alocal
      let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary C hC D
      have htailBoundary : tail.boundaryCompatible (Option β) (fun l => (D' l).comap q) := by
        change tail.boundaryCompatible (Option β)
          (fun l => (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary C hC D l).comap (GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo j C hC I hI he))
        rw [CanonicalBoundaryOpenTransport.Construction.globalBlowupCanonicalBoundary_comap_open]
        exact hboundary.2
      obtain ⟨rest, hrest, hrestBoundary, hcount⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J hC b) hnext q hq
        (GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo_controlled j C J hC I hI he b)
        (GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo_contains_order_support j f C J hC I hI he b hb hCp hcover)
        (Option β) D' (Aglobal.blowupBoundary hC) hcenters.2 htailBoundary
      refine ⟨.blowup C hC hb hCp hCs hCb rest, ?_, ?_, ?_⟩
      · exact ⟨Global.OrderCenterExtension.Construction.order_supported_center_extension_integral f j J I (b - 1) hp' hcover, hrest⟩
      · exact ⟨⟨Aglobal⟩, hrestBoundary⟩
      · exact congrArg (fun n : ℕ => n + 1) hcount

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.transport_boundary_integral_iso_with_stepCount
    {b : ℕ} {V : Scheme} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : V.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b V g L) (hT : T.integralCenters)
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (e : V ≅ X) (hg : e.hom ≫ f = g) (hL : J.comap e.hom = L)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
    (hB : T.boundaryCompatible β (fun l => (D l).comap e.hom)) :
    ∃ U : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J, U.integralCenters ∧ U.boundaryCompatible β D ∧
      U.stepCount = T.stepCount := by
  apply T.extend_boundary_integral_from_order_neighborhood_with_stepCount X f J hJ e.hom hg hL _ β D A hT hB
  intro x _
  refine ⟨e.inv x, ?_⟩
  change (e.inv ≫ e.hom) x = x
  rw [e.inv_hom_id]
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups
