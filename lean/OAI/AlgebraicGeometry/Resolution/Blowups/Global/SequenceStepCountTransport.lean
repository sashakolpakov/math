import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderSequenceExtension

/-! # Sequence Step Count Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Extension and isomorphic transport preserve the number of actual global blowup steps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def MonomialSequence.Construction.SmoothFixedControlSequence.stepCount {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) : ℕ := by
  induction T with
  | terminal => exact 0
  | blowup _ _ _ _ _ _ _ ih => exact ih + 1

theorem MonomialSequence.Construction.SmoothFixedControlSequence.extend_from_order_neighborhood_with_stepCount
    {b : ℕ} {V : Scheme} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : V.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b V g L) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (_hJ : J ≠ ⊥)
      (j : V ⟶ X) [IsOpenImmersion j], j ≫ f = g → J.comap j = L →
      ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support : Set X) ⊆ Set.range j →
      ∃ U : MonomialSequence.Construction.SmoothFixedControlSequence b X f J, U.stepCount = T.stepCount := by
  induction T with
  | @terminal V g hg L ht =>
      intro X _ _ f _ J _ j _ hstructure hlocal hcover
      subst g
      subst L
      have hterm : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1) = ⊤ := by
        apply OrderSequenceExtension.Construction.idealSheaf_eq_top_of_support_in_open j _ hcover
        rw [Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open]
        exact ht
      exact ⟨.terminal hterm, rfl⟩
  | @blowup V hV hNV g L I hI hb hp hs hbl tail ih =>
      intro X _ _ f _ J hJ j _ hstructure hlocal hcover
      subst g
      subst L
      let : Smooth (I.subschemeι ≫ (j ≫ f)) := hs
      have hb' : b - 1 + 1 = b := by omega
      have hp' : J.comap j ≤ I ^ (b - 1 + 1) := by simpa only [hb'] using hp
      let C := OrderCenterExtension.Construction.openCenterExtension j I
      have hC : C ≠ ⊥ := OrderCenterExtension.Construction.order_supported_center_extension_nonzero f j J hJ I (b - 1) hp' hcover
      have he : C.comap j = I := OrderCenterExtension.Construction.order_supported_center_extension_restrict f j J I (b - 1) hp' hcover
      have hCs : Smooth (C.subschemeι ≫ f) := OrderCenterExtension.Construction.order_supported_center_extension_smooth f j J I (b - 1) hp' hcover
      let : Smooth (C.subschemeι ≫ f) := hCs
      have hCp : J ≤ C ^ b := by simpa only [hb'] using OrderCenterExtension.Construction.order_supported_center_extension_permissible f j J I (b - 1) hp' hcover
      have hCb := SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f C hC
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f) := hCb
      let q := GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo j C hC I hI he
      have hq : q ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f) = GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ (j ≫ f) := by
        rw [← Category.assoc, GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo_over, Category.assoc]
      obtain ⟨rest, hrest⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J hC b) (GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot C J hC b hJ) q hq
        (GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo_controlled j C J hC I hI he b)
        (GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo_contains_order_support j f C J hC I hI he b hb hCp hcover)
      exact ⟨.blowup C hC hb hCp hCs hCb rest, congrArg (fun n : ℕ => n + 1) hrest⟩

theorem MonomialSequence.Construction.SmoothFixedControlSequence.transport_iso_with_stepCount
    {b : ℕ} {V : Scheme} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : V.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b V g L)
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (e : V ≅ X) (hg : e.hom ≫ f = g) (hL : J.comap e.hom = L) :
    ∃ U : MonomialSequence.Construction.SmoothFixedControlSequence b X f J, U.stepCount = T.stepCount := by
  apply T.extend_from_order_neighborhood_with_stepCount X f J hJ e.hom hg hL
  intro x _
  refine ⟨e.inv x, ?_⟩
  change (e.inv ≫ e.hom) x = x
  rw [e.inv_hom_id]
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
