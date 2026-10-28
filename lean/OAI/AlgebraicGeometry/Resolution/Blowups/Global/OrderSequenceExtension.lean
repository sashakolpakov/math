import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderCenterExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialSequence
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Nonzero

/-! # Order Sequence Extension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Whole actual fixed-control sequences extend from an open containing the full order locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem OrderSequenceExtension.Construction.idealSheaf_eq_top_of_support_in_open
    {V X : Scheme} (j : V ⟶ X) (I : X.IdealSheafData)
    (hcover : (I.support : Set X) ⊆ Set.range j) (ht : I.comap j = ⊤) : I = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff I).mp
  apply SetLike.coe_injective
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨y, rfl⟩ := hcover hx
  have hy : y ∈ (I.comap j).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hx
  rw [ht, Scheme.IdealSheafData.support_top] at hy
  exact hy

theorem MonomialSequence.Construction.SmoothFixedControlSequence.extend_from_order_neighborhood
    {b : ℕ} {V : Scheme} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : V.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b V g L) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (_hJ : J ≠ ⊥)
      (j : V ⟶ X) [IsOpenImmersion j], j ≫ f = g → J.comap j = L →
      ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support : Set X) ⊆ Set.range j →
      Nonempty (MonomialSequence.Construction.SmoothFixedControlSequence b X f J) := by
  induction T with
  | @terminal V g hg L ht =>
      intro X _ _ f _ J _ j _ hstructure hlocal hcover
      subst g
      subst L
      refine ⟨.terminal (OrderSequenceExtension.Construction.idealSheaf_eq_top_of_support_in_open j _ hcover ?_)⟩
      rw [Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open]
      exact ht
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
      have hCs : Smooth (C.subschemeι ≫ f) :=
        OrderCenterExtension.Construction.order_supported_center_extension_smooth f j J I (b - 1) hp' hcover
      let : Smooth (C.subschemeι ≫ f) := hCs
      have hCp : J ≤ C ^ b := by
        simpa only [hb'] using OrderCenterExtension.Construction.order_supported_center_extension_permissible f j J I (b - 1) hp' hcover
      have hCb := SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f C hC
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f) := hCb
      let q := GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo j C hC I hI he
      have hq : q ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f) =
          GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ (j ≫ f) := by
        rw [← Category.assoc, GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo_over, Category.assoc]
      have hnext := GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot C J hC b hJ
      obtain ⟨rest⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J hC b) hnext q hq
        (GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo_controlled j C J hC I hI he b)
        (GlobalBlowup.OpenTransport.Construction.globalBlowupOpenMapTo_contains_order_support j f C J hC I hI he b hb hCp hcover)
      exact ⟨.blowup C hC hb hCp hCs hCb rest⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
