import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.SupportedCenterExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison

/-! # Control Prefix Open Extension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Whole uniform-incidence prefixes extend from order neighborhoods, retaining every actual comparison map and the remaining order locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_uniform_extension_from_order_neighborhood
    {b : ℕ} {V W : Scheme} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {L : V.IdealSheafData} {M : W.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V g L W k M) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData), J ≠ ⊥ →
      ∀ (j : V ⟶ X) [IsOpenImmersion j], j ≫ f = g → J.comap j = L →
      ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support : Set X) ⊆ Set.range j →
      ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData)
        (_A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]),
      P.uniformBoundaryCompatible β (fun l => (D l).comap j) →
      ∃ (Y : Scheme) (h : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y h K) (r : W ⟶ Y),
        letI : Smooth h := R.endpoint_smooth
        R.uniformBoundaryCompatible β D ∧ R.EtaleComparison P j r ∧ IsOpenImmersion r ∧
          ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf h K (b - 1)).support : Set Y) ⊆ Set.range r := by
  induction P with
  | stop =>
      intro X _ _ f _ J _ j _ hstructure hlocal hcover β _ D A _
      exact ⟨X, f, J, .stop, j, ⟨A⟩, ⟨inferInstance, hstructure, hlocal, rfl⟩, inferInstance, hcover⟩
  | @blowup V hV hNV g L I hI hb hp hs hbl W k M tail ih =>
      intro X _ _ f _ J hJ j _ hstructure hlocal hcover β _ D A hP
      subst g
      subst L
      let : Smooth (I.subschemeι ≫ (j ≫ f)) := hs
      have hb' : b - 1 + 1 = b := by omega
      have hp' : J.comap j ≤ I ^ (b - 1 + 1) := by simpa only [hb'] using hp
      let C := Global.OrderCenterExtension.Construction.openCenterExtension j I
      have hC : C ≠ ⊥ := Global.OrderCenterExtension.Construction.order_supported_center_extension_nonzero f j J hJ I (b - 1) hp' hcover
      have he : C.comap j = I := Global.OrderCenterExtension.Construction.order_supported_center_extension_restrict f j J I (b - 1) hp' hcover
      have hCs : Smooth (C.subschemeι ≫ f) := Global.OrderCenterExtension.Construction.order_supported_center_extension_smooth f j J I (b - 1) hp' hcover
      let : Smooth (C.subschemeι ≫ f) := hCs
      have hCp : J ≤ C ^ b := by
        simpa only [hb'] using Global.OrderCenterExtension.Construction.order_supported_center_extension_permissible f j J I (b - 1) hp' hcover
      have hCb := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f C hC
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f) := hCb
      let q := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo j C I he hC hI
      let : IsOpenImmersion q := GlobalBlowup.OpenComparison.Construction.globalBlowupMapTo_isOpenImmersion j C I he hC hI
      have hq : q ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f) = GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ (j ≫ f) := by
        rw [← Category.assoc, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, Category.assoc]
      obtain ⟨B, F, hF⟩ := hP.1
      obtain ⟨AC, hAC⟩ := B.exists_uniform_order_supported_center f j J I (b - 1) hp' hcover D A F hF
      let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary C hC D
      have hD' : (fun l => (D' l).comap q) = CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI (fun l => (D l).comap j) := by
        funext l
        exact GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_canonicalBoundary_etale j C I he hC hI D l
      have htail : tail.uniformBoundaryCompatible (Option β) (fun l => (D' l).comap q) := by
        rw [hD']
        exact hP.2
      obtain ⟨Y, h, K, R, r, hR, hcomp, hr, horder⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J hC b) (GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot C J hC b hJ) q hq
        (GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_controlledIdeal_etale j C J I he hC hI b)
        (GlobalBlowup.OpenComparison.Construction.globalBlowupMapTo_contains_order_support j f C J hC I hI he b hb hCp hcover)
        (Option β) D' (AC.blowupBoundary hC) htail
      exact ⟨Y, h, K, .blowup C hC hb hCp hCs hCb R, r,
        ⟨⟨AC, F, hAC⟩, hR⟩, ⟨inferInstance, rfl, rfl, he, hcomp⟩, hr, horder⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
