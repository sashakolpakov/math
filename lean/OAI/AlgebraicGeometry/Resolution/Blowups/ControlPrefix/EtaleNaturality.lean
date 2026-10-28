import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtaleBoundary

/-! # Etale Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Prefixes following the same pulled-back center list form actual étale base-change squares. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_endpoint_pullback_of_followsCenters
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ centers : List X.IdealSheafData, P.followsCenters centers →
      ∀ {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
        {L : V.IdealSheafData} {M : W.IdealSheafData}
        (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) [Etale q],
        q ≫ f = h → J.comap q = L → Q.followsCenters (centers.map (fun C => C.comap q)) →
        ∃ r : W ⟶ Y, Etale r ∧ IsPullback r Q.toBase P.toBase q ∧ K.comap r = M := by
  induction P with
  | stop =>
      intro centers hcenters V W h k L M Q q hq hstructure hJ hQ
      change centers = [] at hcenters
      subst centers
      cases Q with
      | stop => exact ⟨q, hq, IsPullback.id_vert q, hJ⟩
      | blowup C hC hb hp hs hbl rest =>
          obtain ⟨cs, he, _⟩ := hQ
          cases he
  | @blowup X hX hNX f J I hI hb hp hs hbl Y g K tail ih =>
      intro centers hcenters V W h k L M Q q hq hstructure hJ hQ
      obtain ⟨cs, rfl, hcs⟩ := hcenters
      cases Q with
      | stop =>
          change (I :: cs).map (fun C => C.comap q) = [] at hQ
          cases hQ
      | blowup C hC hbC hpC hsC hblC rest =>
          obtain ⟨ds, he, hds⟩ := hQ
          change I.comap q :: cs.map (fun B => B.comap q) = C :: ds at he
          have hcenter : I.comap q = C := (List.cons.inj he).1
          have hlist : cs.map (fun B => B.comap q) = ds := (List.cons.inj he).2
          subst ds
          let q' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C hcenter hI hC
          let : Etale q' := GlobalBlowup.EtaleMap.Construction.globalBlowupMapTo_etale q I C hcenter hI hC
          have hover : q' ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) = GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h := by
            rw [← Category.assoc, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, Category.assoc, hstructure]
          have hJ' : (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap q' =
              GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC b := by
            rw [GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_controlledIdeal_etale q I J C hcenter hI hC b, hJ]
          have hmaps : (cs.map (fun B => B.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI))).map (fun B => B.comap q') =
              (cs.map (fun B => B.comap q)).map (fun B => B.comap (GlobalBlowup.Data.Construction.globalBlowupToBase C hC)) := by
            rw [List.map_map, List.map_map]
            apply List.map_congr_left
            intro B _
            change (B.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)).comap q' =
              (B.comap q).comap (GlobalBlowup.Data.Construction.globalBlowupToBase C hC)
            rw [← Scheme.IdealSheafData.comap_comp, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over,
              Scheme.IdealSheafData.comap_comp]
          have hrest : rest.followsCenters
              ((cs.map (fun B => B.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI))).map (fun B => B.comap q')) := by
            rw [hmaps]
            exact hds
          obtain ⟨r, hr, hpb, hK⟩ := ih _ hcs rest q' hover hJ' hrest
          exact ⟨r, hr, hpb.paste_vert (GlobalBlowup.EtalePullback.Construction.globalBlowupMapTo_etale_isPullback q I C hcenter hI hC), hK⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
