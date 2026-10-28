import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceEtalePullback

/-! # Etale Data Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual étale pullbacks retain prescribed center lists and uniform boundary compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.followsCenters
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) (r : W ⟶ Y),
      P.EtaleComparison Q q r → ∀ centers, P.followsCenters centers →
        Q.followsCenters (centers.map (fun C => C.comap q)) := by
  induction P with
  | stop =>
      intro V W h k L M Q q r hc centers hcenters
      cases Q with
      | stop =>
          change centers = [] at hcenters
          subst centers
          rfl
      | blowup => exact False.elim hc
  | @blowup X hX hNX f J I hI hb hp hs hbl Y g K tail ih =>
      intro V W h k L M Q q r hc centers hcenters
      cases Q with
      | stop => exact False.elim hc
      | blowup C hC hbC hpC hsC hblC rest =>
          obtain ⟨_, _, _, he, ht⟩ := hc
          obtain ⟨cs, rfl, hcs⟩ := hcenters
          let q' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C he hI hC
          have htail := ih rest q' r ht _ hcs
          have hmaps : (cs.map (fun B => B.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI))).map (fun B => B.comap q') =
              (cs.map (fun B => B.comap q)).map (fun B => B.comap (GlobalBlowup.Data.Construction.globalBlowupToBase C hC)) := by
            rw [List.map_map, List.map_map]
            apply List.map_congr_left
            intro B _
            change (B.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)).comap q' =
              (B.comap q).comap (GlobalBlowup.Data.Construction.globalBlowupToBase C hC)
            rw [← Scheme.IdealSheafData.comap_comp, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, Scheme.IdealSheafData.comap_comp]
          rw [hmaps] at htail
          exact ⟨cs.map (fun B => B.comap q), by simp only [List.map_cons, he], htail⟩

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.uniformBoundaryCompatible
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) (r : W ⟶ Y),
      P.EtaleComparison Q q r → ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData),
        P.uniformBoundaryCompatible β D → Q.uniformBoundaryCompatible β (fun l => (D l).comap q) := by
  induction P with
  | @stop X f hf J =>
      intro V W h k L M Q q r hcomp β _ D hD
      cases Q with
      | stop =>
          obtain ⟨hq, hstructure, _, _⟩ := hcomp
          let : Etale q := hq
          subst h
          obtain ⟨A⟩ := hD
          exact ⟨A.comapEtale f q⟩
      | blowup => exact False.elim hcomp
  | @blowup X hX hNX f J I hI hb hp hs hbl Y g K tail ih =>
      intro V W h k L M Q q r hcomp β _ D hD
      cases Q with
      | stop => exact False.elim hcomp
      | blowup C hC hbC hpC hsC hblC rest =>
          obtain ⟨hq, hstructure, _, he, ht⟩ := hcomp
          let : Etale q := hq
          obtain ⟨⟨A, F, hA⟩, htail⟩ := hD
          have hAq : ∃ B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas h C (fun l => (D l).comap q),
              ∃ F : Finset β, ∀ i, B.divided i = F := by
            subst h
            subst C
            exact ⟨A.comapEtale f q, F, fun i => hA i.1⟩
          let q' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C he hI hC
          have hboundary : (fun l => (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l).comap q') =
              CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary C hC (fun l => (D l).comap q) := by
            funext l
            exact GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_canonicalBoundary_etale q I C he hI hC D l
          have hrest := ih rest q' r ht (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) htail
          rw [hboundary] at hrest
          exact ⟨hAq, hrest⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
