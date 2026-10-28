import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryAtlasPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison

/-! # Incidence Trace Etale Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Étale pullback preserves the exact fixed incidence trace of an actual prefix. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.hasIncidenceTrace
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) (r : W ⟶ Y),
      P.EtaleComparison Q q r → ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData)
        (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β), P.HasIncidenceTrace β D T →
        Q.HasIncidenceTrace β (fun l => (D l).comap q) T := by
  induction P with
  | @stop X f hf J =>
      intro V W h k L M Q q r hcomp β _ D T hT
      cases Q with
      | stop =>
          obtain ⟨hq, hstructure, _, _⟩ := hcomp
          let : Etale q := hq
          subst h
          cases T with
          | stop =>
              obtain ⟨A⟩ := hT
              exact ⟨A.comapEtale f q⟩
          | step => exact False.elim hT
      | blowup => exact False.elim hcomp
  | @blowup X hX hNX f J I hI hb hp hs hbl Y g K tail ih =>
      intro V W h k L M Q q r hcomp β _ D T hT
      cases Q with
      | stop => exact False.elim hcomp
      | blowup C hC hbC hpC hsC hblC rest =>
          obtain ⟨hq, hstructure, _, he, ht⟩ := hcomp
          let : Etale q := hq
          cases T with
          | stop => exact False.elim hT
          | step F T =>
              obtain ⟨⟨A, hA⟩, htail⟩ := hT
              have hAq : ∃ B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas h C (fun l => (D l).comap q),
                  ∀ i, B.divided i = F := by
                subst h
                subst C
                exact ⟨A.comapEtale f q, fun i => hA i.1⟩
              let q' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C he hI hC
              have hD : (fun l => (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l).comap q') =
                  CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary C hC (fun l => (D l).comap q) := by
                funext l
                exact GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_canonicalBoundary_etale q I C he hI hC D l
              have hrest := ih rest q' r ht (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) T htail
              rw [hD] at hrest
              exact ⟨hAq, hrest⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
