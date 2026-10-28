import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison

/-! # Monomial Program Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary

noncomputable section

/-! Recorded monomial programs compare at every actual center under an étale pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem MonomialProgram.Construction.BoundaryMonomialProgram.exists_etaleComparison {b : ℕ} {β : Type} [Fintype β] {a : β → ℕ}
    {L : List (Finset β)} {S : MonomialSchedule.Construction.BoundaryMonomialSchedule b β a L}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (H : MonomialProgram.Construction.BoundaryMonomialProgram b β a L S X f J D Y g K P) :
    ∀ {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {B : V.IdealSheafData} {M : W.IdealSheafData} {E : β → V.IdealSheafData}
      {Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h B W k M},
      MonomialProgram.Construction.BoundaryMonomialProgram b β a L S V h B E W k M Q →
      ∀ (q : V ⟶ X) [Etale q], q ≫ f = h → J.comap q = B → (∀ l, (D l).comap q = E l) →
      ∃ r : W ⟶ Y, P.EtaleComparison Q q r := by
  induction H with
  | terminal ht A hJ =>
      intro V W h k B M E Q H q hq hstructure hB hD
      cases H with
      | terminal => exact ⟨q, hq, hstructure, hB, rfl⟩
  | @step β hβ dec a L C hC hface rest X hX hNX f J D A hJ hI hb hp Y g K P tail ih =>
      intro V W h k B M E Q H q hq hstructure hB hD
      cases H with
      | step C hC hface rest A' hB' hE hb' hp' Q tail' =>
          have he : (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C).comap q = GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf E C :=
            (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf_comap D C q).trans (congrArg (fun D => GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) (funext hD))
          let r := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf E C) he hI hE
          let : Etale r := GlobalBlowup.EtaleMap.Construction.globalBlowupMapTo_etale q _ _ he hI hE
          have hover : r ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) hI ≫ f) =
              GlobalBlowup.Data.Construction.globalBlowupToBase (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf E C) hE ≫ h := by
            rw [← Category.assoc, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, Category.assoc, hstructure]
          have hnext : (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) J hI b).comap r =
              GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf E C) B hE b := by
            rw [GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_controlledIdeal_etale, hB]
          have hboundary : ∀ l,
              (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) hI D l).comap r =
                CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf E C) hE E l := by
            intro l
            rw [GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_canonicalBoundary_etale]
            exact congrArg (fun D => CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf E C) hE D l) (funext hD)
          obtain ⟨s, hs⟩ := ih tail' r hover hnext hboundary
          exact ⟨s, hq, hstructure, hB, he, hs⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary
