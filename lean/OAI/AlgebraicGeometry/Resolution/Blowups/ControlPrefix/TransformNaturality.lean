import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.IdealTransforms
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison

/-! # Transform Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Every controlled ideal transform, including the distinguished old boundary, commutes with a stepwise étale comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.transformIdeal_ne_bot
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    (H : X.IdealSheafData) (c : ℕ) (hH : H ≠ ⊥) : P.transformIdeal H c ≠ ⊥ := by
  induction P with
  | stop => exact hH
  | blowup I hI hb hp hs hbl tail ih =>
      exact ih (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI c) (GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot I H hI c hH)

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.transformIdeal
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) (r : W ⟶ Y),
      P.EtaleComparison Q q r → ∀ (H : X.IdealSheafData) (c : ℕ),
      (P.transformIdeal H c).comap r = Q.transformIdeal (H.comap q) c := by
  induction P with
  | stop =>
      intro V W h k L M Q q r hc H c
      cases Q with
      | stop =>
          obtain ⟨_, _, _, hr⟩ := hc
          subst r
          rfl
      | blowup => exact False.elim hc
  | blowup I hI hb hp hs hbl tail ih =>
      intro V W h k L M Q q r hc H c
      cases Q with
      | stop => exact False.elim hc
      | blowup C hC hbC hpC hsC hblC rest =>
          obtain ⟨hq, _, _, he, ht⟩ := hc
          let : Etale q := hq
          have htransform := ih rest _ r ht (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI c) c
          rw [GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_controlledIdeal_etale q I H C he hI hC c] at htransform
          exact htransform

end

end OAI.AlgebraicGeometry.Resolution.Blowups
