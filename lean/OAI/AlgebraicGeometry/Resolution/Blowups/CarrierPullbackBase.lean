import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonHeads
import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierBlowupPullbackData

/-! # Carrier Pullback Base -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Simultaneous pullback of ambient and coefficient prefixes retains their actual closed-carrier maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierPullback
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) : Prop :=
    ∀ {c : ℕ} {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V h L W k M) (q : V ⟶ X) (r : W ⟶ Y), P.CarrierComparison Q q r →
      ∀ {X' Y' : Scheme} {f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
        {J' : X'.IdealSheafData} {K' : Y'.IdealSheafData} (P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X' f' J' Y' g' K')
        {V' W' : Scheme} {h' : V' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k' : W' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
        {L' : V'.IdealSheafData} {M' : W'.IdealSheafData} (Q' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V' h' L' W' k' M')
        (q' : V' ⟶ X') (p : V' ⟶ V) (s : W' ⟶ W) (a : X' ⟶ X) (t : Y' ⟶ Y),
        P.EtaleComparison P' a t → Q.EtaleComparison Q' p s → IsPullback p q' q a →
        ∃ r' : W' ⟶ Y', P'.CarrierComparison Q' q' r' ∧ IsPullback s r' r t

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierPullback_stop {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {J : X.IdealSheafData} : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierPullback (.stop : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J X f J) := by
  intro c V W h k L M Q q r hc X' Y' f' g' J' K' P' V' W' h' k' L' M' Q' q' p s a t ha hp hpb
  cases Q with
  | blowup => exact False.elim hc
  | stop =>
      cases P' with
      | blowup => exact False.elim ha
      | stop =>
          cases Q' with
          | blowup => exact False.elim hp
          | stop =>
              obtain ⟨hq, hqf, hr⟩ := hc
              subst r
              obtain ⟨_, haf, _, ht⟩ := ha
              subst t
              obtain ⟨_, hph, _, hs⟩ := hp
              subst s
              let : IsClosedImmersion q := hq
              obtain ⟨hq', hq'f⟩ := CarrierBlowupPullbackData.Construction.closed_carrier_pullback_geometry q q' p a hpb f h f' h' hqf haf hph
              exact ⟨q', ⟨hq', hq'f, rfl⟩, hpb⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
