import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonHeads
import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierCenterBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierBlowupEtaleSquare

/-! # Carrier Prefix Etale Base -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Separate the head steps of carrier naturality into independently checked induction lemmas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierNaturality
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) : Prop :=
    ∀ {c : ℕ} {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V h L W k M) (q : V ⟶ X) (r : W ⟶ Y), P.CarrierComparison Q q r →
      ∀ {X' Y' : Scheme} {f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
        {J' : X'.IdealSheafData} {K' : Y'.IdealSheafData} (P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X' f' J' Y' g' K')
        {V' W' : Scheme} {h' : V' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k' : W' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
        {L' : V'.IdealSheafData} {M' : W'.IdealSheafData} (Q' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V' h' L' W' k' M')
        (q' : V' ⟶ X') (r' : W' ⟶ Y'), P'.CarrierComparison Q' q' r' →
        ∀ (p : V' ⟶ V) (s : W' ⟶ W), Q.EtaleComparison Q' p s →
        ∀ (a : X' ⟶ X) [Etale a], a ≫ f = f' → J.comap a = J' → IsPullback p q' q a →
        ∃ u : Y' ⟶ Y, P.EtaleComparison P' a u ∧ IsPullback s r' r u

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierNaturality_stop {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {J : X.IdealSheafData} : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierNaturality (.stop : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J X f J) := by
  intro c V W h k L M Q q r hc X' Y' f' g' J' K' P' V' W' h' k' L' M' Q' q' r' hc' p s he a ha hf hJ hpb
  cases Q with
  | blowup => exact False.elim hc
  | stop =>
      cases Q' with
      | blowup => exact False.elim he
      | stop =>
          cases P' with
          | blowup => exact False.elim hc'
          | stop =>
              obtain ⟨_, _, rfl⟩ := hc
              obtain ⟨_, _, rfl⟩ := hc'
              obtain ⟨_, _, _, rfl⟩ := he
              exact ⟨a, ⟨ha, hf, hJ, rfl⟩, hpb⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
