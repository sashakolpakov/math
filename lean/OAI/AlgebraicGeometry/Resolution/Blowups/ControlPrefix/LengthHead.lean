import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison

/-! # Length Head -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A positive prescribed length exposes an actual permissible first step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_blowup_of_stepCount_succ
    {b : ℕ} {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (N : ℕ) (hN : P.stepCount = N + 1) :
    ∃ (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
      (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
      (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K),
      P = .blowup I hI hb hp hs hbl tail ∧ tail.stepCount = N := by
  cases P with
  | stop => exact False.elim (Nat.noConfusion hN)
  | blowup I hI hb hp hs hbl tail =>
      exact ⟨I, hI, hb, hp, hs, hbl, tail, rfl, Nat.add_right_cancel hN⟩

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_comparison_from_stop_of_stepCount_zero
    {b : ℕ} {X V W : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) [Etale q]
    (hf : q ≫ f = h) (hJ : J.comap q = L) (hN : Q.stepCount = 0) :
    ∃ r : W ⟶ X, (.stop : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J X f J).EtaleComparison Q q r := by
  cases Q with
  | stop => exact ⟨q, inferInstance, hf, hJ, rfl⟩
  | blowup => exact False.elim (Nat.noConfusion hN)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
