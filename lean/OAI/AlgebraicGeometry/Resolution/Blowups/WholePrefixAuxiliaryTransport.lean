import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.HomogenizedTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Auxiliary

/-! # Whole Prefix Auxiliary Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! An auxiliary prefix transports the original ideal and distinguished boundary through the same actual blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_auxiliary_same_blowups
    {m : ℕ} (hm : 0 < m) {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {C : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f C Y g K) :
    ∀ [Smooth f] (J H : X.IdealSheafData), C = GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H m →
      ∃ (J' H' : Y.IdealSheafData) (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f J Y g J')
        (S : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 X f H Y g H'),
        Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups m m P R ∧ Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups m 1 P S ∧ K = GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J' H' m := by
  induction P with
  | stop =>
      intro _ J H hC
      exact ⟨J, H, .stop, .stop, .stop, .stop, hC⟩
  | @blowup X hX hNX f C I hI hc hp hs hbl Y g K tail ih =>
      intro hf J H hC
      let : Smooth f := hf
      let : Smooth (I.subschemeι ≫ f) := hs
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
      obtain ⟨hJ, hH⟩ := (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_smooth_center_iff f I J H m hm).mp (hC ▸ hp)
      have hnext : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I C hI m =
          GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m)
            (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1) m := by
        rw [hC, GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_transform I J H hI m hJ hH]
      obtain ⟨J', H', R, S, hR, hS, hK⟩ := ih _ _ hnext
      have hH' : H ≤ I ^ 1 := by simpa only [pow_one] using hH
      exact ⟨J', H', .blowup I hI hm hJ hs hbl R, .blowup I hI Nat.one_pos hH' hs hbl S,
        .blowup I hI hc hm hp hJ hs hbl hR, .blowup I hI hc Nat.one_pos hp hH' hs hbl hS, hK⟩

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_auxiliary_clearance_prefix
    {m : ℕ} (hm : 0 < m) {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {C : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f C Y g K)
    (J H : X.IdealSheafData) (hC : C = GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H m) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K (m - 1) = ⊤ →
      ∃ (J' H' : Y.IdealSheafData) (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f J Y g J')
        (S : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 X f H Y g H'),
        Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups m m P R ∧ Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups m 1 P S ∧
          Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g J' (m - 1) ⊔ H' = ⊤ := by
  let : Smooth g := P.endpoint_smooth
  intro ht
  obtain ⟨J', H', R, S, hR, hS, hK⟩ := P.exists_auxiliary_same_blowups hm J H hC
  refine ⟨J', H', R, S, hR, hS, ?_⟩
  apply (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_terminal_iff g J' H' m hm).mp
  rw [← hK]
  exact ht

end

end OAI.AlgebraicGeometry.Resolution.Blowups
