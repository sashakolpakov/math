import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceDifferentialPullback

/-! # Differential Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The endpoint order support lies over the original order support, and actual comparison squares lift its points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.differential_total_le_endpoint
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    (r : ℕ) (hr : r ≤ b) : ∀ [Smooth f],
      letI := P.endpoint_smooth
      (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J r).comap P.toBase ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K r := by
  induction P with
  | stop =>
      intro hf
      rw [Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.toBase, Scheme.IdealSheafData.comap_id]
  | @blowup X hX hNX f J I hI hb hp hs hbl Y g K tail ih =>
      intro hf
      let : Smooth f := hf
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
      have hstep := Global.SequenceDifferentialPullback.Construction.globalBlowup_differential_total_le_controlled f I J hI b r hr hp
      change (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J r).comap (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≤ _
      rw [Scheme.IdealSheafData.comap_comp]
      exact (Scheme.IdealSheafData.comap_mono tail.toBase hstep).trans ih

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.endpoint_order_support_toBase
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    (r : ℕ) (hr : r ≤ b) :
    letI := P.endpoint_smooth
    ∀ x : Y, x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K r).support →
      P.toBase x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J r).support := by
  let : Smooth g := P.endpoint_smooth
  have hs := Scheme.IdealSheafData.support_antitone (P.differential_total_le_endpoint r hr)
  rw [Scheme.IdealSheafData.support_comap] at hs
  exact fun _ hx => hs hx

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.endpoint_order_support_cover
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {L : V.IdealSheafData} {M : W.IdealSheafData} (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M)
    (a : V ⟶ X) (r : W ⟶ Y) (hc : P.EtaleComparison Q a r) (n : ℕ) (hn : n ≤ b)
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X) ⊆ Set.range a) :
    letI := P.endpoint_smooth
    ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n).support : Set Y) ⊆ Set.range r := by
  let : Smooth g := P.endpoint_smooth
  intro x hx
  obtain ⟨v, hv⟩ := hcover (P.endpoint_order_support_toBase n hn x hx)
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback (hc.endpoint_pullback P Q a r).2.1 x v hv.symm
  exact ⟨w, hw⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
