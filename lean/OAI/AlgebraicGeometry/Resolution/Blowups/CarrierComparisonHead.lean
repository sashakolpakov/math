import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo

/-! # Carrier Comparison Head -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A coefficient blowup forces an actual ambient blowup in a carrier comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierComparison.exists_blowup
    {b c : ℕ} {X Y V W : Scheme} [IsIntegral V] [IsLocallyNoetherian V]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (C : V.IdealSheafData) (hC : C ≠ ⊥)
    (hc : 0 < c) (hpC : L ≤ C ^ c) (hsC : Smooth (C.subschemeι ≫ h))
    (hblC : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h))
    (rest : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC c) W k M)
    (q : V ⟶ X) (r : W ⟶ Y) (H : P.CarrierComparison (.blowup C hC hc hpC hsC hblC rest) q r) :
    ∃ (hX : IsIntegral X) (hNX : IsLocallyNoetherian X),
      letI := hX
      letI := hNX
      ∃ (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
        (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
        (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
          (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K), P = .blowup I hI hb hp hs hbl tail := by
  cases P with
  | stop => exact False.elim H
  | blowup I hI hb hp hs hbl tail => exact ⟨inferInstance, inferInstance, I, hI, hb, hp, hs, hbl, tail, rfl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
