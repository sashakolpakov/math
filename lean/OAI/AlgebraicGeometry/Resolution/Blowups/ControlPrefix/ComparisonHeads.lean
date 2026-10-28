import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierComparisonHead

/-! # Comparison Heads -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Head extraction for coefficient and étale comparisons keeps later recursive proofs small. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierComparison.exists_coefficient_blowup
    {b c : ℕ} {X Y V W : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K)
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V h L W k M) (q : V ⟶ X) (r : W ⟶ Y)
    (H : (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup I hI hb hp hs hbl tail).CarrierComparison Q q r) :
    ∃ (hV : IsIntegral V) (hNV : IsLocallyNoetherian V),
      letI := hV
      letI := hNV
      ∃ (C : V.IdealSheafData) (hC : C ≠ ⊥) (hc : 0 < c) (hpC : L ≤ C ^ c)
        (hsC : Smooth (C.subschemeι ≫ h)) (hblC : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h))
        (rest : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h)
          (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC c) W k M), Q = .blowup C hC hc hpC hsC hblC rest := by
  cases Q with
  | stop => exact False.elim H
  | blowup C hC hc hpC hsC hblC rest => exact ⟨inferInstance, inferInstance, C, hC, hc, hpC, hsC, hblC, rest, rfl⟩

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_blowup
    {b : ℕ} {X Y V W : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K)
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) (r : W ⟶ Y)
    (H : (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup I hI hb hp hs hbl tail).EtaleComparison Q q r) :
    ∃ (hV : IsIntegral V) (hNV : IsLocallyNoetherian V),
      letI := hV
      letI := hNV
      ∃ (C : V.IdealSheafData) (hC : C ≠ ⊥) (hc : 0 < b) (hpC : L ≤ C ^ b)
        (hsC : Smooth (C.subschemeι ≫ h)) (hblC : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h))
        (rest : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h)
          (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC b) W k M), Q = .blowup C hC hc hpC hsC hblC rest := by
  cases Q with
  | stop => exact False.elim H
  | blowup C hC hc hpC hsC hblC rest => exact ⟨inferInstance, inferInstance, C, hC, hc, hpC, hsC, hblC, rest, rfl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
