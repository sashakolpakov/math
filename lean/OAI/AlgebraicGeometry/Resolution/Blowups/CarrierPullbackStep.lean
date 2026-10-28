import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierPullbackBase
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo

/-! # Carrier Pullback Step -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

open OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix

section

/-! Pull back an explicitly named ambient and coefficient blowup step while retaining the actual carrier embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierPullback_explicit_blowups
    {b c : ℕ} {X Y V W X' Y' V' W' : Scheme}
    [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral V] [IsLocallyNoetherian V]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsIntegral V'] [IsLocallyNoetherian V']
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h' : V' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k' : W' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    {J' : X'.IdealSheafData} {K' : Y'.IdealSheafData} {L' : V'.IdealSheafData} {M' : W'.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K)
    (C : V.IdealSheafData) (hC : C ≠ ⊥) (hcC : 0 < c) (hpC : L ≤ C ^ c)
    (hsC : Smooth (C.subschemeι ≫ h)) (hblC : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h))
    (rest : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC c) W k M)
    (I' : X'.IdealSheafData) (hI' : I' ≠ ⊥) (hb' : 0 < b) (hp' : J' ≤ I' ^ b)
    (hs' : Smooth (I'.subschemeι ≫ f')) (hbl' : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I' hI' ≫ f'))
    (tail' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I' hI') (GlobalBlowup.Data.Construction.globalBlowupToBase I' hI' ≫ f') (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I' J' hI' b) Y' g' K')
    (C' : V'.IdealSheafData) (hC' : C' ≠ ⊥) (hcC' : 0 < c) (hpC' : L' ≤ C' ^ c)
    (hsC' : Smooth (C'.subschemeι ≫ h')) (hblC' : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C' hC' ≫ h'))
    (rest' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c (GlobalBlowup.Data.Construction.globalBlowup C' hC') (GlobalBlowup.Data.Construction.globalBlowupToBase C' hC' ≫ h') (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C' L' hC' c) W' k' M')
    (q : V ⟶ X) (r : W ⟶ Y) (q' : V' ⟶ X') (p : V' ⟶ V) (s : W' ⟶ W)
    (a : X' ⟶ X) (t : Y' ⟶ Y)
    (hc : (blowup I hI hb hp hs hbl tail).CarrierComparison (blowup C hC hcC hpC hsC hblC rest) q r)
    (ha : (blowup I hI hb hp hs hbl tail).EtaleComparison (blowup I' hI' hb' hp' hs' hbl' tail') a t)
    (he : (blowup C hC hcC hpC hsC hblC rest).EtaleComparison (blowup C' hC' hcC' hpC' hsC' hblC' rest') p s)
    (hpb : IsPullback p q' q a) (ih : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierPullback tail) :
    ∃ r' : W' ⟶ Y',
      (blowup I' hI' hb' hp' hs' hbl' tail').CarrierComparison (blowup C' hC' hcC' hpC' hsC' hblC' rest') q' r' ∧
        IsPullback s r' r t := by
  obtain ⟨hq, hqf, hqI, hpush, ht⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierComparison_blowup_iff I hI hb hp hs hbl tail C hC hcC hpC hsC hblC rest q r).mp hc
  obtain ⟨haEtale, haf, _, heI, haRest⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff I hI hb hp hs hbl tail I' hI' hb' hp' hs' hbl' tail' a t).mp ha
  obtain ⟨hpEtale, hph, _, heC, heRest⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff C hC hcC hpC hsC hblC rest C' hC' hcC' hpC' hsC' hblC' rest' p s).mp he
  let : IsClosedImmersion q := hq
  let : Etale a := haEtale
  let : Etale p := hpEtale
  obtain ⟨hq', hq'f⟩ := CarrierBlowupPullbackData.Construction.closed_carrier_pullback_geometry q q' p a hpb f h f' h' hqf haf hph
  obtain ⟨hqI', hpush', hnext⟩ := CarrierBlowupPullbackData.Construction.exists_carrier_blowup_pullback_data q q' p a hpb
    I C I' C' hI hC hI' hC' hqI hpush heI heC
  obtain ⟨r', hc', hfinal⟩ := ih rest (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C hqI hI hC) r ht
    tail' rest' (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q' I' C' hqI' hI' hC')
    (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo p C C' heC hC hC') s (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I I' heI hI hI') t haRest heRest hnext
  exact ⟨r', (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierComparison_blowup_iff I' hI' hb' hp' hs' hbl' tail'
    C' hC' hcC' hpC' hsC' hblC' rest' q' r').mpr ⟨hq', hq'f, hqI', hpush', hc'⟩, hfinal⟩

end

section

/-! Head extraction for the simultaneous pullback of four actual prefixes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierPullback_blowup {b : ℕ} {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K) (ih : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierPullback tail) :
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierPullback (.blowup I hI hb hp hs hbl tail) := by
  intro c V W h k L M Q q r hc X' Y' f' g' J' K' P' V' W' h' k' L' M' Q' q' p s a t ha he hpb
  obtain ⟨hV, hNV, C, hC, hcC, hpC, hsC, hblC, rest, hQ⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierComparison.exists_coefficient_blowup I hI hb hp hs hbl tail Q q r hc
  let : IsIntegral V := hV
  let : IsLocallyNoetherian V := hNV
  subst Q
  obtain ⟨hX', hNX', I', hI', hb', hp', hs', hbl', tail', hP'⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_blowup I hI hb hp hs hbl tail P' a t ha
  let : IsIntegral X' := hX'
  let : IsLocallyNoetherian X' := hNX'
  subst P'
  obtain ⟨hV', hNV', C', hC', hcC', hpC', hsC', hblC', rest', hQ'⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_blowup C hC hcC hpC hsC hblC rest Q' p s he
  let : IsIntegral V' := hV'
  let : IsLocallyNoetherian V' := hNV'
  subst Q'
  exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierPullback_explicit_blowups I hI hb hp hs hbl tail C hC hcC hpC hsC hblC rest
    I' hI' hb' hp' hs' hbl' tail' C' hC' hcC' hpC' hsC' hblC' rest' q r q' p s a t hc ha he hpb ih

end

/-! Every recorded closed-carrier lift persists through simultaneous actual étale pullback of both prefixes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierPullback
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierPullback P := by
  induction P with
  | stop => exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierPullback_stop
  | blowup I hI hb hp hs hbl tail ih => exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierPullback_blowup I hI hb hp hs hbl tail ih

end

end OAI.AlgebraicGeometry.Resolution.Blowups
