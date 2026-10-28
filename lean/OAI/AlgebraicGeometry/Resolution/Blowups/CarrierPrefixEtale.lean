import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierPrefixEtaleBase
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo
import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierBlowupComparisonData

/-! # Carrier Prefix Etale -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

open OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix

section

/-! The geometric induction step for four explicitly named blowup prefixes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierNaturality_explicit_blowups
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
    (q : V ⟶ X) (r : W ⟶ Y) (q' : V' ⟶ X') (r' : W' ⟶ Y') (p : V' ⟶ V) (s : W' ⟶ W)
    (a : X' ⟶ X) [Etale a]
    (hc : (blowup I hI hb hp hs hbl tail).CarrierComparison (blowup C hC hcC hpC hsC hblC rest) q r)
    (hc' : (blowup I' hI' hb' hp' hs' hbl' tail').CarrierComparison (blowup C' hC' hcC' hpC' hsC' hblC' rest') q' r')
    (he : (blowup C hC hcC hpC hsC hblC rest).EtaleComparison (blowup C' hC' hcC' hpC' hsC' hblC' rest') p s)
    (hf : a ≫ f = f') (hJ : J.comap a = J') (hpb : IsPullback p q' q a) (ih : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierNaturality tail) :
    ∃ u : Y' ⟶ Y, (blowup I hI hb hp hs hbl tail).EtaleComparison (blowup I' hI' hb' hp' hs' hbl' tail') a u ∧
      IsPullback s r' r u := by
  obtain ⟨hq, _, hqI, hpush, ht⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierComparison_blowup_iff I hI hb hp hs hbl tail C hC hcC hpC hsC hblC rest q r).mp hc
  obtain ⟨_, _, hqI', hpush', ht'⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierComparison_blowup_iff I' hI' hb' hp' hs' hbl' tail' C' hC' hcC' hpC' hsC' hblC' rest' q' r').mp hc'
  obtain ⟨hpEtale, _, _, heC, heRest⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff C hC hcC hpC hsC hblC rest C' hC' hcC' hpC' hsC' hblC' rest' p s).mp he
  let : IsClosedImmersion q := hq
  let : Etale p := hpEtale
  obtain ⟨heI, ha', hf', hJ', hsquare⟩ := CarrierBlowupComparisonData.Construction.exists_carrier_blowup_comparison_data f f' J J' b q q' p a
    hf hJ hpb I C I' C' hI hC hI' hC' hqI hpush hqI' hpush' heC
  let a' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I I' heI hI hI'
  let : Etale a' := ha'
  obtain ⟨u, hu, hpu⟩ := ih rest _ r ht tail' rest' _ r' ht' _ s heRest a' hf' hJ' hsquare
  exact ⟨u, (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff I hI hb hp hs hbl tail I' hI' hb' hp' hs' hbl' tail' a u).mpr
    ⟨inferInstance, hf, hJ, heI, hu⟩, hpu⟩

end

section

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierNaturality_blowup {b : ℕ} {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K) (ih : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierNaturality tail) :
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierNaturality (.blowup I hI hb hp hs hbl tail) := by
  intro c V W h k L M Q q r hc X' Y' f' g' J' K' P' V' W' h' k' L' M' Q' q' r' hc' p s he a ha hf hJ hpb
  obtain ⟨hV, hNV, C, hC, hcC, hpC, hsC, hblC, rest, hQ⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierComparison.exists_coefficient_blowup I hI hb hp hs hbl tail Q q r hc
  let : IsIntegral V := hV
  let : IsLocallyNoetherian V := hNV
  subst Q
  obtain ⟨hV', hNV', C', hC', hcC', hpC', hsC', hblC', rest', hQ'⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_blowup C hC hcC hpC hsC hblC rest Q' p s he
  let : IsIntegral V' := hV'
  let : IsLocallyNoetherian V' := hNV'
  subst Q'
  obtain ⟨hX', hNX', I', hI', hb', hp', hs', hbl', tail', hP'⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierComparison.exists_blowup P' C' hC' hcC' hpC' hsC' hblC' rest' q' r' hc'
  let : IsIntegral X' := hX'
  let : IsLocallyNoetherian X' := hNX'
  subst P'
  exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierNaturality_explicit_blowups I hI hb hp hs hbl tail C hC hcC hpC hsC hblC rest
    I' hI' hb' hp' hs' hbl' tail' C' hC' hcC' hpC' hsC' hblC' rest' q r q' r' p s a hc hc' he hf hJ hpb ih

end

/-! Exact comparison of coefficient programs induces exact comparison of their actual ambient carrier lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierComparison.exists_etaleComparison
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
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
        ∃ u : Y' ⟶ Y, P.EtaleComparison P' a u ∧ IsPullback s r' r u := by
  change Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierNaturality P
  induction P with
  | stop => exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierNaturality_stop
  | blowup I hI hb hp hs hbl tail ih => exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierNaturality_blowup I hI hb hp hs hbl tail ih

end

end OAI.AlgebraicGeometry.Resolution.Blowups
