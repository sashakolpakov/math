import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.HomogenizedTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison

/-! # Same Etale Pullback Existence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Changing the controlled ideals along the same blowups preserves stepwise étale comparisons whenever the new initial ideals match. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups.etaleComparison
    {b c : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J L : X.IdealSheafData} {K M : Y.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K} {R : Smooth.ControlPrefix.Construction.SmoothControlPrefix c X f L Y g M}
    (h : Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups b c P R) :
    ∀ {V W : Scheme} {v : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {w : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {A B : V.IdealSheafData} {C D : W.IdealSheafData}
      {Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V v A W w C} {S : Smooth.ControlPrefix.Construction.SmoothControlPrefix c V v B W w D},
      Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups b c Q S → ∀ (q : V ⟶ X) (r : W ⟶ Y),
      P.EtaleComparison Q q r → L.comap q = B → R.EtaleComparison S q r := by
  induction h with
  | stop =>
      intro V W v w A B C D Q S hS q r hcomp hL
      cases hS with
      | stop => exact ⟨hcomp.1, hcomp.2.1, hL, hcomp.2.2.2⟩
      | blowup => exact False.elim hcomp
  | @blowup X Y hX hNX f g J L K M I hI hb hc hp hq hs hbl P R tail ih =>
      intro V W v w A B C D Q S hS q r hcomp hL
      cases hS with
      | stop => exact False.elim hcomp
      | @blowup V W hV hNV v w A B C D I' hI' hb' hc' hp' hq' hs' hbl' Q S rest =>
          obtain ⟨hqEtale, hover, hJ, he, ht⟩ := hcomp
          let : Etale q := hqEtale
          have hL' : (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI c).comap
              (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I I' he hI hI') = GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I' B hI' c := by
            rw [GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_controlledIdeal_etale q I L I' he hI hI' c, hL]
          exact ⟨hqEtale, hover, hL, he, ih rest _ r ht hL'⟩

end

/-! A pullback of one marked prefix determines the actual pullback of every other control along the same blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups.exists_etale_pullback_transport
    {b c : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J L : X.IdealSheafData} {K M : Y.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K} {R : Smooth.ControlPrefix.Construction.SmoothControlPrefix c X f L Y g M}
    (h : Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups b c P R) :
    ∀ {V W : Scheme} {v : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {w : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {A : V.IdealSheafData} {C : W.IdealSheafData}
      (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V v A W w C) (q : V ⟶ X) (r : W ⟶ Y),
      P.EtaleComparison Q q r → ∀ B : V.IdealSheafData, L.comap q = B →
      ∃ (D : W.IdealSheafData) (S : Smooth.ControlPrefix.Construction.SmoothControlPrefix c V v B W w D),
        Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups b c Q S ∧ R.EtaleComparison S q r := by
  induction h with
  | stop =>
      intro V W v w A C Q q r hcomp B hL
      cases Q with
      | stop => exact ⟨B, .stop, .stop, hcomp.1, hcomp.2.1, hL, hcomp.2.2.2⟩
      | blowup => exact False.elim hcomp
  | @blowup X Y hX hNX f g J L K M I hI hb hc hp hq hs hbl P R tail ih =>
      intro V W v w A C Q q r hcomp B hL
      cases Q with
      | stop => exact False.elim hcomp
      | blowup I' hI' hb' hp' hs' hbl' Q =>
          obtain ⟨hqEtale, hover, hJ, he, ht⟩ := hcomp
          let : Etale q := hqEtale
          have hpB : B ≤ I' ^ c := by
            rw [← hL, ← he, ← IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow]
            exact Scheme.IdealSheafData.comap_mono q hq
          let q' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I I' he hI hI'
          have hL' : (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI c).comap q' =
              GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I' B hI' c := by
            rw [GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_controlledIdeal_etale q I L I' he hI hI' c, hL]
          obtain ⟨D, S, hsame, hS⟩ := ih Q q' r ht (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I' B hI' c) hL'
          exact ⟨D, .blowup I' hI' hc hpB hs' hbl' S,
            .blowup I' hI' hb' hc hp' hpB hs' hbl' hsame, hqEtale, hover, hL, he, hS⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
