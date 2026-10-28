import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo

/-! # Carrier Comparison Iso Composition -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A coefficient-prefix isomorphism composes with the actual closed-carrier comparison at every step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierComparison.comp_iso
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {c : ℕ} {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix c V h L W k M) (q : V ⟶ X) (r : W ⟶ Y),
      P.CarrierComparison Q q r →
      ∀ {Z U : Scheme} {a : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {d : U ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
        {B : Z.IdealSheafData} {C : U.IdealSheafData}
        (T : Smooth.ControlPrefix.Construction.SmoothControlPrefix c Z a B U d C) (p : Z ⟶ V) [IsIso p] (s : U ⟶ W),
        Q.EtaleComparison T p s → P.CarrierComparison T (p ≫ q) (s ≫ r) := by
  induction P with
  | stop =>
      intro c V W h k L M Q q r hQ Z U a d B C T p _ s hT
      cases Q with
      | blowup => exact False.elim hQ
      | stop =>
          cases T with
          | blowup => exact False.elim hT
          | stop =>
              obtain ⟨hq, hg, hr⟩ := hQ
              obtain ⟨_, ha, _, hs⟩ := hT
              let : IsClosedImmersion q := hq
              refine ⟨inferInstance, ?_, ?_⟩
              · rw [Category.assoc, hg, ha]
              · rw [hr, hs]
  | blowup I hI hb hp hs hbl tail ih =>
      intro c V W h k L M Q q r hQ Z U a d B C T p _ s hT
      cases Q with
      | stop => exact False.elim hQ
      | blowup F hF hcF hpF hsF hblF rest =>
          cases T with
          | stop => exact False.elim hT
          | blowup E hE hcE hpE hsE hblE last =>
              obtain ⟨hq, hg, he, hpush, ht⟩ := hQ
              obtain ⟨_, ha, _, he', ht'⟩ := hT
              let : IsClosedImmersion q := hq
              let : IsIso (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo p F E he' hF hE) := ControlPrefix.ComparisonFactorizationTo.Construction.globalBlowupMapTo_isIso p F E he' hF hE
              have he'' : I.comap (p ≫ q) = E := by
                rw [Scheme.IdealSheafData.comap_comp, he, he']
              refine ⟨inferInstance, ?_, he'', ?_, ?_⟩
              · rw [Category.assoc, hg, ha]
              · rw [Scheme.IdealSheafData.map_comp, ← he', ControlPrefix.ComparisonFactorizationTo.Construction.idealSheaf_map_comap_iso, hpush]
              · have hc := ih rest _ r ht last _ s ht'
                rw [GlobalBlowup.MapComposition.Construction.globalBlowupMapTo_comp q p I F E he he' he'' hI hF hE] at hc
                exact hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups
