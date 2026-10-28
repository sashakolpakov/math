import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapComposition

/-! # Comparison Coherence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Stepwise étale prefix comparisons have unique endpoints and satisfy identity and composition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.endpoint_unique
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) (r s : W ⟶ Y),
      P.EtaleComparison Q q r → P.EtaleComparison Q q s → r = s := by
  induction P with
  | stop =>
      intro V W h k L M Q q r s hr hs
      cases Q with
      | stop => exact hr.2.2.2.trans hs.2.2.2.symm
      | blowup => exact False.elim hr
  | blowup I hI hb hp hs hbl tail ih =>
      intro V W h k L M Q q r s hr hs
      cases Q with
      | stop => exact False.elim hr
      | blowup C hC hbC hpC hsC hblC rest =>
          obtain ⟨_, _, _, he, ht⟩ := hr
          obtain ⟨_, _, _, he', ht'⟩ := hs
          exact ih rest _ r s ht ht'

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.refl
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    P.EtaleComparison P (𝟙 X) (𝟙 Y) := by
  induction P with
  | stop => exact ⟨inferInstance, Category.id_comp _, Scheme.IdealSheafData.comap_id _, rfl⟩
  | blowup I hI hb hp hs hbl tail ih =>
      refine ⟨inferInstance, Category.id_comp _, Scheme.IdealSheafData.comap_id _,
        Scheme.IdealSheafData.comap_id I, ?_⟩
      rw [GlobalBlowup.MapComposition.Construction.globalBlowupMapTo_id]
      exact ih

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.comp
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) (r : W ⟶ Y),
      P.EtaleComparison Q q r →
      ∀ {Z U : Scheme} {a : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {c : U ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
        {B : Z.IdealSheafData} {C : U.IdealSheafData}
        (T : Smooth.ControlPrefix.Construction.SmoothControlPrefix b Z a B U c C) (p : Z ⟶ V) (s : U ⟶ W),
        Q.EtaleComparison T p s → P.EtaleComparison T (p ≫ q) (s ≫ r) := by
  induction P with
  | stop =>
      intro V W h k L M Q q r hQ Z U a c B C T p s hT
      cases Q with
      | blowup => exact False.elim hQ
      | stop =>
          cases T with
          | blowup => exact False.elim hT
          | stop =>
              obtain ⟨hq, hg, hJ, hr⟩ := hQ
              obtain ⟨hp, ha, hL, hs⟩ := hT
              let : Etale q := hq
              let : Etale p := hp
              refine ⟨inferInstance, ?_, ?_, ?_⟩
              · rw [Category.assoc, hg, ha]
              · rw [Scheme.IdealSheafData.comap_comp, hJ, hL]
              · rw [hr, hs]
  | blowup I hI hb hp hs hbl tail ih =>
      intro V W h k L M Q q r hQ Z U a c B C T p s hT
      cases Q with
      | stop => exact False.elim hQ
      | blowup C hC hbC hpC hsC hblC rest =>
          cases T with
          | stop => exact False.elim hT
          | blowup E hE hbE hpE hsE hblE last =>
              obtain ⟨hq, hg, hJ, he, ht⟩ := hQ
              obtain ⟨hp, ha, hL, he', ht'⟩ := hT
              let : Etale q := hq
              let : Etale p := hp
              have he'' : I.comap (p ≫ q) = E := by
                rw [Scheme.IdealSheafData.comap_comp, he, he']
              refine ⟨inferInstance, ?_, ?_, he'', ?_⟩
              · rw [Category.assoc, hg, ha]
              · rw [Scheme.IdealSheafData.comap_comp, hJ, hL]
              · have ht'' := ih rest _ r ht last _ s ht'
                rw [GlobalBlowup.MapComposition.Construction.globalBlowupMapTo_comp q p I C E he he' he'' hI hC hE] at ht''
                exact ht''

end

end OAI.AlgebraicGeometry.Resolution.Blowups
