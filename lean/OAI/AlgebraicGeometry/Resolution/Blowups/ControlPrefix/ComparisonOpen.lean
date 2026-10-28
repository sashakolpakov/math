import OAI.AlgebraicGeometry.Resolution.Blowups.OrderSupportedCenterNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonCoherence
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenComparison

/-! # Comparison Open -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Stepwise comparisons descend from an open containing the source order locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_etaleComparison_of_order_neighborhood
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ [Smooth f] {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth h] {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) [Etale q],
      q ≫ f = h → J.comap q = L →
      ∀ {U Z : Scheme} {a : U ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {c : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
        {B : U.IdealSheafData} {C : Z.IdealSheafData}
        (T : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b U a B Z c C) (j : U ⟶ V) [IsOpenImmersion j]
        (r : Z ⟶ Y) (s : Z ⟶ W),
        P.EtaleComparison T (j ≫ q) r → Q.EtaleComparison T j s →
        ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf h L (b - 1)).support : Set V) ⊆ Set.range j →
        ∃ t : W ⟶ Y, P.EtaleComparison Q q t := by
  induction P with
  | stop =>
      intro _ V W h _ k L M Q q hq hstructure hJ U Z a c B C T j _ r s hP hQ hcover
      cases T with
      | blowup => exact False.elim hP
      | stop =>
          cases Q with
          | blowup => exact False.elim hQ
          | stop => exact ⟨q, hq, hstructure, hJ, rfl⟩
  | @blowup X hX hNX f J I hI hb hp hs hbl Y g K tail ih =>
      intro hf V W h hh k L M Q q hq hstructure hJ U Z a c B C T j hj r s hP hQ hcover
      let : Smooth f := hf
      let : Smooth h := hh
      cases T with
      | stop => exact False.elim hP
      | blowup E hE hbE hpE hsE hblE last =>
          cases Q with
          | stop => exact False.elim hQ
          | blowup I' hI' hb' hp' hs' hbl' rest =>
              obtain ⟨_, _, _, heP, htP⟩ := hP
              obtain ⟨_, _, _, heQ, htQ⟩ := hQ
              have hlocal : (I.comap q).comap j = I'.comap j := by
                rw [← Scheme.IdealSheafData.comap_comp, heP, heQ]
              have he : I.comap q = I' := by
                subst h
                subst L
                exact OrderSupportedCenterNaturality.Construction.permissible_center_comap_eq_of_order_neighborhood f q J I I' b hb hp hp' j hcover hlocal
              let q' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I I' he hI hI'
              let j' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo j I' E heQ hI' hE
              let : Etale q' := GlobalBlowup.EtaleMap.Construction.globalBlowupMapTo_etale q I I' he hI hI'
              let : IsOpenImmersion j' := GlobalBlowup.OpenComparison.Construction.globalBlowupMapTo_isOpenImmersion j I' E heQ hI' hE
              let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
              let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I' hI' ≫ h) := hbl'
              have hstructure' : q' ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) = GlobalBlowup.Data.Construction.globalBlowupToBase I' hI' ≫ h := by
                rw [← Category.assoc, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, Category.assoc, hstructure]
              have hJ' : (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap q' =
                  GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I' L hI' b := by
                rw [GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_controlledIdeal_etale q I J I' he hI hI' b, hJ]
              have htP' : tail.EtaleComparison last (j' ≫ q') r := by
                change tail.EtaleComparison last
                  (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo j I' E heQ hI' hE ≫ GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I I' he hI hI') r
                rw [GlobalBlowup.MapComposition.Construction.globalBlowupMapTo_comp q j I I' E he heQ heP hI hI' hE]
                exact htP
              obtain ⟨t, ht⟩ := ih rest q' hstructure' hJ' last j' r s htP' htQ
                (GlobalBlowup.OpenComparison.Construction.globalBlowupMapTo_contains_order_support j h I' L hI' E hE heQ b hb hp' hcover)
              exact ⟨t, hq, hstructure, hJ, he, ht⟩

end

section

/-! Endpoint structure maps and terminal order descend through actual prefix comparisons over an order neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.endpoint_structure
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) (r : W ⟶ Y),
      P.EtaleComparison Q q r → r ≫ g = k := by
  induction P with
  | stop =>
      intro V W h k L M Q q r hc
      cases Q with
      | stop =>
          obtain ⟨_, hg, _, hr⟩ := hc
          subst r
          exact hg
      | blowup => exact False.elim hc
  | blowup I hI hb hp hs hbl tail ih =>
      intro V W h k L M Q q r hc
      cases Q with
      | stop => exact False.elim hc
      | blowup C hC hbC hpC hsC hblC rest =>
          obtain ⟨_, _, _, he, ht⟩ := hc
          exact ih rest _ r ht

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.terminal_order_of_endpoint_cover
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {L : V.IdealSheafData} {M : W.IdealSheafData} (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M)
    (q : V ⟶ X) (r : W ⟶ Y) (hc : P.EtaleComparison Q q r) (n : ℕ) :
    letI : Smooth g := P.endpoint_smooth
    letI : Smooth k := Q.endpoint_smooth
    ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n).support : Set Y) ⊆ Set.range r →
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf k M n = ⊤ → Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤ := by
  let : Smooth g := P.endpoint_smooth
  let : Smooth k := Q.endpoint_smooth
  intro hcover ht
  obtain ⟨het, _, hK⟩ := hc.endpoint_pullback P Q q r
  let : Etale r := het
  apply Global.OrderSequenceExtension.Construction.idealSheaf_eq_top_of_support_in_open r _ hcover
  have he := Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale g K n r
  rw [hK] at he
  exact he.trans ((DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (r ≫ g) k
    (hc.endpoint_structure P Q q r) M n).trans ht)

end

/-! Endpoint differential-order bounds pull back through actual full program comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.endpoint_order_bound
    {b : ℕ} {X Y V W : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M)
    (q : V ⟶ X) (r : W ⟶ Y) (hc : P.EtaleComparison Q q r) (n : ℕ) :
    letI : Smooth g := P.endpoint_smooth
    letI : Smooth k := Q.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤ → Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf k M n = ⊤ := by
  let : Smooth g := P.endpoint_smooth
  let : Smooth k := Q.endpoint_smooth
  intro ht
  obtain ⟨hr, _, hM⟩ := hc.endpoint_pullback P Q q r
  let : Etale r := hr
  have he := Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale g K n r
  rw [hM] at he
  have he' := he.trans (DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (r ≫ g) k
    (hc.endpoint_structure P Q q r) M n)
  rw [ht, Scheme.IdealSheafData.comap_top] at he'
  exact he'.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
