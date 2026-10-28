import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonCoherence
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedCarrierCenters
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtaleMap

/-! # Comparison Factorization To -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! A carrier comparison records the actual closed embeddings and the pushforward of each coefficient center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ControlPrefix.ComparisonFactorizationTo.Construction.idealSheaf_map_comap_iso {X Y : Scheme} (q : Y ⟶ X) [IsIso q] (I : X.IdealSheafData) :
    (I.comap q).map q = I := by
  have h := congrArg (fun K : Y.IdealSheafData => K.comap (inv q)) (ClosedCarrierCenters.Construction.idealSheaf_closed_comap_map q (I.comap q))
  simpa only [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id] using h

theorem ControlPrefix.ComparisonFactorizationTo.Construction.globalBlowupMapTo_isIso
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ X) [IsIso q] (I : X.IdealSheafData) (K : Y.IdealSheafData)
    (he : I.comap q = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥) : IsIso (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K he hI hK) := by
  have hpb := GlobalBlowup.EtalePullback.Construction.globalBlowupMapTo_etale_isPullback q I K he hI hK
  rw [← hpb.isoPullback_hom_fst]
  infer_instance

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierComparison {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {c : ℕ} {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData},
      Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V h L W k M → (V ⟶ X) → (W ⟶ Y) → Prop := by
  induction P with
  | @stop X f hf J =>
      intro c V W h k L M Q q r
      cases Q with
      | stop => exact IsClosedImmersion q ∧ q ≫ f = h ∧ r = q
      | blowup => exact False
  | @blowup X hX hNX f J I hI hb hp hs hbl Y g K tail ih =>
      intro c V W h k L M Q q r
      cases Q with
      | stop => exact False
      | blowup C hC hc hpC hsC hblC rest =>
          exact IsClosedImmersion q ∧ q ≫ f = h ∧
            ∃ he : I.comap q = C, C.map q = I ∧ ih rest (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C he hI hC) r

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierComparison.stepCount_eq
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {c : ℕ} {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V h L W k M) (q : V ⟶ X) (r : W ⟶ Y),
      P.CarrierComparison Q q r → P.stepCount = Q.stepCount := by
  induction P with
  | stop =>
      intro c V W h k L M Q q r hc
      cases Q with
      | stop => rfl
      | blowup => exact False.elim hc
  | blowup I hI hb hp hs hbl tail ih =>
      intro c V W h k L M Q q r hc
      cases Q with
      | stop => exact False.elim hc
      | blowup C hC hcC hpC hsC hblC rest =>
          obtain ⟨_, _, he, _, ht⟩ := hc
          exact congrArg (fun n : ℕ => n + 1) (ih rest _ r ht)

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.CarrierComparison.endpoint
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {c : ℕ} {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData}
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c V h L W k M) (q : V ⟶ X) (r : W ⟶ Y),
      P.CarrierComparison Q q r → IsClosedImmersion r ∧ r ≫ g = k ∧ r ≫ P.toBase = Q.toBase ≫ q := by
  induction P with
  | stop =>
      intro c V W h k L M Q q r hc
      cases Q with
      | stop =>
          obtain ⟨hq, hover, rfl⟩ := hc
          exact ⟨hq, hover, by simp [Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.toBase]⟩
      | blowup => exact False.elim hc
  | blowup I hI hb hp hs hbl tail ih =>
      intro c V W h k L M Q q r hc
      cases Q with
      | stop => exact False.elim hc
      | blowup C hC hcC hpC hsC hblC rest =>
          obtain ⟨_, _, he, _, ht⟩ := hc
          obtain ⟨hr, hover, hmap⟩ := ih rest _ r ht
          refine ⟨hr, hover, ?_⟩
          change r ≫ (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) = (rest.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase C hC) ≫ q
          rw [← Category.assoc, hmap, Category.assoc, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, Category.assoc]

end

section

/-! Opaque equations for the comparison of two explicitly named blowup steps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.carrierComparison_blowup_iff
    {b c : ℕ} {X Y V W : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral V] [IsLocallyNoetherian V]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K)
    (C : V.IdealSheafData) (hC : C ≠ ⊥) (hc : 0 < c) (hpC : L ≤ C ^ c)
    (hsC : Smooth (C.subschemeι ≫ h)) (hblC : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h))
    (rest : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix c (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC c) W k M) (q : V ⟶ X) (r : W ⟶ Y) :
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup I hI hb hp hs hbl tail).CarrierComparison (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup C hC hc hpC hsC hblC rest) q r ↔
      IsClosedImmersion q ∧ q ≫ f = h ∧ ∃ he : I.comap q = C, C.map q = I ∧
        tail.CarrierComparison rest (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C he hI hC) r := Iff.rfl

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff
    {b : ℕ} {X Y V W : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral V] [IsLocallyNoetherian V]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K)
    (C : V.IdealSheafData) (hC : C ≠ ⊥) (hc : 0 < b) (hpC : L ≤ C ^ b)
    (hsC : Smooth (C.subschemeι ≫ h)) (hblC : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h))
    (rest : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC b) W k M) (q : V ⟶ X) (r : W ⟶ Y) :
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup I hI hb hp hs hbl tail).EtaleComparison (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup C hC hc hpC hsC hblC rest) q r ↔
      Etale q ∧ q ≫ f = h ∧ J.comap q = L ∧ ∃ he : I.comap q = C,
        tail.EtaleComparison rest (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C he hI hC) r := Iff.rfl

end

section

/-! Separate base and induction steps for factorization of actual program comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.ComparisonFactorization
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) : Prop :=
    ∀ {V W S T : Scheme} {v : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {w : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {s : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {t : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData} {A : S.IdealSheafData} {B : T.IdealSheafData}
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V v L W w M) (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b S s A T t B)
      (j : V ⟶ X) (r : W ⟶ Y) (q : S ⟶ X) (u : T ⟶ Y),
      P.EtaleComparison Q j r → P.EtaleComparison R q u →
      ∀ (a : S ⟶ V) [Etale a], a ≫ j = q → ∃ z : T ⟶ W, Q.EtaleComparison R a z

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.comparisonFactorization_stop {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {J : X.IdealSheafData} : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.ComparisonFactorization (.stop : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J X f J) := by
  intro V W S T v w s t L M A B Q R j r q u hQ hR a _ hfactor
  subst q
  cases Q with
  | blowup => exact False.elim hQ
  | stop =>
      cases R with
      | blowup => exact False.elim hR
      | stop =>
          refine ⟨a, inferInstance, ?_, ?_, rfl⟩
          · rw [← hQ.2.1, ← Category.assoc]
            exact hR.2.1
          · rw [← hQ.2.2.1, ← Scheme.IdealSheafData.comap_comp]
            exact hR.2.2.1

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.globalBlowupMapTo_factor
    {X V S : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral V] [IsLocallyNoetherian V] [IsIntegral S] [IsLocallyNoetherian S]
    (j : V ⟶ X) (a : S ⟶ V) (q : S ⟶ X) (hfactor : a ≫ j = q)
    (I : X.IdealSheafData) (C : V.IdealSheafData) (E : S.IdealSheafData)
    (heC : I.comap j = C) (he : C.comap a = E) (heE : I.comap q = E)
    (hI : I ≠ ⊥) (hC : C ≠ ⊥) (hE : E ≠ ⊥) :
    GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a C E he hC hE ≫ GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo j I C heC hI hC =
      GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I E heE hI hE := by
  subst q
  exact GlobalBlowup.MapComposition.Construction.globalBlowupMapTo_comp j a I C E heC he heE hI hC hE

end

/-! A separately checked tail comparison supplies the comparison of the two displayed first steps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.comparisonFactorization_of_tail
    {b : ℕ} {V S W T : Scheme} [IsIntegral V] [IsLocallyNoetherian V] [IsIntegral S] [IsLocallyNoetherian S]
    {v : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {s : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {w : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {t : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {L : V.IdealSheafData} {A : S.IdealSheafData} {M : W.IdealSheafData} {B : T.IdealSheafData}
    (C : V.IdealSheafData) (hC : C ≠ ⊥) (hbC : 0 < b) (hpC : L ≤ C ^ b)
    (hsC : Smooth (C.subschemeι ≫ v)) (hblC : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ v))
    (rest : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ v)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC b) W w M)
    (E : S.IdealSheafData) (hE : E ≠ ⊥) (hbE : 0 < b) (hpE : A ≤ E ^ b)
    (hsE : Smooth (E.subschemeι ≫ s)) (hblE : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase E hE ≫ s))
    (last : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup E hE) (GlobalBlowup.Data.Construction.globalBlowupToBase E hE ≫ s)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal E A hE b) T t B)
    (a : S ⟶ V) [Etale a] (hf : a ≫ v = s) (hJ : L.comap a = A) (he : C.comap a = E)
    (hnext : ∃ z : T ⟶ W, rest.EtaleComparison last (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a C E he hC hE) z) :
    ∃ z : T ⟶ W, (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup C hC hbC hpC hsC hblC rest).EtaleComparison
      (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup E hE hbE hpE hsE hblE last) a z := by
  exact ⟨Classical.choose hnext,
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff C hC hbC hpC hsC hblC rest E hE hbE hpE hsE hblE last
      a (Classical.choose hnext)).mpr ⟨inferInstance, hf, hJ, he, Classical.choose_spec hnext⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
