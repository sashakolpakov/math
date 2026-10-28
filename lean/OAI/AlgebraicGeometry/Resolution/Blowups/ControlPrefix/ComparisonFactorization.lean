import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTail
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonHeads

/-! # Comparison Factorization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Explicit head steps keep comparison factorization within the default kernel limits. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.comparisonFactorization_explicit_blowups
    {b : ℕ} {X V S Y W T : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral V] [IsLocallyNoetherian V] [IsIntegral S] [IsLocallyNoetherian S]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {v : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {s : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {w : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {t : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {L : V.IdealSheafData} {A : S.IdealSheafData}
    {K : Y.IdealSheafData} {M : W.IdealSheafData} {B : T.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K)
    (C : V.IdealSheafData) (hC : C ≠ ⊥) (hbC : 0 < b) (hpC : L ≤ C ^ b)
    (hsC : Smooth (C.subschemeι ≫ v)) (hblC : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ v))
    (rest : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ v)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC b) W w M)
    (E : S.IdealSheafData) (hE : E ≠ ⊥) (hbE : 0 < b) (hpE : A ≤ E ^ b)
    (hsE : Smooth (E.subschemeι ≫ s)) (hblE : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase E hE ≫ s))
    (last : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup E hE) (GlobalBlowup.Data.Construction.globalBlowupToBase E hE ≫ s)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal E A hE b) T t B)
    (j : V ⟶ X) (r : W ⟶ Y) (q : S ⟶ X) (u : T ⟶ Y)
    (hQ : (blowup I hI hb hp hs hbl tail).EtaleComparison (blowup C hC hbC hpC hsC hblC rest) j r)
    (hR : (blowup I hI hb hp hs hbl tail).EtaleComparison (blowup E hE hbE hpE hsE hblE last) q u)
    (a : S ⟶ V) [Etale a] (hfactor : a ≫ j = q) (ih : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.ComparisonFactorization tail) :
    ∃ z : T ⟶ W, (blowup C hC hbC hpC hsC hblC rest).EtaleComparison
      (blowup E hE hbE hpE hsE hblE last) a z := by
  obtain ⟨hj, hv, hL, heC, hrest⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff I hI hb hp hs hbl tail C hC hbC hpC hsC hblC rest j r).mp hQ
  obtain ⟨hq, hS, hA, heE, hlast⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff I hI hb hp hs hbl tail E hE hbE hpE hsE hblE last q u).mp hR
  let : Etale j := hj
  have he : C.comap a = E := by
    rw [← heC, ← Scheme.IdealSheafData.comap_comp, hfactor]
    exact heE
  have hnext := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.comparisonFactorization_tail I hI C hC E hE tail rest last j r q u heC heE
    hrest hlast a hfactor he ih
  have hground : a ≫ v = s := by
    rw [← hv, ← Category.assoc, hfactor]
    exact hS
  have hmarked : L.comap a = A := by
    rw [← hL, ← Scheme.IdealSheafData.comap_comp, hfactor]
    exact hA
  exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.comparisonFactorization_of_tail C hC hbC hpC hsC hblC rest E hE hbE hpE hsE hblE last
    a hground hmarked he hnext

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.comparisonFactorization_blowup {b : ℕ} {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K) (ih : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.ComparisonFactorization tail) :
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.ComparisonFactorization (blowup I hI hb hp hs hbl tail) := by
  intro V W S T v w s t L M A B Q R j r q u hQ hR a _ hfactor
  obtain ⟨hV, hNV, C, hC, hbC, hpC, hsC, hblC, rest, hEq⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_blowup I hI hb hp hs hbl tail Q j r hQ
  let : IsIntegral V := hV
  let : IsLocallyNoetherian V := hNV
  subst Q
  obtain ⟨hS, hNS, E, hE, hbE, hpE, hsE, hblE, last, hEq⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_blowup I hI hb hp hs hbl tail R q u hR
  let : IsIntegral S := hS
  let : IsLocallyNoetherian S := hNS
  subst R
  exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.comparisonFactorization_explicit_blowups I hI hb hp hs hbl tail C hC hbC hpC hsC hblC rest
    E hE hbE hpE hsE hblE last j r q u hQ hR a hfactor ih

end

/-! A factorization of initial étale comparison maps lifts through every actual program step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_comparison_over_factor
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ {V W S T : Scheme} {v : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {w : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {s : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {t : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData} {A : S.IdealSheafData} {B : T.IdealSheafData}
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V v L W w M) (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b S s A T t B)
      (j : V ⟶ X) (r : W ⟶ Y) (q : S ⟶ X) (u : T ⟶ Y),
      P.EtaleComparison Q j r → P.EtaleComparison R q u →
      ∀ (a : S ⟶ V) [Etale a], a ≫ j = q → ∃ z : T ⟶ W, Q.EtaleComparison R a z := by
  change Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.ComparisonFactorization P
  induction P with
  | stop => exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.comparisonFactorization_stop
  | blowup I hI hb hp hs hbl tail ih => exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.comparisonFactorization_blowup I hI hb hp hs hbl tail ih

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_factor
    {b : ℕ} {X Y V W S T : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {v : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {w : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {s : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {t : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    {A : S.IdealSheafData} {B : T.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V v L W w M)
    (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b S s A T t B) (j : V ⟶ X) (r : W ⟶ Y) (q : S ⟶ X) (u : T ⟶ Y)
    (hQ : P.EtaleComparison Q j r) (hR : P.EtaleComparison R q u)
    (a : S ⟶ V) [Etale a] (hfactor : a ≫ j = q) :
    ∃ z : T ⟶ W, Q.EtaleComparison R a z ∧ z ≫ r = u := by
  obtain ⟨z, hz⟩ := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_comparison_over_factor P Q R j r q u hQ hR a hfactor
  have hcomp := hQ.comp P Q j r R a z hz
  rw [hfactor] at hcomp
  exact ⟨z, hz, Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.endpoint_unique P R q (z ≫ r) u hcomp hR⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
