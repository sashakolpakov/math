import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonHeads
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo

/-! # Comparison At -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Pointed overlap compatibility records actual common prefixes over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.OpenCompatible
    {b : ℕ} {X U V Y Z : Scheme} {f : U ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {h : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {I : U.IdealSheafData} {J : V.IdealSheafData} {K : Y.IdealSheafData} {L : Z.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b U f I Y h K) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V g J Z k L)
    (j : U ⟶ X) (l : V ⟶ X) : Prop :=
  ∀ (x : U) (y : V), j x = l y →
    ∃ (S T : Scheme) (s : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (t : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
      (A : S.IdealSheafData) (B : T.IdealSheafData) (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b S s A T t B)
      (a : S ⟶ U) (c : S ⟶ V) (r : T ⟶ Y) (v : T ⟶ Z) (z : S),
      a z = x ∧ c z = y ∧ a ≫ j = c ≫ l ∧ P.EtaleComparison R a r ∧ Q.EtaleComparison R c v

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.OpenCompatible.head_support
    {b : ℕ} {X U V Y Z : Scheme} [IsIntegral U] [IsLocallyNoetherian U]
    [IsIntegral V] [IsLocallyNoetherian V]
    {f : U ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : U.IdealSheafData} {L : V.IdealSheafData} {M : Y.IdealSheafData} {N : Z.IdealSheafData}
    (I : U.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y h M)
    (C : V.IdealSheafData) (hC : C ≠ ⊥) (hc : 0 < b) (hpC : L ≤ C ^ b)
    (hsC : Smooth (C.subschemeι ≫ g)) (hblC : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ g))
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ g)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC b) Z k N) (j : U ⟶ X) (l : V ⟶ X)
    (H : (blowup I hI hb hp hs hbl P).OpenCompatible (blowup C hC hc hpC hsC hblC Q) j l)
    (x : U) (y : V) (hxy : j x = l y) : x ∈ I.support ↔ y ∈ C.support := by
  obtain ⟨S, T, s, t, A, B, R, a, c, r, v, z, hx, hy, _, ha, hc'⟩ := H x y hxy
  obtain ⟨hS, hNS, E, hE, hbE, hpE, hsE, hblE, rest, hR⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_blowup I hI hb hp hs hbl P R a r ha
  let : IsIntegral S := hS
  let : IsLocallyNoetherian S := hNS
  subst R
  obtain ⟨_, _, _, he, _⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff I hI hb hp hs hbl P E hE hbE hpE hsE hblE rest a r).mp ha
  obtain ⟨_, _, _, he', _⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff C hC hc hpC hsC hblC Q E hE hbE hpE hsE hblE rest c v).mp hc'
  have hz := congrArg (fun F : S.IdealSheafData => z ∈ F.support) (he.trans he'.symm)
  rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap] at hz
  change (a z ∈ I.support) = (c z ∈ C.support) at hz
  rw [hx, hy] at hz
  exact Iff.of_eq hz

end

/-! A pointed actual common program on one specified overlap point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.OpenComparisonAt
    {b : ℕ} {X U V Y Z : Scheme} {f : U ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {h : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {I : U.IdealSheafData} {J : V.IdealSheafData} {K : Y.IdealSheafData} {L : Z.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b U f I Y h K) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V g J Z k L)
    (j : U ⟶ X) (l : V ⟶ X) (x : U) (y : V) : Prop :=
  ∃ (S T : Scheme) (s : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (t : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (A : S.IdealSheafData) (B : T.IdealSheafData) (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b S s A T t B)
    (a : S ⟶ U) (c : S ⟶ V) (r : T ⟶ Y) (v : T ⟶ Z) (z : S),
    a z = x ∧ c z = y ∧ a ≫ j = c ≫ l ∧ P.EtaleComparison R a r ∧ Q.EtaleComparison R c v

end

end OAI.AlgebraicGeometry.Resolution.Blowups
