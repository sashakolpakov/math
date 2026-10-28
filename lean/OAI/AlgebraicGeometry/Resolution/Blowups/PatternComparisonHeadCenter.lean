import OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternChart
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonHeads
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo

/-! # Pattern Comparison Head Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A common actual program transfers the coordinate model's first-center alternative to the global center on the chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.head_center_dichotomy_of_pattern_comparison
    {X Y V W S T : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {v : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {w : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {s : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {t : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    {A : S.IdealSheafData} {B : T.IdealSheafData}
    (C : X.IdealSheafData) (hC : C ≠ ⊥) (hp : J ≤ C ^ 1)
    (hs : Smooth (C.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J hC 1) Y g K)
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 V v L W w M) (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 S s A T t B)
    (j : S ⟶ X) (r : T ⟶ Y) (a : S ⟶ V) (u : T ⟶ W)
    (hglobal : (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup
      C hC (by decide) hp hs hbl tail).EtaleComparison R j r)
    (hmodel : Q.EtaleComparison R a u) (hpattern : Q.UnitUntilWhole) :
    C.comap j = J.comap j ∨ C.comap j = ⊤ := by
  obtain ⟨hS, hNS, E, hE, hbE, hpE, hsE, hblE, rest, heR⟩ :=
    hglobal.exists_blowup C hC (by decide) hp hs hbl tail R j r
  let : IsIntegral S := hS
  let : IsLocallyNoetherian S := hNS
  subst R
  obtain ⟨_, _, hJA, hCE, _⟩ := (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff
    C hC (by decide) hp hs hbl tail E hE hbE hpE hsE hblE rest j r).mp hglobal
  cases Q with
  | stop => exact False.elim hmodel
  | blowup D hD hbD hpD hsD hblD modelTail =>
      obtain ⟨_, _, hLA, hDE, _⟩ := (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff
        D hD hbD hpD hsD hblD modelTail E hE hbE hpE hsE hblE rest a u).mp hmodel
      rcases hpattern with hwhole | ⟨hempty, _⟩
      · left
        exact hCE.trans (hDE.symm.trans ((congrArg (fun I => I.comap a) hwhole).trans (hLA.trans hJA.symm)))
      · right
        exact hCE.trans (hDE.symm.trans ((congrArg (fun I => I.comap a) hempty).trans
          (Scheme.IdealSheafData.comap_top a)))

end

end OAI.AlgebraicGeometry.Resolution.Blowups
