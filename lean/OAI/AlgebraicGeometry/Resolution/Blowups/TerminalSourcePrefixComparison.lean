import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.TangentPrefixDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.EtalePullbackExistence

/-! # Terminal Source Prefix Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Over the initial order complement, equal-length permissible programs have a common actual restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_endpointIso_of_terminal_source
    {n : ℕ} {X Y Z : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : Z.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Z h L)
    (hN : P.stepCount = Q.stepCount) (ht : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n = ⊤) :
    ∃ e : Z ≅ Y, P.EtaleComparison Q (𝟙 X) e.hom ∧
      ∀ r : Z ⟶ Y, P.EtaleComparison Q (𝟙 X) r → r = e.hom := by
  apply P.exists_endpointIso_of_pointed_tangent Q hN
  intro x hx
  rw [ht, Scheme.IdealSheafData.support_top] at hx
  exact False.elim hx

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_common_program_of_terminal_source
    {n : ℕ} {X X' Y Y' : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {J' : X'.IdealSheafData} {K : Y.IdealSheafData} {K' : Y'.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K) (P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X' f' J' Y' g' K')
    (hN : P.stepCount = P'.stepCount)
    {S : Scheme} [IsIntegral S] [IsLocallyNoetherian S]
    (v : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth v] (L : S.IdealSheafData)
    (ht : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf v L n = ⊤)
    (a : S ⟶ X) (b : S ⟶ X') [Etale a] [Etale b]
    (haf : a ≫ f = v) (hbf : b ≫ f' = v) (haJ : J.comap a = L) (hbJ : J'.comap b = L) :
    ∃ (W : Scheme) (w : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
      (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) S v L W w M) (r : W ⟶ Y) (s : W ⟶ Y'),
      P.EtaleComparison R a r ∧ P'.EtaleComparison R b s := by
  obtain ⟨Z, z, B, R, r, hr⟩ := P.exists_etale_pullback S v L a haf haJ
  obtain ⟨Z', z', B', R', r', hr'⟩ := P'.exists_etale_pullback S v L b hbf hbJ
  have hcount : R.stepCount = R'.stepCount :=
    (hr.stepCount_eq P R a r).symm.trans (hN.trans (hr'.stepCount_eq P' R' b r'))
  obtain ⟨e, he, _⟩ := R.exists_endpointIso_of_terminal_source R' hcount ht
  have hcomp := hr.comp P R a r R' (𝟙 S) e.hom he
  rw [Category.id_comp] at hcomp
  exact ⟨Z', z', B', R', e.hom ≫ r, r', hcomp, hr'⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
