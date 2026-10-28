import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialProgramNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryAtlasPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualNeighborhoodEtalePullback

/-! # Monomial Program Etale Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A fixed monomial schedule has a complete compatible realization after étale pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Boundary.MonomialProgram.Construction.BoundaryMonomialProgram.exists_etale_pullback {b : ℕ} (hb : 0 < b) {β : Type} [Fintype β] {a : β → ℕ}
    {faces : List (Finset β)} {schedule : Boundary.MonomialSchedule.Construction.BoundaryMonomialSchedule b β a faces}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (H : Boundary.MonomialProgram.Construction.BoundaryMonomialProgram b β a faces schedule X f J D Y g K P)
    (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V]
    (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : V.IdealSheafData) (E : β → V.IdealSheafData)
    (q : V ⟶ X) [Etale q] (hstructure : q ≫ f = h) (hL : J.comap q = L)
    (hD : ∀ l, (D l).comap q = E l) :
    ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (r : W ⟶ Y),
      Boundary.MonomialProgram.Construction.BoundaryMonomialProgram b β a faces schedule V h L E W k M Q ∧ P.EtaleComparison Q q r := by
  obtain ⟨A, hJ⟩ : ∃ A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D faces, J = Global.MixedBoundary.Construction.boundaryMonomialSheaf D a := by
    cases H with
    | terminal ht A hJ => exact ⟨A, hJ⟩
    | step C hC hface rest A hJ hI hb hp P tail => exact ⟨A, hJ⟩
  let : Smooth h := hstructure ▸ inferInstanceAs (Smooth (q ≫ f))
  let A' : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas h E faces := by
    rw [← hstructure, ← funext hD]
    exact A.comapEtale f q
  have hL' : L = Global.MixedBoundary.Construction.boundaryMonomialSheaf E a := by
    rw [← hL, hJ, ResidualNeighborhoodEtalePullback.Construction.boundaryMonomialSheaf_comap, funext hD]
  obtain ⟨W, k, M, Q, hQ⟩ := schedule.exists_program hb V h E L hL' A'.component_ne_bot A'
  obtain ⟨r, hr⟩ := H.exists_etaleComparison hQ q hstructure hL hD
  exact ⟨W, k, M, Q, r, hQ, hr⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
