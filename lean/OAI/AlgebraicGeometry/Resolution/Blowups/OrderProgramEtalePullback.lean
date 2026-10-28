import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.HistoryProgramEtalePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.PositiveSurface

/-! # Order Program Etale Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Every positive-control surface order program has an actual étale pullback with the same schedule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem PositiveSurface.Construction.PositiveSurfaceOrderProgram.exists_etale_pullback
    {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : Surface.HistorySchedule.Construction.SurfaceHistorySchedule (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β)}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (H : PositiveSurface.Construction.PositiveSurfaceOrderProgram b β schedule X f J D Y g K P)
    (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V] [CompactSpace V] (hdV : topologicalKrullDim V ≤ 2)
    (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : V.IdealSheafData) (hLne : L ≠ ⊥) (E : β → V.IdealSheafData)
    (q : V ⟶ X) [Etale q] (hstructure : q ≫ f = h) (hL : J.comap q = L)
    (hD : ∀ l, (D l).comap q = E l) :
    ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (r : W ⟶ Y),
      PositiveSurface.Construction.PositiveSurfaceOrderProgram b β schedule V h L E W k M Q ∧ P.EtaleComparison Q q r := by
  cases b with
  | zero => exact False.elim H
  | succ n => exact Surface.HistoryProgram.Construction.SurfaceHistoryProgram.exists_etale_pullback H V hdV h L hLne E q hstructure hL hD

end

end OAI.AlgebraicGeometry.Resolution.Blowups
