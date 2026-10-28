import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryProgramPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.PositiveDimensionHas

/-! # Dimension Order Program Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Every positive-control dimension-indexed order program has an actual étale pullback with the same schedule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem PositiveDimensionHas.Construction.PositiveDimensionOrderProgram.exists_etale_pullback
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : Dimension.HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β)}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (H : PositiveDimensionHas.Construction.PositiveDimensionOrderProgram 𝒮 b β schedule X f J D Y g K P)
    (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V] [CompactSpace V]
    (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : V.IdealSheafData) (hLne : L ≠ ⊥) (E : β → V.IdealSheafData)
    (q : V ⟶ X) [Etale q] (hstructure : q ≫ f = h) (hL : J.comap q = L)
    (hD : ∀ l, (D l).comap q = E l) :
    ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (r : W ⟶ Y),
      PositiveDimensionHas.Construction.PositiveDimensionOrderProgram 𝒮 b β schedule V h L E W k M Q ∧ P.EtaleComparison Q q r := by
  cases b with
  | zero => exact False.elim H
  | succ n => exact Dimension.HistoryProgramAuxiliary.Construction.DimensionHistoryProgram.exists_etale_pullback H V h L hLne E q hstructure hL hD

end

end OAI.AlgebraicGeometry.Resolution.Blowups
