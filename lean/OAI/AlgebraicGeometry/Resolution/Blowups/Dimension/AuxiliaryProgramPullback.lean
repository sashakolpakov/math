import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.LogarithmicProgramPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryProgramAuxiliary

/-! # Auxiliary Program Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Dimension

noncomputable section

/-! Scheduled auxiliary programs retain their full named input under étale pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem HistoryProgramAuxiliary.Construction.DimensionAuxiliaryProgram.exists_etale_pullback
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {j : β} {schedule : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n {l : β // l ≠ j}} {X Y : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K}
    (H : HistoryProgramAuxiliary.Construction.DimensionAuxiliaryProgram 𝒮 j schedule X f J D Y g K P)
    (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V] [CompactSpace V]
    (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : V.IdealSheafData) (E : β → V.IdealSheafData)
    (q : V ⟶ X) [Etale q] (hstructure : q ≫ f = h) (hL : J.comap q = L)
    (hD : ∀ l, (D l).comap q = E l) :
    ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal L (E j) (n + 1)) W k M)
      (r : W ⟶ Y), HistoryProgramAuxiliary.Construction.DimensionAuxiliaryProgram 𝒮 j schedule V h L E W k M Q ∧ P.EtaleComparison Q q r := by
  apply LogarithmicProgram.Construction.DimensionLogarithmicProgram.exists_etale_pullback H V h
    (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal L (E j) (n + 1)) (fun l : {l : β // l ≠ j} => E l.val) q hstructure
  · rw [GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_comap, hL, hD]
  · intro l
    exact hD l.val

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Dimension
