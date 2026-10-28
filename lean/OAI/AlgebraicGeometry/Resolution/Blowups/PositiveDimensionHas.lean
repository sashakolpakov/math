import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryFiniteExistence
import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryProgramNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryProgramAuxiliary

/-! # Positive Dimension Has -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PositiveDimensionHas.Construction

noncomputable section

/-! The synchronized dimension-indexed maximum-order programs work at any positive named control. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def PositiveDimensionOrderProgram {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d) (b : ℕ) (β : Type) [Fintype β] [DecidableEq β]
    (schedule : Dimension.HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β))
    (X : Scheme) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (J : X.IdealSheafData) (D : β → X.IdealSheafData)
    (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData) (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) : Prop := by
  cases b with
  | zero => exact False
  | succ n => exact Dimension.HistoryProgramAuxiliary.Construction.DimensionHistoryProgram 𝒮 n schedule X f J D Y g K P

namespace PositiveDimensionOrderProgram

theorem hasIncidenceTrace
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : Dimension.HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β)}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (T : PositiveDimensionOrderProgram 𝒮 b β schedule X f J D Y g K P) :
    P.HasIncidenceTrace β D schedule.incidenceTrace := by
  cases b with
  | zero => exact False.elim T
  | succ n => exact Dimension.HistoryProgramAuxiliary.Construction.DimensionHistoryProgram.hasIncidenceTrace T

theorem stepCount
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : Dimension.HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β)}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (T : PositiveDimensionOrderProgram 𝒮 b β schedule X f J D Y g K P) : P.stepCount = schedule.stepCount := by
  cases b with
  | zero => exact False.elim T
  | succ n => exact Dimension.HistoryProgramAuxiliary.Construction.DimensionHistoryProgram.stepCount T

theorem terminal_order
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : Dimension.HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β)}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (T : PositiveDimensionOrderProgram 𝒮 b β schedule X f J D Y g K P) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K (b - 1) = ⊤ := by
  cases b with
  | zero => exact False.elim T
  | succ n => exact Dimension.HistoryProgramAuxiliary.Construction.DimensionHistoryProgram.terminal_order T

theorem exists_etaleComparison
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : Dimension.HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β)}
    {X Y V W : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth h] {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    {D : β → X.IdealSheafData} {E : β → V.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K} {Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M}
    (T : PositiveDimensionOrderProgram 𝒮 b β schedule X f J D Y g K P)
    (S : PositiveDimensionOrderProgram 𝒮 b β schedule V h L E W k M Q)
    (q : V ⟶ X) [Etale q] (hstructure : q ≫ f = h) (hJ : J.comap q = L)
    (hD : ∀ l, (D l).comap q = E l) : ∃ r : W ⟶ Y, P.EtaleComparison Q q r := by
  cases b with
  | zero => exact False.elim T
  | succ n => exact Dimension.HistoryProgramAuxiliary.Construction.DimensionHistoryProgram.exists_etaleComparison T S q hstructure hJ hD

end PositiveDimensionOrderProgram

theorem exists_finite_positive_dimension_order_programs {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    (b : ℕ) (hb : 0 < b) {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι]
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (hd : ∀ i, topologicalKrullDim (X i) ≤ (d + 1 : ℕ))
    (D : ∀ i, β → (X i).IdealSheafData)
    (E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ])
    (hbound : ∀ i, Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (J i) b = ⊤) :
    ∃ schedule : Dimension.HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β), ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData) (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (X i) (f i) (J i) Y g K),
        PositiveDimensionOrderProgram 𝒮 b β schedule (X i) (f i) (J i) (D i) Y g K P := by
  cases b with
  | zero => omega
  | succ n => exact Dimension.HistoryFiniteExistence.Construction.exists_finite_dimension_order_programs 𝒮 n X f J hJ hd D E hbound

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PositiveDimensionHas.Construction
