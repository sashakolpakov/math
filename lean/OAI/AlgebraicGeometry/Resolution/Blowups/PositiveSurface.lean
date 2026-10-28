import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.OrderFinitePrograms
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.HistoryProgramNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.HistoryIncidenceTrace

/-! # Positive Surface -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PositiveSurface.Construction

noncomputable section

/-! The synchronized surface maximum-order programs work at any positive named control. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def PositiveSurfaceOrderProgram (b : ℕ) (β : Type) [Fintype β] [DecidableEq β]
    (schedule : Surface.HistorySchedule.Construction.SurfaceHistorySchedule (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β))
    (X : Scheme) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (J : X.IdealSheafData) (D : β → X.IdealSheafData)
    (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData) (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) : Prop := by
  cases b with
  | zero => exact False
  | succ n => exact Surface.HistoryProgram.Construction.SurfaceHistoryProgram n schedule X f J D Y g K P

namespace PositiveSurfaceOrderProgram

theorem hasIncidenceTrace
    {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : Surface.HistorySchedule.Construction.SurfaceHistorySchedule (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β)}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (T : PositiveSurfaceOrderProgram b β schedule X f J D Y g K P) :
    P.HasIncidenceTrace β D schedule.incidenceTrace := by
  cases b with
  | zero => exact False.elim T
  | succ n => exact Surface.HistoryProgram.Construction.SurfaceHistoryProgram.hasIncidenceTrace T

theorem stepCount
    {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : Surface.HistorySchedule.Construction.SurfaceHistorySchedule (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β)}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (T : PositiveSurfaceOrderProgram b β schedule X f J D Y g K P) : P.stepCount = schedule.stepCount := by
  cases b with
  | zero => exact False.elim T
  | succ n => exact Surface.HistoryProgram.Construction.SurfaceHistoryProgram.stepCount T

theorem terminal_order
    {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : Surface.HistorySchedule.Construction.SurfaceHistorySchedule (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β)}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (T : PositiveSurfaceOrderProgram b β schedule X f J D Y g K P) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K (b - 1) = ⊤ := by
  cases b with
  | zero => exact False.elim T
  | succ n => exact Surface.HistoryProgram.Construction.SurfaceHistoryProgram.terminal_order T

theorem exists_etaleComparison
    {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : Surface.HistorySchedule.Construction.SurfaceHistorySchedule (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β)}
    {X Y V W : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth h] {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    {D : β → X.IdealSheafData} {E : β → V.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K} {Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M}
    (T : PositiveSurfaceOrderProgram b β schedule X f J D Y g K P)
    (S : PositiveSurfaceOrderProgram b β schedule V h L E W k M Q)
    (q : V ⟶ X) [Etale q] (hstructure : q ≫ f = h) (hJ : J.comap q = L)
    (hD : ∀ l, (D l).comap q = E l) : ∃ r : W ⟶ Y, P.EtaleComparison Q q r := by
  cases b with
  | zero => exact False.elim T
  | succ n => exact Surface.HistoryProgram.Construction.SurfaceHistoryProgram.exists_etaleComparison T S q hstructure hJ hD

end PositiveSurfaceOrderProgram

theorem exists_finite_positive_surface_order_programs
    (b : ℕ) (hb : 0 < b) {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι]
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (hd : ∀ i, topologicalKrullDim (X i) ≤ 2)
    (D : ∀ i, β → (X i).IdealSheafData)
    (E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ])
    (hbound : ∀ i, Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (J i) b = ⊤) :
    ∃ schedule : Surface.HistorySchedule.Construction.SurfaceHistorySchedule (b - 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ β), ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData) (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (X i) (f i) (J i) Y g K),
        PositiveSurfaceOrderProgram b β schedule (X i) (f i) (J i) (D i) Y g K P := by
  cases b with
  | zero => omega
  | succ n => exact Surface.OrderFinitePrograms.Construction.exists_finite_surface_order_programs n X f J hJ hd D E hbound

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PositiveSurface.Construction
