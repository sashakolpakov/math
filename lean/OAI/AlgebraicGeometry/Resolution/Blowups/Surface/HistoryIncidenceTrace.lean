import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.AuxiliaryIncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceOpenDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.SameTraceComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.HistoryProgram

/-! # History Incidence Trace -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface

noncomputable section

/-! Every complete surface history program follows one pure incidence trace determined by the common schedule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def HistorySchedule.Construction.SurfaceHistorySchedule.incidenceTrace
    {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    (S : HistorySchedule.Construction.SurfaceHistorySchedule n e) : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β := by
  induction S with
  | @full β γ _ _ _ e he ℓ => exact ProgramIncidenceTrace.Construction.logarithmicSurfaceIncidenceTrace n ℓ β
  | @clear β γ _ _ _ e j hj ℓ tail ih =>
      exact (AuxiliaryIncidenceTrace.Construction.auxiliarySurfaceIncidenceTrace n ℓ β j).appendAtLength
        (HistorySchedule.Construction.surfaceAuxiliaryProgramStepCount n ℓ (Fintype.card β)) (AuxiliaryIncidenceTrace.Construction.auxiliarySurfaceIncidenceTrace_length n ℓ β j) ih

theorem HistorySchedule.Construction.SurfaceHistorySchedule.incidenceTrace_length
    {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    (S : HistorySchedule.Construction.SurfaceHistorySchedule n e) : S.incidenceTrace.length = S.stepCount := by
  induction S with
  | @full β γ _ _ _ e he ℓ => exact ProgramIncidenceTrace.Construction.logarithmicSurfaceIncidenceTrace_length n ℓ β
  | @clear β γ _ _ _ e j hj ℓ tail ih =>
      change ((AuxiliaryIncidenceTrace.Construction.auxiliarySurfaceIncidenceTrace n ℓ β j).appendAtLength _ _ tail.incidenceTrace).length = _
      rw [Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.appendAtLength_length, ih]
      rfl

theorem HistoryProgram.Construction.SurfaceHistoryProgram.hasIncidenceTrace
    {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    {schedule : HistorySchedule.Construction.SurfaceHistorySchedule n e} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : HistoryProgram.Construction.SurfaceHistoryProgram n schedule X f J D Y g K P) :
    P.HasIncidenceTrace β D schedule.incidenceTrace := by
  induction T with
  | full e he ℓ T => exact T.hasIncidenceTrace
  | clear e j hj ℓ schedule A aux hA P same T tail R r comparison hR hcover ih =>
      let _ := A.endpoint_smooth
      have hAB := Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible.boundaryCompatible A _ hA
      obtain ⟨EA⟩ := A.boundaryCompatible_source_atlas _ hAB
      have htraceA := aux.hasIncidenceTrace EA
      obtain ⟨EY⟩ := A.boundaryAtLength_atlas _ hAB _ aux.stepCount
      have hclear := A.auxiliary_clearance (Nat.succ_pos n) _ _ rfl
        (by simpa only [Nat.add_sub_cancel, Nat.succ_sub_one] using aux.terminal_order)
      rw [same.transformIdeal] at hclear
      have htraceR := R.hasIncidenceTrace_of_order_neighborhood T _ r comparison
        (Global.ClearedHistoryNeighborhood.Construction.cleared_boundary_complement_contains_order_locus _ _ _ (n + 1) hclear)
        _ _ EY _ ih
      exact same.append_traceAtLength A P R _ _ htraceA _ (AuxiliaryIncidenceTrace.Construction.auxiliarySurfaceIncidenceTrace_length n ℓ _ j) _ htraceR

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface
