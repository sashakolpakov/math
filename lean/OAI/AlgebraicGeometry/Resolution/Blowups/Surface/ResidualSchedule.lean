import OAI.AlgebraicGeometry.Resolution.Blowups.PositiveSurface
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceExponents
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialProgramNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialProgram

/-! # Residual Schedule -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ResidualSchedule.Construction

noncomputable section

/-! Residual-order schedules share every coefficient level, incidence trace, and monomial exponent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

inductive SurfaceResidualSchedule (b : ℕ) :
    (m : ℕ) → (β : Type) → [Fintype β] → [DecidableEq β] → (β → ℕ) → Type 1
  | monomial {β : Type} [Fintype β] [DecidableEq β] (a : β → ℕ)
      (S : Boundary.MonomialSchedule.Construction.BoundaryMonomialSchedule b β a [Finset.univ]) : SurfaceResidualSchedule b 0 β a
  | higher {m : ℕ} {β : Type} [Fintype β] [DecidableEq β] (a : β → ℕ) (hle : b ≤ m + 1)
      (S : HistorySchedule.Construction.SurfaceHistorySchedule m (Function.Embedding.ofIsEmpty : Fin 0 ↪ β))
      (tail : SurfaceResidualSchedule b m (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels S.incidenceTrace.length β)
        (S.incidenceTrace.residualExponents a (m + 1) b)) : SurfaceResidualSchedule b (m + 1) β a
  | companion {m : ℕ} {β : Type} [Fintype β] [DecidableEq β] (a : β → ℕ) (hlt : m + 1 < b)
      (S : HistorySchedule.Construction.SurfaceHistorySchedule ((m + 1) * (b - (m + 1)) - 1)
        (Function.Embedding.ofIsEmpty : Fin 0 ↪ β))
      (tail : SurfaceResidualSchedule b m (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels S.incidenceTrace.length β)
        (S.incidenceTrace.companionExponents a (m + 1) b)) : SurfaceResidualSchedule b (m + 1) β a

def SurfaceResidualSchedule.incidenceTrace {b m : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {a : β → ℕ} (S : Construction.SurfaceResidualSchedule b m β a) : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β := by
  induction S with
  | monomial a S => exact S.incidenceTrace
  | higher a hle S tail ih => exact S.incidenceTrace.append ih
  | companion a hlt S tail ih => exact S.incidenceTrace.append ih

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ResidualSchedule.Construction
