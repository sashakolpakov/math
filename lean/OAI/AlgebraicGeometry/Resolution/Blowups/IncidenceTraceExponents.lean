import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IncidenceTrace

/-! # Incidence Trace Exponents -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! An exact incidence trace determines the complete residual boundary exponent update before a geometric realization is chosen. -/

def Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.residualExponents {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β) :
    (β → ℕ) → ℕ → ℕ → (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels T.length β → ℕ) := by
  induction T with
  | stop => exact fun a _ _ => a
  | step F tail ih => exact fun a m b => ih (ResidualBoundaryMonomialUpdate.Construction.residualBoundaryMonomialExponents F a m b) m b

def Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.companionExponents {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β) :
    (β → ℕ) → ℕ → ℕ → (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels T.length β → ℕ) := by
  induction T with
  | stop => exact fun a _ _ => a
  | step F tail ih => exact fun a m b => ih (Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a (b - m) F) m b

theorem IncidenceTraceExponents.Construction.residualBoundaryMonomialExponents_of_le {β : Type} (F : Finset β) (a : β → ℕ)
    (m b : ℕ) (h : m ≤ b) : ResidualBoundaryMonomialUpdate.Construction.residualBoundaryMonomialExponents F a m b = Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a (b - m) F := by
  funext j
  cases j with
  | none =>
      change (m - b) + ((∑ j ∈ F, a j) - (b - m)) = (∑ j ∈ F, a j) - (b - m)
      rw [Nat.sub_eq_zero_of_le h, Nat.zero_add]
  | some => rfl

theorem Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.companionExponents_eq_residual {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (a : β → ℕ) (m b : ℕ) (h : m ≤ b) : T.companionExponents a m b = T.residualExponents a m b := by
  induction T with
  | stop => rfl
  | step F tail ih =>
      change tail.companionExponents (Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a (b - m) F) m b =
        tail.residualExponents (ResidualBoundaryMonomialUpdate.Construction.residualBoundaryMonomialExponents F a m b) m b
      rw [IncidenceTraceExponents.Construction.residualBoundaryMonomialExponents_of_le F a m b h]
      exact ih _

end

end OAI.AlgebraicGeometry.Resolution.Blowups
