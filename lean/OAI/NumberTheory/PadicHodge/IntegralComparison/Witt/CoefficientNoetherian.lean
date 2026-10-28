import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.FieldTheory.Finite.Basic

/-! # Coefficient Noetherian -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientNoetherian

noncomputable section

/-! The original lifted Witt coefficient ring over a finite field is Noetherian. -/

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]

theorem witt : IsNoetherianRing (WittVector p k) := by infer_instance

theorem coefficient : IsNoetherianRing (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) := by
  let : IsNoetherianRing (WittVector p k) := witt p k
  exact isNoetherianRing_of_ringEquiv (WittVector p k) ULift.ringEquiv.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientNoetherian
