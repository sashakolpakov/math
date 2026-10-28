import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientNoetherian
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.AdicCompletion.Topology

/-! # Coefficient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Coefficient

noncomputable section

/-! The original universe-lifted Witt coefficient ring is p-adically complete. -/

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]

theorem coefficient : IsAdicComplete
    (Ideal.span {(p : Crystalline.ExactRestriction.Coeff (B := WittVector p k))})
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) := by
  apply (IsAdicComplete.congr_ringEquiv _ (ULift.ringEquiv :
    Crystalline.ExactRestriction.Coeff (B := WittVector p k) ≃+* WittVector p k)).mp
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using
    (inferInstance : IsAdicComplete (Ideal.span {(p : WittVector p k)}) (WittVector p k))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Coefficient
