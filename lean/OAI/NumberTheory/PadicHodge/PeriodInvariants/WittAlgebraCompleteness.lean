import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittAlgebraFunctor
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Witt Algebra Completeness -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.WittAlgebraCompleteness

noncomputable section

/-! # Witt coefficient algebras are complete over their common Witt scalar ring -/

attribute [local instance] WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] (S T : Type*) [CommRing S] [CommRing T] [Algebra S T]
  [CharP T p] [PerfectRing T p]

theorem complete : IsAdicComplete (Ideal.span {(p : WittVector p S)}) (WittVector p T) := by
  apply (IsAdicComplete.map_algebraMap_iff (S := WittVector p T)
    (Ideal.span {(p : WittVector p S)}) (WittVector p T)).mp
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.WittAlgebraCompleteness
