import Mathlib.RingTheory.Trace.Basic

/-! # Trace Pairing -/

namespace OAI.Algebra.FieldTheory.TracePairing.HodgeTracePairing

universe u v

/-- TracePairing: The trace pairing of a finite separable field extension is nondegenerate. -/
theorem trace_pairing_nondegenerate
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    (Algebra.traceForm K L).Nondegenerate := by
  exact traceForm_nondegenerate K L

end OAI.Algebra.FieldTheory.TracePairing.HodgeTracePairing
