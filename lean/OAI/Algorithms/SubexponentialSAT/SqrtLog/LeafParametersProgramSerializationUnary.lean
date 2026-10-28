import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpClauseMastersProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Paid, preserving serialization of parameter words as unary loop counters.
This is the checked bit conversion already used for clause-factor masters. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

open BitProgram StructuredCalls BinaryArithmetic

abbrev Data := SubexpClauseMastersProgram.Data
abbrev unaryCopy := SubexpClauseMastersProgram.unaryCopy
abbrev unaryCopyBound := SubexpClauseMastersProgram.unaryCopyBound

/-- Ports 11--13 are temporary. The binary parameter remains at `src`, and
`dst` receives one true bit per unit of the parameter. -/
theorem unaryCopy_eval (src dst : Fin 14) (d : Data)
    (hs11 : src ≠ 11) (hs13 : src ≠ 13)
    (hd11 : dst ≠ 11) (hd12 : dst ≠ 12)
    (hd : d.stacks dst = []) (h11 : d.stacks 11 = [])
    (h12 : d.stacks 12 = []) (h13 : d.stacks 13 = []) :
    ∃ t ≤ unaryCopyBound (d.stacks src),
      Eval (unaryCopy src dst) t d
        (SubexpClauseMastersProgram.write d dst (List.replicate (BinaryArithmetic.toNat (d.stacks src)) true)) := by
  simpa only [SubexpClauseMastersProgram.unary,CounterPrograms.value_eq_toNat] using
    SubexpClauseMastersProgram.unaryCopy_eval src dst d hs11 hs13 hd11 hd12 hd h11 h12 h13

/-- The value-dependent cost is exposed; unary serialization is never free. -/
theorem unaryCopyBound_eq (bits : List Bool) :
    unaryCopyBound bits=7*bits.length+5+32*(BinaryArithmetic.toNat bits+1)*(bits.length+1) := by
  simp only [unaryCopyBound,SubexpClauseMastersProgram.unaryCopyBound,
    CounterConversions.runtimeBound,CounterPrograms.value_eq_toNat]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

end OAI.Algorithms
