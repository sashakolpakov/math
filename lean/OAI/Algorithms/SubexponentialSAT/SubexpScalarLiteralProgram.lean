import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentLoopProof

namespace OAI.Algorithms

/-! A fixed-control scalar-to-raw-polynomial literal service.  In particular,
zero and one literals are produced by supplying their coefficient words; no
index record or instruction stream is supplied by the caller. -/

namespace SubexponentialSAT.SubexpScalarLiteralProgram

open BitProgram StructuredCalls SubexpArgumentEmitLoop

/-- Serialized singleton raw polynomial with the all-zero exponent index. -/
def rawLiteral (D : ℕ) (coefficient : List Bool) : List Bool :=
  Encoding.encodeList id
    [SubexpArgumentProgram.recordBody
      (SubexpSymbolicCost.fixedKey (SubexpArgumentCode.constantIndex D 0 0)) coefficient]

/-- The instruction table is independent of the dimension and coefficient. -/
def program := StructuredCalls.compiled (emitConstant false) 0 3

/-- Framed coefficient on stack0, unary dimension on7 and unary index width on8.
Stack3 initially encodes the empty list. All other stacks are empty. -/
theorem program_trace (D : ℕ) (coefficient tail : List Bool)
    (v p mark priorU saved : Bool) :
    Trace program (constantCost D (SubexpSymbolicCost.indexBits D) false coefficient + 1)
      ((ready v p mark priorU saved (Encoding.frame coefficient ++ tail) [false]
        D (SubexpSymbolicCost.indexBits D) 0 0 0 0 0).withPC (some program.entry))
      ((ready true false false false saved tail (rawLiteral D coefficient)
        D (SubexpSymbolicCost.indexBits D) 0 0 0 0 0).withPC none) := by
  have h := emitConstant_eval v p mark priorU false saved coefficient tail [false]
    D (SubexpSymbolicCost.indexBits D) 0 0 0 0 0
  have ht := StructuredCalls.compiled_halt_trace h 0 3
  simpa [program, rawLiteral, prepend, SubexpArgumentKeyEmitter.paddedKey_constant,
    Encoding.encodeList] using ht

theorem program_steps_le (D : ℕ) (coefficient : List Bool) :
    constantCost D (SubexpSymbolicCost.indexBits D) false coefficient + 1 ≤
      29 * coefficient.length + 33 * D + 32 * SubexpSymbolicCost.indexBits D + 196 := by
  have h := constantCost_le D (SubexpSymbolicCost.indexBits D) false coefficient
  omega

end SubexponentialSAT.SubexpScalarLiteralProgram

end OAI.Algorithms
