import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramScoreCanonical

namespace OAI.Algorithms

/-! Fixed placement of the score normalizer after the marked-clause sum. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Score.Wide

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def register (i : Fin 8) : Fin 40 := i.castAdd 32
def stack : Fin 9 → Fin 768 := ![322,323,324,325,326,327,328,329,212]
abbrev command : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram Score.program register stack)

theorem run (frame : State 40 768) (regs : Fin 8 → Bool) (input width : List Bool)
    (z : ℕ) (hz : z < 2 ^ width.length) (hv : BinaryArithmetic.toNat input = z) :
    ∃ steps finalRegs, steps ≤ 14 * width.length + 2 * input.length + 15 ∧
      Eval command steps
        (embedState register stack frame (Score.data regs input [] width))
        (embedState register stack frame
          (Score.data finalRegs (SubexpLiftRing.fixedBits width.length z) [] width)) :=
  canonical_score_lifted register stack (Fin.castAdd_injective 8 32) (by decide)
    frame regs input width z hz hv

end SubexponentialSAT.SqrtLog.LeafProgram.Score.Wide

end OAI.Algorithms
