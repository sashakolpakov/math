import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramLocalProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphProgram

namespace OAI.Algorithms

/-! Primitive bit-machine execution of both exhaustive searches. The two
program constants have no dimension parameter; dimensions occur only in
input tapes and in the proved bounds. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem localProgram_primitive (D B ell t : ℕ) (hB : 0 < B) (hell : 0 < ell)
    (hD : D ≤ 2 ^ ell) (ht : D ≤ 8 * B * t) (a : LocalProgramState)
    (ha : LocalProgramReady t D (D / (100 * B * ell) + 1) a) :
    ∃ (out : LocalProgramState) (Q : Fin t → Fin D → SparseCode.F3),
      SparseCode.HasDistance Q (D / (100 * B * ell) + 1) ∧ out.stacks 18 = matrixFrames Q ∧
      SubexponentialSAT.Computation.RunsIn (primitive localProgram).step
        (primitiveOverhead localProgram * localProgramBudget t D (D / (100 * B * ell) + 1))
        (primitiveCfg localProgram (a.withPC (some localProgram.entry)))
        (primitiveCfg localProgram (out.withPC none)) := by
  obtain ⟨out,Q,hQ,hout,hrun⟩ := localProgram_distance D B ell t hB hell hD ht a ha
  exact ⟨out,Q,hQ,hout,primitive_execution localProgram hrun⟩

theorem graphProgram_primitive {D r q : ℕ} {qbits Dbits : List Bool} (a : GraphProgramState)
    (ha : GraphProgramReady D r q qbits Dbits a)
    (hq : 1 ≤ q) (hsize : r = 0 ∨ 8 * q ^ 2 * (r + 1) ≤ D) :
    ∃ (out : GraphProgramState) (s : Fin D → Cayley.Cube r), WalshExistence.Good q s ∧
      out.stacks 29 = matrixFrames s ∧
      SubexponentialSAT.Computation.RunsIn (primitive graphProgram).step
        (primitiveOverhead graphProgram * graphProgramBudget D r qbits.length Dbits.length)
        (primitiveCfg graphProgram (a.withPC (some graphProgram.entry)))
        (primitiveCfg graphProgram (out.withPC none)) := by
  obtain ⟨out,s,hs,hout,hrun⟩ := graphProgram_runsIn a ha hq hsize
  exact ⟨out,s,hs,hout,primitive_execution graphProgram hrun⟩

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
