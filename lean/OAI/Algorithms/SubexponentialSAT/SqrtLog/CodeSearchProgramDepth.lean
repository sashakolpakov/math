import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramFramed

namespace OAI.Algorithms

/-! Runtime tuple depth is the length of a tape; the bits on that tape are
irrelevant. In particular metadata counters may use true unary bits. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.TupleProgram SubexponentialSAT.SubexpEnumerationPayload

def framedDepthInput (p : ℕ) [Fact p.Prime] (depth : List Bool) :
    StructuredProgram.State 10 9 :=
  ⟨fun _ => false, fun i =>
    if i = 1 then ProgramEncoding.encodeRecords (framedAlphabet p)
    else if i = 8 then depth else []⟩

theorem framedDepth_runsIn (p : ℕ) [Fact p.Prime] (depth : List Bool) :
    ∃ next : StructuredProgram.State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords (framedCandidates p depth.length) ∧
      next.stacks 8 = [] ∧
      RunsIn enumerationProgram (framedEnumerationCost p depth.length)
        ((framedDepthInput p depth).withPC (some enumerationProgram.entry))
        (next.withPC none) := by
  have hi : outerInvariant (framedAlphabet p) depth false (framedDepthInput p depth) := by
    simp [outerInvariant,framedDepthInput]
  obtain ⟨next,hnext,k,hk,he⟩ := generateProgram_runsIn (framedAlphabet p) depth false
    (framedDepthInput p depth) hi (by simp [framedDepthInput])
    (by simp [framedDepthInput]) (by simp [framedDepthInput])
  have hwidth : ∀ word ∈ framedAlphabet p, word.length ≤ 2 * scalarWidth p + 1 := by
    intro word hw
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hw
    exact ((framedScalarCode p).length_block x).le
  have hc := Subexp.PackingTupleBounds.generated_powerCost_le
    (framedAlphabet p) depth.length (2 * scalarWidth p + 1) hwidth
  refine ⟨next,?_,hnext.1.2.2.2.2.2.1,k,?_,he⟩
  · simpa [framedCandidates] using hnext.2.1
  · have hk' : k ≤ powerCost (framedAlphabet p) depth.length [[]] + 9 := by simpa using hk
    exact hk'.trans (by simpa [framedEnumerationCost] using Nat.add_le_add_right hc 9)

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
