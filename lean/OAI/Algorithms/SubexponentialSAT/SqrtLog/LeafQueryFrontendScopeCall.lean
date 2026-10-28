import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCalls
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramMarkedTable
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramScopeOnly

namespace OAI.Algorithms

/-! Scope-only parsing uses a fixed t=1,d=0 dummy scalar shape. It requires
no ring parameter input and retains every hash and optional marked row. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def scopeCall : Code := .call (ProgramLinking.liftProgram HashScopeProgram.Complete.program r11 scopes)

theorem scopeCall_eval (a : Data) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : HashScopeProgram.RawTable.Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (mark : Option (Fin clauses.length)) (index width modulus : List Bool)
    (hindex : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (hw : width.length=b) (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hp : projectState r11 scopes a = HashScopeProgram.Complete.data
      HashScopeProgram.RawTable.zeroRegs width modulus (Encoding.encodeList id clauses)
      [false,false] (HashScopeProgram.RawTable.inputBits b rows) [] index [mark.isSome]) :
    ∃ n ≤ HashScopeProgram.Complete.cost 1 0 b modulus clauses codes rows mark index, ∃ rf,
      Eval scopeCall n a (embedState r11 scopes a (HashScopeProgram.Complete.data rf
        width modulus (Encoding.encodeList id clauses) [false,false]
        (LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark)) [] [] [])) := by
  obtain ⟨rf,he⟩ := HashScopeProgram.Complete.program_runsIn 1 0 (by decide) b hb
    clauses codes hc rows hbound mark index hindex width modulus [false,false] hw hm
    HashScopeProgram.Complete.scopeOnly_shape
  rw [HashScopeProgram.Complete.outputBits_nested] at he
  rw [←hp] at he
  obtain ⟨n,hn,he⟩ := call_run _ r11 scopes (registers_injective ..) (block_injective ..) a _ _ he
  exact ⟨n,hn,rf,he⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
