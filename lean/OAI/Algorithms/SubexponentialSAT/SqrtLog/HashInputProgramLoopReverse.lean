import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLoopDecode

namespace OAI.Algorithms

/-! The raw selector parser exposes a reversed payload. Decode its last
fixed-width digit first, reversing only that digit, so prepending emitted
records later restores the original tuple order. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

abbrev reverseChunk : Cmd 8 14 := .call (StackRoutines.reverseProgram 4 2 3 0 1)

theorem reverseChunk_eval (regs : Fin 8 → Bool) (word rest width modulus : List Bool) :
    Eval reverseChunk (9*word.length+7)
      (data regs rest width modulus word.reverse [] [] [])
      (data (readRegs regs 0 1 none) rest width modulus word [] [] []) := by
  have h := reverse_eval (data regs rest width modulus word.reverse [] [] [])
    4 2 3 0 1 (by decide) (by decide) (by decide) (by decide) rfl rfl
  convert h using 1
  · simp [tapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [tapes,StackRoutines.reverseStacks]

abbrev reversedCommand : Cmd 8 14 := .seq take (.seq reverseChunk (.seq divide encode))

theorem reversedCommand_eval (regs : Fin 8 → Bool) (word rest width modulus : List Bool)
    (hw : width.length = word.length) (hm : 0 < SubexponentialSAT.BinaryArithmetic.toNat modulus) :
    ∃ n ≤ budget word.length modulus.length (SubexponentialSAT.BinaryArithmetic.toNat modulus)+
        9*word.length+7, ∃ rf,
      Eval reversedCommand n (data regs (word.reverse++rest) width modulus [] [] [] [])
        (data rf rest width modulus [] []
          (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
          (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat word %
            SubexponentialSAT.BinaryArithmetic.toNat modulus))) := by
  have ht := take_eval regs word.reverse rest width modulus (by simpa using hw)
  have hv := reverseChunk_eval (readRegs regs 0 1 none) word rest width modulus
  obtain ⟨nd,hnd,rd,hd⟩ := divide_eval
    (readRegs (readRegs regs 0 1 none) 0 1 none) rest width modulus word
  obtain ⟨ne,hne,re,he⟩ := encode_eval rd rest width modulus
    (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).2
    (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
  have hr := SubexponentialSAT.ModularQuotientArithmetic.divide_remainder_correct modulus word hm
  rw [hr] at he
  have hb : ne ≤ 32*(SubexponentialSAT.BinaryArithmetic.toNat modulus+1)*(modulus.length+word.length+1) := by
    unfold SubexponentialSAT.CounterConversions.runtimeBound at hne
    rw [SubexponentialSAT.CounterPrograms.value_eq_toNat,hr,
      SubexponentialSAT.ModularQuotientArithmetic.divide_remainder_length] at hne
    exact hne.trans (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mod_lt _ hm).le 1)))
  refine ⟨_,?_,re,ht.seq (hv.seq (hd.seq he))⟩
  simp only [List.length_reverse]
  unfold budget
  omega

def reversedProgram := compiled reversedCommand 0 12

theorem reversedProgram_runs (regs : Fin 8 → Bool) (word rest width modulus : List Bool)
    (hw : width.length = word.length) (hm : 0 < SubexponentialSAT.BinaryArithmetic.toNat modulus) :
    ∃ rf, RunsIn reversedProgram
      (budget word.length modulus.length (SubexponentialSAT.BinaryArithmetic.toNat modulus)+
        9*word.length+8)
      ((data regs (word.reverse++rest) width modulus [] [] [] []).withPC
        (some reversedProgram.entry))
      ((data rf rest width modulus [] []
        (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
        (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat word %
          SubexponentialSAT.BinaryArithmetic.toNat modulus))).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := reversedCommand_eval regs word rest width modulus hw hm
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 0 12⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode

end OAI.Algorithms
