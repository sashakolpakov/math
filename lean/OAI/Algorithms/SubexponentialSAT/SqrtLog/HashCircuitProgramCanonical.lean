import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramDecode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramPayload

namespace OAI.Algorithms

/-! Direct native incidence evaluation from original unary CNF literal records.
This module composes the paid literal decoder with the paid dictionary lookup;
no preprocessing assumption converts literal numbers into variable keys. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def decodeRegisters : Fin 4 → Fin 6 := ![0,1,2,5]
def decodeStacks : Fin 2 → Fin 7 := ![2,0]

theorem decodeRegisters_injective : Function.Injective decodeRegisters := by decide
theorem decodeStacks_injective : Function.Injective decodeStacks := by decide

abbrev canonicalDecode : Cmd 6 7 :=
  liftCommand Decode.programCommand 0 0 decodeRegisters decodeStacks

def canonicalRegs (regs : Fin 5 → Bool) : Fin 5 → Bool := ![false,false,true,regs 3,regs 4]

private theorem embed_decode_input (regs : Fin 5 → Bool) (old : Bool)
    (m : ℕ) (table : List Bool) :
    embedState decodeRegisters decodeStacks
      (data regs old [] (Encoding.encodeNat m).reverse [] table)
      (Decode.input ![regs 0,regs 1,regs 2,old] m) =
        data regs old [] (Encoding.encodeNat m).reverse [] table := by
  apply embedState_eq_of_ports _ _ _ _ _ decodeRegisters_injective decodeStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [decodeRegisters,Fin.exists_fin_succ]
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [decodeStacks,Fin.exists_fin_succ]

private theorem embed_decode_output (regs : Fin 5 → Bool) (old positive : Bool)
    (m v : ℕ) (table : List Bool) :
    embedState decodeRegisters decodeStacks
      (data regs old [] (Encoding.encodeNat m).reverse [] table)
      (Decode.output positive v) =
        data (canonicalRegs regs) positive []
          (Encoding.encodeNat v ++ [positive]).reverse [] table := by
  apply embedState_eq_of_ports _ _ _ _ _ decodeRegisters_injective decodeStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;>
      simp_all [decodeRegisters,canonicalRegs,Fin.exists_fin_succ]
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;>
      simp_all [decodeStacks,Fin.exists_fin_succ]

theorem canonicalDecode_eval (regs : Fin 5 → Bool) (old positive : Bool)
    (v : ℕ) (table : List Bool) :
    Eval canonicalDecode (8*v + 4*(if positive then 1 else 0)+12)
      (data regs old [] (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse [] table)
      (data (canonicalRegs regs) positive []
        (Encoding.encodeNat v ++ [positive]).reverse [] table) := by
  have h := Decode.command_eval ![regs 0,regs 1,regs 2,old] v positive
  have hh := eval_liftCommand h 0 0 decodeRegisters decodeStacks
    (data regs old [] (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse [] table)
    decodeRegisters_injective decodeStacks_injective
  simpa only [embed_decode_input,embed_decode_output,Nat.add_assoc] using hh

abbrev canonicalLiteral : Cmd 6 7 := .seq canonicalDecode literalDictionary

theorem canonicalLiteral_hit (regs : Fin 5 → Bool) (old positive : Bool)
    (v : ℕ) (payload : List Bool) (entries : List (List Bool × List Bool))
    (hlookup : entries.lookup (Encoding.encodeNat v) = some payload) :
    ∃ n ≤ 8*v+16 + literalFetchBudget (Encoding.encodeNat v) entries + 9*payload.length+9,
      ∃ regs', Eval canonicalLiteral n
        (data regs old [] (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse []
          (Squarefree.Program.lookupRecords entries))
        (data regs' positive [] [] payload (Squarefree.Program.lookupRecords entries)) ∧
      regs' 4 = true := by
  have hd := canonicalDecode_eval regs old positive v (Squarefree.Program.lookupRecords entries)
  obtain ⟨n,hn,rr,he,hf⟩ := literalDictionary_hit (canonicalRegs regs) positive positive
    (Encoding.encodeNat v) payload entries hlookup
  refine ⟨(8*v+4*(if positive then 1 else 0)+12)+n,?_,rr,hd.seq he,hf⟩
  cases positive <;> simp only [Bool.false_eq_true,↓reduceIte] at * <;> omega

def canonicalLiteralProgram := compiled canonicalLiteral 2 5

/-- The input here is exactly `Encoding.literalCode`, not a new literal syntax. -/
theorem canonicalLiteral_runs {n : ℕ} (l : SAT.Literal (Fin n))
    (regs : Fin 5 → Bool) (old : Bool) (payload : List Bool)
    (entries : List (List Bool × List Bool))
    (hlookup : entries.lookup (Encoding.encodeNat l.variable.val) = some payload) :
    ∃ regs', RunsIn canonicalLiteralProgram
      (8*l.variable.val+16 + literalFetchBudget (Encoding.encodeNat l.variable.val) entries +
        9*payload.length+10)
      ((data regs old [] (Encoding.encodeNat (Encoding.literalCode l)).reverse []
        (Squarefree.Program.lookupRecords entries)).withPC (some canonicalLiteralProgram.entry))
      ((data regs' l.positive [] [] payload (Squarefree.Program.lookupRecords entries)).withPC none) ∧
      regs' 4 = true := by
  obtain ⟨m,hm,rr,he,hf⟩ := canonicalLiteral_hit regs old l.positive l.variable.val payload entries hlookup
  exact ⟨rr,⟨m+1,by omega,compiled_halt_trace he 2 5⟩,hf⟩
end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
