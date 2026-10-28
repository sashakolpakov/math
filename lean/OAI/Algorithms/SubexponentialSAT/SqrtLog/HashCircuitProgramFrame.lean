import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramCanonical
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramRows

namespace OAI.Algorithms

/-! Fixed caller framing for the native sparse-hash interpreter. Low ports
0--55 are reserved for arithmetic. Literal lookup uses 56--62, leaving the
clause, row and constant accumulators physically untouched. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Machine := State 8 96

def literalRegisters : Fin 6 → Fin 8 := Fin.castAdd 2
def literalStacks (i : Fin 7) : Fin 96 := ⟨56+i.val,by omega⟩
theorem literalRegisters_injective : Function.Injective literalRegisters :=
  Fin.castAdd_injective _ _
theorem literalStacks_injective : Function.Injective literalStacks := by
  intro i j h
  have h' := congrArg Fin.val h
  apply Fin.ext
  simp only [literalStacks] at h'
  omega

abbrev fetchLiteral : Cmd 8 96 :=
  liftCommand canonicalLiteral 2 5 literalRegisters literalStacks

noncomputable def literalFrame (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) : Machine :=
  embedState literalRegisters literalStacks base (data regs positive scan query result table)

/-- A caller may keep arbitrary arithmetic data, source records and accumulators
outside the seven lookup stacks. The run includes the subroutine return. -/
theorem fetchLiteral_eval (base : Machine) (regs : Fin 5 → Bool) (old positive : Bool)
    (v : ℕ) (payload : List Bool) (entries : List (List Bool × List Bool))
    (hlookup : entries.lookup (Encoding.encodeNat v) = some payload) :
    ∃ n ≤ 8*v+16 + literalFetchBudget (Encoding.encodeNat v) entries + 9*payload.length+10,
      ∃ regs', Eval fetchLiteral n
        (literalFrame base regs old [] (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse
          [] (Squarefree.Program.lookupRecords entries))
        (literalFrame base regs' positive [] [] payload (Squarefree.Program.lookupRecords entries)) ∧
      regs' 4 = true := by
  obtain ⟨n,hn,rr,he,hf⟩ := canonicalLiteral_hit regs old positive v payload entries hlookup
  refine ⟨n+1,by omega,rr,?_,hf⟩
  exact eval_liftCommand he 2 5 literalRegisters literalStacks base
    literalRegisters_injective literalStacks_injective

theorem literalFrame_stack (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) (i : Fin 96)
    (hi : i.val < 56 ∨ 63 ≤ i.val) :
    (literalFrame base regs positive scan query result table).stacks i = base.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  simp only [literalStacks] at hh
  have := j.isLt
  omega

@[simp] theorem literalFrame_result (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) :
    (literalFrame base regs positive scan query result table).stacks 61 = result := by
  exact embedState_stack literalRegisters literalStacks base _ literalStacks_injective 5

@[simp] theorem literalFrame_table (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) :
    (literalFrame base regs positive scan query result table).stacks 62 = table := by
  exact embedState_stack literalRegisters literalStacks base _ literalStacks_injective 6

@[simp] theorem literalFrame_sign (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) :
    (literalFrame base regs positive scan query result table).regs 5 = positive := by
  exact embedState_register literalRegisters literalStacks base _ literalRegisters_injective 5

/-- The weighted record opener consumes50 and writes original clause bytes47
and reversed flat weight49. Ports41,59,60 are scratch shared with lookup. -/
def rowRegisters : Fin 5 → Fin 8 := Fin.castAdd 3
def rowStacks : Fin 6 → Fin 96 := ![66,57,63,59,60,65]
theorem rowRegisters_injective : Function.Injective rowRegisters := Fin.castAdd_injective _ _
theorem rowStacks_injective : Function.Injective rowStacks := by decide

abbrev openWeighted : Cmd 8 96 :=
  liftCommand Rows.openWeighted 0 2 rowRegisters rowStacks

noncomputable abbrev rowFrame (base : Machine) (regs : Fin 5 → Bool) (payload clause weight : List Bool) : Machine :=
  embedState rowRegisters rowStacks base
    (SubexponentialSAT.SubexpRecordScan.recordState regs payload [] clause [] [] weight)

theorem openWeighted_eval (base : Machine) (regs : Fin 5 → Bool) (weight clause : List Bool) :
    Eval openWeighted (3*(Encoding.frame weight ++ clause).length+6*weight.length+8)
      (rowFrame base regs (Encoding.frame weight ++ clause).reverse [] [])
      (rowFrame base (readRegs (readRegs regs 0 1 none) 0 1 (some false)) [] clause weight.reverse) := by
  have h := eval_liftCommand (Rows.openWeighted_eval regs weight clause) 0 2 rowRegisters rowStacks base
    rowRegisters_injective rowStacks_injective
  simpa only [Nat.add_assoc] using h

/-- All clause/row accumulator stacks are outside the opener's scratch set. -/
theorem rowFrame_stack (base : Machine) (regs : Fin 5 → Bool) (payload clause weight : List Bool)
    (i : Fin 96) (hi : i.val < 56 ∨ 67 ≤ i.val) :
    (rowFrame base regs payload clause weight).stacks i = base.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  fin_cases j <;> simp [rowStacks] at hj <;> subst i <;> omega

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
