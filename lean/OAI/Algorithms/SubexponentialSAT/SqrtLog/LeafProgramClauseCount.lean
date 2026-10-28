import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScopeCountSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramBinaryFrame

namespace OAI.Algorithms

/-! Count the clauses in the actual emitted leaf. Both the preserving record
scan and unary-to-binary conversion are fixed native programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 8 16

def data (regs : Fin 8 → Bool) (formula unary binary : List Bool) : Data :=
  ⟨regs,![[],formula,unary,[],[],[],[],[],[],[],[],[],[],[],[],binary]⟩

def small (regs : Fin 8 → Bool) (formula unary : List Bool) : State 8 15 :=
  ⟨regs,![[],formula,unary,[],[],[],[],[],[],[],[],[],[],[],[]]⟩

private theorem data_updates (regs oldRegs : Fin 8 → Bool) (formula oldU oldB u b : List Bool) :
    (data regs formula u b).stacks =
      Function.update (Function.update (data oldRegs formula oldU oldB).stacks 2 u) 15 b := by
  funext i; fin_cases i <;> simp [data]

abbrev count : Cmd 8 16 := liftCommand SubexpScopeCountSetup.countCommand 1 2 id (Fin.castAdd 1)
def binaryRegisters (i : Fin 3) : Fin 8 := i.castAdd 5
def binaryStacks : Fin 3 → Fin 16 := ![2,15,14]
abbrev convert : Cmd 8 16 := .call (ProgramLinking.liftProgram
  LeafStatisticsProgram.Binary.program binaryRegisters binaryStacks)
abbrev command : Cmd 8 16 := .seq count convert

theorem embedded (frameRegs regs : Fin 8 → Bool) (formula unary : List Bool) :
    embedState id (Fin.castAdd 1) (data frameRegs formula [] []) (small regs formula unary) =
      data regs formula unary [] := by
  apply embedState_eq_of_ports id (Fin.castAdd 1) _ _ _ Function.injective_id (Fin.castAdd_injective 15 1)
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hlast : i.val = 15 := by
      by_contra h
      have hlt : i.val < 15 := by omega
      exact hi ⟨⟨i.val,hlt⟩,Fin.ext rfl⟩
    have he : i = (15 : Fin 16) := Fin.ext hlast
    subst i
    rfl

theorem count_eval (regs : Fin 8 → Bool) (records : List (List Bool)) :
    ∃ rr, Eval count (SubexpScopeCountSetup.countBudget records+1)
      (data regs (Encoding.encodeList id records) [] [])
      (data rr (Encoding.encodeList id records) (List.replicate records.length true) []) := by
  obtain ⟨rr,he⟩ := SubexpScopeCountSetup.count_eval records
    (small regs (Encoding.encodeList id records) []) rfl rfl rfl rfl
  have hh : (⟨rr,Function.update (small regs (Encoding.encodeList id records) []).stacks
      2 (List.replicate records.length true)⟩ : State 8 15) =
      small rr (Encoding.encodeList id records) (List.replicate records.length true) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [hh] at he
  have ht := eval_call_lifted (compiled SubexpScopeCountSetup.countCommand 1 2)
    id (Fin.castAdd 1) (data regs (Encoding.encodeList id records) [] [])
    Function.injective_id (Fin.castAdd_injective 15 1) (compiled_halt_trace he 1 2)
  rw [embedded,embedded] at ht
  exact ⟨rr,ht⟩

def budget (records : List (List Bool)) : ℕ :=
  SubexpScopeCountSetup.countBudget records+1+records.length*(8*records.length+10)+5

theorem command_eval (regs : Fin 8 → Bool) (records : List (List Bool)) :
    ∃ k word rr, k ≤ budget records ∧ BinaryArithmetic.toNat word = records.length ∧
      word.length ≤ records.length ∧
      Eval command k (data regs (Encoding.encodeList id records) [] [])
        (data rr (Encoding.encodeList id records) [] word) := by
  obtain ⟨r1,h1⟩ := count_eval regs records
  let mid := data r1 (Encoding.encodeList id records) (List.replicate records.length true) []
  have hp : projectState binaryRegisters binaryStacks mid =
      LeafStatisticsProgram.Binary.state (mid.regs ∘ binaryRegisters)
        (List.replicate records.length true) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨k,word,b,hk,hv,hl,h0,h15,h14,hr,hf,he⟩ := LeafStatisticsProgram.Binary.lifted_eval
    binaryRegisters binaryStacks (Fin.castAdd_injective 3 5) (by decide) mid
    (List.replicate records.length true) hp
  have hb : b = data b.regs (Encoding.encodeList id records) [] word := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      change b.stacks i = (data b.regs (Encoding.encodeList id records) [] word).stacks i
      rw [data_updates b.regs r1 (Encoding.encodeList id records)
        (List.replicate records.length true) [] [] word]
      by_cases h2 : i=2
      · subst i
        change b.stacks (binaryStacks 0) = []
        exact h0
      by_cases hOut : i=15
      · subst i
        change b.stacks (binaryStacks 1) = word
        exact h15
      by_cases hTemp : i=14
      · subst i
        change b.stacks (binaryStacks 2) = []
        exact h14
      · rw [Function.update_of_ne hOut,Function.update_of_ne h2]
        apply hf
        rintro ⟨j,hj⟩
        fin_cases j <;> simp_all [binaryStacks]
  rw [hb] at he
  refine ⟨SubexpScopeCountSetup.countBudget records+1+k,word,b.regs,?_,?_,?_,h1.seq he⟩
  · simp only [List.length_replicate] at hk
    unfold budget
    omega
  · simpa only [List.length_replicate] using hv
  · simpa only [List.length_replicate] using hl

def program := compiled command 1 15

def callerRegisters (i : Fin 8) : Fin 40 := i.castAdd 32
def callerStacks : Fin 16 → Fin 896 := ![0,784,1,2,3,4,5,6,7,8,9,10,11,12,13,782]
abbrev caller : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram program callerRegisters callerStacks)

end SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

end OAI.Algorithms
