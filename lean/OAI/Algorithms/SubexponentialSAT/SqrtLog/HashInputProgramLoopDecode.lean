import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ModularQuotientLift
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Fixed native decoding of one raw hash digit.  The width and modulus are
runtime data.  A digit is split into its coefficient quotient and original
clause-index remainder; the latter is emitted in the source list's canonical
natural-field syntax.  No expanded clause payload is an input. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

abbrev Data := State 8 14

abbrev tapes (raw width modulus chunk remainder quotient index : List Bool) : Fin 14 → List Bool :=
  ![raw,width,[],[],chunk,remainder,quotient,modulus,[],[],[],[],index,[]]

abbrev data (regs : Fin 8 → Bool) (raw width modulus chunk remainder quotient index : List Bool) : Data :=
  ⟨regs,tapes raw width modulus chunk remainder quotient index⟩

abbrev take : Cmd 8 14 := takeWord 1 2 3 0 4 0 1

theorem take_eval (regs : Fin 8 → Bool) (word rest width modulus : List Bool)
    (hw : width.length = word.length) :
    Eval take (14*word.length+11)
      (data regs (word++rest) width modulus [] [] [] [])
      (data (readRegs regs 0 1 none) rest width modulus word [] [] []) := by
  have h := takeWord_eval (data regs (word++rest) width modulus [] [] [] [])
    1 2 3 0 4 0 1 (by decide) (by decide) word rest rfl rfl rfl hw
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [tapes]

def divisionPorts : Fin 8 ↪ Fin 14 := ⟨![5,8,9,10,11,7,4,6],by decide⟩
abbrev divide : Cmd 8 14 := .call (SubexponentialSAT.ModularQuotientLift.programAt divisionPorts)

theorem divide_eval (regs : Fin 8 → Bool) (rest width modulus word : List Bool) :
    ∃ n ≤ 100*(modulus.length+word.length+1)^2, ∃ rf,
      Eval divide n (data regs rest width modulus word [] [] [])
        (data rf rest width modulus []
          (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).2
          (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1 []) := by
  obtain ⟨n,hn,rf,h⟩ := SubexponentialSAT.ModularQuotientLift.programAt_eval divisionPorts modulus word regs
    (tapes rest width modulus word [] [] []) rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨n,hn,rf,?_⟩
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [tapes,
      SubexponentialSAT.ModularQuotientLift.quotientStacksAt,divisionPorts]

def conversionRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def conversionStacks : Fin 3 → Fin 14 := ![5,12,8]
theorem conversionRegisters_injective : Function.Injective conversionRegisters :=
  Fin.castAdd_injective _ _
theorem conversionStacks_injective : Function.Injective conversionStacks := by decide

abbrev encode : Cmd 8 14 := .call (ProgramLinking.liftProgram
  SubexponentialSAT.CounterConversions.encodeNatProgram conversionRegisters conversionStacks)

theorem encode_eval (regs : Fin 8 → Bool) (rest width modulus remainder quotient : List Bool) :
    ∃ n ≤ SubexponentialSAT.CounterConversions.runtimeBound remainder, ∃ rf,
      Eval encode n (data regs rest width modulus [] remainder quotient [])
        (data rf rest width modulus [] [] quotient
          (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat remainder))) := by
  let d := data regs rest width modulus [] remainder quotient []
  let a := SubexponentialSAT.CounterConversions.state (regs ∘ conversionRegisters) remainder []
  let b := SubexponentialSAT.CounterConversions.state SubexponentialSAT.CounterConversions.zeroRegs []
    (Encoding.encodeNat (SubexponentialSAT.CounterPrograms.value remainder))
  have ha : projectState conversionRegisters conversionStacks d = a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨n,hn,ht⟩ := SubexponentialSAT.CounterConversions.encodeNat_runs
    (regs ∘ conversionRegisters) remainder
  change Trace SubexponentialSAT.CounterConversions.encodeNatProgram n
    (a.withPC (some SubexponentialSAT.CounterConversions.encodeNatProgram.entry)) (b.withPC none) at ht
  rw [← ha] at ht
  have h := eval_call_from_state SubexponentialSAT.CounterConversions.encodeNatProgram
    conversionRegisters conversionStacks d conversionRegisters_injective
    conversionStacks_injective ht
  let rf := (embedState conversionRegisters conversionStacks d b).regs
  have hb : embedState conversionRegisters conversionStacks d b =
      data rf rest width modulus [] [] quotient
        (Encoding.encodeNat (SubexponentialSAT.CounterPrograms.value remainder)) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : ∃ j, conversionStacks j = i
      · obtain ⟨j,rfl⟩ := hi
        exact (embedState_stack conversionRegisters conversionStacks d b
          conversionStacks_injective j).trans (by fin_cases j <;> rfl)
      · apply (embedState_stack_frame conversionRegisters conversionStacks d b i hi).trans
        have h5 : i ≠ 5 := fun h => hi ⟨0,h.symm⟩
        have h12 : i ≠ 12 := fun h => hi ⟨1,h.symm⟩
        fin_cases i <;> simp_all [d,data,tapes]
  rw [hb,SubexponentialSAT.CounterPrograms.value_eq_toNat] at h
  exact ⟨n,hn,rf,h⟩

abbrev command : Cmd 8 14 := .seq take (.seq divide encode)

def budget (width modulusLength modulusValue : ℕ) : ℕ :=
  14*width+11 + 100*(modulusLength+width+1)^2 +
    32*(modulusValue+1)*(modulusLength+width+1)

theorem command_eval (regs : Fin 8 → Bool) (word rest width modulus : List Bool)
    (hw : width.length = word.length) (hm : 0 < SubexponentialSAT.BinaryArithmetic.toNat modulus) :
    ∃ n ≤ budget word.length modulus.length (SubexponentialSAT.BinaryArithmetic.toNat modulus), ∃ rf,
      Eval command n (data regs (word++rest) width modulus [] [] [] [])
        (data rf rest width modulus [] []
          (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
          (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat word %
            SubexponentialSAT.BinaryArithmetic.toNat modulus))) := by
  have ht := take_eval regs word rest width modulus hw
  obtain ⟨nd,hnd,rd,hd⟩ := divide_eval (readRegs regs 0 1 none) rest width modulus word
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
  refine ⟨_,?_,re,ht.seq (hd.seq he)⟩
  unfold budget
  omega

def program := compiled command 0 12

theorem program_runs (regs : Fin 8 → Bool) (word rest width modulus : List Bool)
    (hw : width.length = word.length) (hm : 0 < SubexponentialSAT.BinaryArithmetic.toNat modulus) :
    ∃ rf, RunsIn program
      (budget word.length modulus.length (SubexponentialSAT.BinaryArithmetic.toNat modulus)+1)
      ((data regs (word++rest) width modulus [] [] [] []).withPC (some program.entry))
      ((data rf rest width modulus [] []
        (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
        (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat word %
          SubexponentialSAT.BinaryArithmetic.toNat modulus))).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := command_eval regs word rest width modulus hw hm
  exact ⟨rf,n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 0 12⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode

end OAI.Algorithms
