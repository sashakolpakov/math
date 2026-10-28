import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramArithmetic
import OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram

namespace OAI.Algorithms

/-! Primitive preparation of a nonnegative shifted integer coefficient.
The input signed integer is a pair P-N; W dominates N. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

abbrev ShiftData := State 8 10

def shiftState (regs : Fin 8 → Bool) (W N P diff out : List Bool) : ShiftData :=
  ⟨regs, ![W,N,diff,[],[],[],[],[],P,out]⟩

def subtractPort : Fin 8 → Fin 10 := Fin.castAdd 2

theorem subtractPort_injective : Function.Injective subtractPort := Fin.castAdd_injective _ _

abbrev subtractCall : Cmd 8 10 := .call
  (ProgramLinking.liftProgram SubexponentialSAT.SaturatingSubtractionProgram.program id subtractPort)

def shiftWork : Fin 5 ↪ Fin 10 where
  toFun i := ⟨i.val+3, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def shiftAddPorts : Ports 10 where
  left := 2
  right := 8
  out := 9
  work := shiftWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

abbrev shiftCommand : Cmd 8 10 := .seq subtractCall (addAt shiftAddPorts)
def shiftProgram := compiled shiftCommand 0 9

theorem shiftCommand_eval_lengths (regs : Fin 8 → Bool) (W N P : List Bool) :
    ∃ t ≤ 300*(W.length+N.length+P.length+1)^2, ∃ rf diff out,
      Eval shiftCommand t (shiftState regs W N P [] []) (shiftState rf W N P diff out) ∧
      SubexponentialSAT.BinaryArithmetic.toNat out =
        SubexponentialSAT.BinaryArithmetic.toNat W - SubexponentialSAT.BinaryArithmetic.toNat N + SubexponentialSAT.BinaryArithmetic.toNat P ∧
      out.length ≤ W.length+N.length+P.length+1 ∧ diff.length ≤ W.length+N.length := by
  obtain ⟨ts, diff, hts, hes, hvs, hls⟩ :=
    SubexponentialSAT.SaturatingSubtractionProgram.command_eval regs W N
  have hstart : projectState id subtractPort (shiftState regs W N P [] []) =
      SubexponentialSAT.SaturatingSubtractionProgram.state regs W N [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i; fin_cases i <;> rfl
  have htrace := compiled_halt_trace hes 0 2
  rw [← hstart] at htrace
  have hcall := eval_call_from_state SubexponentialSAT.SaturatingSubtractionProgram.program id subtractPort
    (shiftState regs W N P [] []) Function.injective_id subtractPort_injective htrace
  have hend : embedState id subtractPort (shiftState regs W N P [] [])
      (SubexponentialSAT.SaturatingSubtractionProgram.state (fun _ => false) W N diff) =
      shiftState (fun _ => false) W N P diff [] := by
    apply embedState_eq_of_ports id subtractPort _ _ _ Function.injective_id subtractPort_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> try rfl
      exact (hi ⟨2,rfl⟩).elim
  rw [hend] at hcall
  let a := shiftState (fun _ => false) W N P diff []
  have ha : Valid shiftAddPorts a := by
    constructor
    · rfl
    · intro i; fin_cases i <;> rfl
  obtain ⟨ta, rf, out, hea, hva, hla, hta⟩ := addAt_eval shiftAddPorts a ha
  have hout : (⟨rf, Function.update a.stacks shiftAddPorts.out out⟩ : ShiftData) =
      shiftState rf W N P diff out := by
    apply congrArg (StructuredProgram.State.mk rf)
    funext i; fin_cases i <;> rfl
  rw [hout] at hea
  refine ⟨ts+1+ta, ?_, rf, diff, out, hcall.seq hea, ?_, ?_, hls⟩
  · have hl : (a.stacks shiftAddPorts.left).length + (a.stacks shiftAddPorts.right).length+1 ≤
        W.length+N.length+P.length+1 := by simpa [a,shiftState,shiftAddPorts] using Nat.add_le_add_right hls (P.length+1)
    have ht := hta.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hl 2))
    nlinarith
  · simpa [a,shiftState,shiftAddPorts,hvs] using hva
  · have hl : diff.length+P.length+1 ≤ W.length+N.length+P.length+1 := by omega
    exact (by simpa [a,shiftState,shiftAddPorts] using hla : out.length ≤ diff.length+P.length+1).trans hl

theorem shiftCommand_eval (regs : Fin 8 → Bool) (W N P : List Bool) :
    ∃ t ≤ 300*(W.length+N.length+P.length+1)^2, ∃ rf diff out,
      Eval shiftCommand t (shiftState regs W N P [] []) (shiftState rf W N P diff out) ∧
      SubexponentialSAT.BinaryArithmetic.toNat out =
        SubexponentialSAT.BinaryArithmetic.toNat W - SubexponentialSAT.BinaryArithmetic.toNat N + SubexponentialSAT.BinaryArithmetic.toNat P ∧
      out.length ≤ W.length+N.length+P.length+1 := by
  obtain ⟨t,ht,rf,diff,out,he,hv,hl,hd⟩ := shiftCommand_eval_lengths regs W N P
  exact ⟨t,ht,rf,diff,out,he,hv,hl⟩

theorem shift_value_integer (W N P : ℕ) (hNW : N ≤ W) :
    ((W-N+P : ℕ) : ℤ) = (W : ℤ) + ((P : ℤ)-(N : ℤ)) := by
  rw [Nat.cast_add, Int.natCast_sub hNW]
  ring

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
