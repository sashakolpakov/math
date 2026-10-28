import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgramCore

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram

abbrev clearOne (i : Fin 15) : Cmd 8 22 := ArithmeticExpressionSupport.clearCmd (port i)

abbrev clearMany : List (Fin 15) → Cmd 8 22
  | [] => .base .skip
  | i::is => .seq (clearOne i) (clearMany is)

abbrev erased : List (Fin 15) → Words → Words
  | [],w => w
  | i::is,w => erased is (Function.update w i [])

theorem clearOne_eval (regs : Regs) (w : Words) (i : Fin 15) :
    Eval (clearOne i) (2*(w i).length+3) (bank regs w)
      (bank (readRegs regs 0 1 none) (Function.update w i [])) := by
  have h := ArithmeticExpressionSupport.clear_eval (port i) (bank regs w)
  simpa only [clearOne, bank, state_port, state_update,
    SubexpBlockParameterProgram.state_regs] using h

theorem clearMany_eval (is : List (Fin 15)) (regs : Regs) (w : Words) (H : ℕ)
    (hw : ∀ i ∈ is,(w i).length ≤ H) :
    ∃ ticks rf, Eval (clearMany is) ticks (bank regs w) (bank rf (erased is w)) ∧
      ticks ≤ is.length*(2*H+3) := by
  induction is generalizing regs w with
  | nil => exact ⟨0,regs,.base (.skip _),by simp⟩
  | cons i is ih =>
      have hi := hw i (by simp)
      have ht : ∀ j ∈ is,((Function.update w i []) j).length ≤ H := by
        intro j hj
        by_cases he : j=i
        · subst j
          simpa only [Function.update_self,List.length_nil] using (Nat.zero_le H)
        · simpa [Function.update_apply,he] using hw j (by simp [hj])
      obtain ⟨t,rf,he,hle⟩ := ih (readRegs regs 0 1 none) (Function.update w i []) ht
      refine ⟨2*(w i).length+3+t,rf,(clearOne_eval regs w i).seq he,?_⟩
      simp only [List.length_cons,Nat.add_mul]
      omega

abbrev scratch : List (Fin 15) := [3,4,5,6,7,8]

abbrev command : Cmd 8 22 := .seq core (.seq (clearMany scratch) RegisterResetProgram.all)
abbrev program := compiled command 0 9

abbrev input (regs : Regs) (B Q R : List Bool) : Data := bank regs (initial B Q R)
abbrev result (B Q R out : List Bool) : Data := bank (fun _ => false) (Function.update (initial B Q R) 9 out)

theorem erased_filled (B Q R a e p b out : List Bool) :
    erased scratch (filled B Q R a e p b out)=Function.update (initial B Q R) 9 out := by
  funext i
  fin_cases i <;> simp [erased,filled,loaded,initial,inputWords]

/-- A fixed command computes the offset and restores its local workspace. The
extra tick in the bound also pays for the standalone program's halt. -/
theorem command_eval (regs : Regs) (B Q R : List Bool) :
    ∃ ticks out, Eval command ticks (input regs B Q R) (result B Q R out) ∧
      BinaryArithmetic.toNat out=2*BinaryArithmetic.toNat B*(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) ∧
      out.length ≤ outputLength B Q R ∧ ticks+1 ≤ budget B Q R := by
  obtain ⟨tc,rc,a,e,p,b,out,hc,hval,hlen,hw,htc⟩ := core_eval regs B Q R
  obtain ⟨tz,rz,hz,htz⟩ := clearMany_eval scratch rc (filled B Q R a e p b out) (width B Q R) hw
  rw [erased_filled] at hz
  have hr := RegisterResetProgram.all_eval (bank rz (Function.update (initial B Q R) 9 out))
  have he := hc.seq (hz.seq hr)
  have hresult : RegisterResetProgram.zeroed (bank rz (Function.update (initial B Q R) 9 out))=
      result B Q R out := rfl
  rw [hresult] at he
  refine ⟨tc+(tz+8),out,he,hval,hlen,?_⟩
  have hH := width_pos B Q R
  have hs : width B Q R ≤ (width B Q R)^2 := by nlinarith only [hH]
  simp only [scratch,List.length_cons,List.length_nil] at htz
  unfold budget coreBudget at *
  nlinarith only [htc,htz,hH,hs]

/-- A single fixed binary-stack machine computes the offset, retains all three
source words, clears temporary data, and resets its eight Boolean registers. -/
theorem program_runsIn (regs : Regs) (B Q R : List Bool) :
    ∃ out, BinaryArithmetic.toNat out=2*BinaryArithmetic.toNat B*(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) ∧
      out.length ≤ outputLength B Q R ∧
      RunsIn program (budget B Q R)
        ((input regs B Q R).withPC (some program.entry)) ((result B Q R out).withPC none) := by
  obtain ⟨ticks,out,he,hval,hlen,ht⟩ := command_eval regs B Q R
  exact ⟨out,hval,hlen,ticks+1,ht,compiled_halt_trace he 0 9⟩

theorem program_primitive (regs : Regs) (B Q R : List Bool) :
    ∃ out, BinaryArithmetic.toNat out=2*BinaryArithmetic.toNat B*(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) ∧
      out.length ≤ outputLength B Q R ∧
      Computation.RunsIn (primitive program).step (primitiveOverhead program*budget B Q R)
        (primitiveCfg program ((input regs B Q R).withPC (some program.entry)))
        (primitiveCfg program ((result B Q R out).withPC none)) := by
  obtain ⟨out,hv,hl,he⟩ := program_runsIn regs B Q R
  exact ⟨out,hv,hl,primitive_execution program he⟩

theorem result_frame (B Q R out : List Bool) (i : Fin 22) (hi : i≠9) :
    (result B Q R out).stacks i=(bank (fun _ => false) (initial B Q R)).stacks i := by
  by_cases h : i.val < 15
  · have hne : (⟨i.val,h⟩ : Fin 15)≠9 := by
      intro he
      apply hi
      apply Fin.ext
      exact congrArg (fun x : Fin 15 => x.val) he
    simp [result,bank,state,h,hne]
  · simp [result,bank,state,h]

/-- Explicit polynomial in the numerical R and the physical source widths. -/
theorem budget_eq (B Q R : List Bool) :
    budget B Q R=5000*(2*BinaryArithmetic.toNat R+1)^2*(B.length+Q.length+R.length+11)^2 := by
  unfold budget width sourceWidth
  ring

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
