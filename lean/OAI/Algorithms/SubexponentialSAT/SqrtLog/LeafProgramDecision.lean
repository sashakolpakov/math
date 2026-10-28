import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.PositiveWordProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! The final SAT bit is obtained by scanning the physically computed integer
count. The count tape is consumed and the exact one-bit answer is emitted. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Decision

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 2 2
def data (regs : Fin 2 → Bool) (count answer : List Bool) : Data :=
  ⟨regs,![count,answer]⟩

abbrev positive : Cmd 2 2 :=
  .call (ProgramLinking.liftProgram PositiveWordProgram.program id (Fin.castAdd 1))
abbrev finish : Cmd 2 2 :=
  .seq (.base (.atom (.pop 0 0 1)))
    (.seq (.base (.atom (.push 1 0))) (.call (StackRoutines.clearProgram 0 0 1)))
abbrev command : Cmd 2 2 := .seq positive finish
def program := compiled command 0 1

theorem embedded (frameRegs regs : Fin 2 → Bool) (old word answer : List Bool) :
    embedState id (Fin.castAdd 1) (data frameRegs old answer)
      (⟨regs,fun _ : Fin 1 => word⟩ : State 2 1) = data regs word answer := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (Fin.castAdd_injective 1 1)
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i; rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0,rfl⟩)
    · rfl

theorem positive_eval (word answer : List Bool) (v pr : Bool) :
    Eval positive (PositiveWordProgram.cost word)
      (data (PositiveWordProgram.regs v pr) word answer)
      (data (PositiveWordProgram.regs (PositiveWordProgram.positive word)
        (PositiveWordProgram.positive word))
        (PositiveWordProgram.positive word :: PositiveWordProgram.residual word) answer) := by
  have h := PositiveWordProgram.run word v pr
  change Trace PositiveWordProgram.program (PositiveWordProgram.cost word)
    ((⟨PositiveWordProgram.regs v pr,fun _ : Fin 1 => word⟩ : State 2 1).withPC
      (some PositiveWordProgram.program.entry))
    ((⟨PositiveWordProgram.regs (PositiveWordProgram.positive word) (PositiveWordProgram.positive word),
      fun _ : Fin 1 => PositiveWordProgram.positive word :: PositiveWordProgram.residual word⟩ : State 2 1).withPC none) at h
  have he := eval_call_lifted PositiveWordProgram.program id (Fin.castAdd 1)
    (data (PositiveWordProgram.regs v pr) word answer)
    Function.injective_id (Fin.castAdd_injective 1 1) h
  simpa only [positive,embedded] using he

theorem finish_eval (regs : Fin 2 → Bool) (bit : Bool) (rest : List Bool) :
    Eval finish (2*rest.length+5) (data regs (bit::rest) [])
      (data (fun _ => false) [] [bit]) := by
  let r := readRegs regs 0 1 (some bit)
  have h1 : Eval (.base (.atom (.pop 0 0 1))) 1 (data regs (bit::rest) []) (data r rest []) := by
    convert Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 2) (0 : Fin 2) 1) (data regs (bit::rest) [])) using 1 ;
      simp [data,r,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr] ;
      (try (funext i; fin_cases i <;> rfl))
  have h2 : Eval (.base (.atom (.push 1 0))) 1 (data r rest []) (data r rest [bit]) := by
    convert Eval.base (StructuredProgram.Eval.atom (.push (1 : Fin 2) (0 : Fin 2)) (data r rest [])) using 1 ;
      simp [data,r,readRegs,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr] ;
      (try (funext i; fin_cases i <;> rfl))
  have h3 : Eval (.call (StackRoutines.clearProgram 0 0 1)) (2*rest.length+3)
      (data r rest [bit]) (data (fun _ => false) [] [bit]) := by
    have h := ListRegisterProgram.clear_run (0 : Fin 2) (0 : Fin 2) 1 r (data r rest [bit]).stacks
    have he : Eval (.call (StackRoutines.clearProgram (0 : Fin 2) (0 : Fin 2) 1))
        (2*rest.length+3) (data r rest [bit])
        ⟨readRegs r 0 1 none,StackRoutines.clearStacks 0 (data r rest [bit]).stacks⟩ :=
      Eval.call _ h
    have hstate : (⟨readRegs r 0 1 none,StackRoutines.clearStacks 0 (data r rest [bit]).stacks⟩ : Data) =
        data (fun _ => false) [] [bit] := by
      apply congrArg₂ StructuredProgram.State.mk
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
    rw [hstate] at he
    exact he
  convert h1.seq (h2.seq h3) using 1 ; first | rfl | omega

theorem residual_length_le (word : List Bool) :
    (PositiveWordProgram.residual word).length ≤ word.length := by
  induction word with
  | nil => simp [PositiveWordProgram.residual]
  | cons b bs ih => cases b <;> simp [PositiveWordProgram.residual] ; omega

theorem program_run (word : List Bool) (v pr : Bool) :
    RunsIn program (5*word.length+11)
      ((data (PositiveWordProgram.regs v pr) word []).withPC (some program.entry))
      ((data (fun _ => false) [] [PositiveWordProgram.positive word]).withPC none) := by
  have h := (positive_eval word [] v pr).seq (finish_eval _ _ _)
  refine ⟨PositiveWordProgram.cost word + (2*(PositiveWordProgram.residual word).length+5)+1,?_,
    compiled_halt_trace h 0 1⟩
  have hc := PositiveWordProgram.cost_le word
  have hl := residual_length_le word
  omega

theorem answer_iff (word : List Bool) (count : ℕ) (h : BinaryArithmetic.toNat word = count) :
    PositiveWordProgram.positive word = true ↔ 0 < count := by
  rw [PositiveWordProgram.positive_iff,h]

end SubexponentialSAT.SqrtLog.LeafProgram.Decision

end OAI.Algorithms
