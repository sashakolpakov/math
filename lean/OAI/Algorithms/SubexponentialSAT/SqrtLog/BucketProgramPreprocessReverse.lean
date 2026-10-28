import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

namespace OAI.Algorithms

/-! A fixed EOF-controlled reversal of a raw list of framed words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev PreReverseData := State 8 4
abbrev PreReverseCode := Cmd 8 4

abbrev preReverseState (regs : Fin 8 → Bool) (xs : List (List Bool))
    (out : List Bool) : PreReverseData := ⟨regs, ![words xs,[],[],out]⟩

abbrev preReverseStep : PreReverseCode :=
  .seq (readWord 0 1 2 (by decide)) (emitFrame 1 3 2 (by decide))

theorem preReverseStep_eval (regs : Fin 8 → Bool) (x : List Bool)
    (xs : List (List Bool)) (out : List Bool) :
    ∃ rf, Eval preReverseStep (17*x.length+15)
      (preReverseState regs (x::xs) out)
      (preReverseState rf xs (Encoding.frame x++out)) := by
  let d := preReverseState regs (x::xs) out
  obtain ⟨a,ha,hsa⟩ := readWord_eval (0 : Fin 4) 1 2
    (by decide) (by decide) (by decide) d x (words xs) rfl rfl rfl
  obtain ⟨b,hb,hsb⟩ := emitFrame_eval (1 : Fin 4) 3 2
    (by decide) (by decide) (by decide) a (by rw [hsa]; rfl)
  have ha1 : a.stacks 1=x := by rw [hsa]; rfl
  have hend : b=preReverseState b.regs xs (Encoding.frame x++out) := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    rw [hsb,hsa]
    funext i; fin_cases i <;> rfl
  have he := ha.seq hb
  rw [hend,ha1] at he
  exact ⟨b.regs, by convert he using 1 ; omega⟩

abbrev preReversePeek : PreReverseCode := .base (.atom (.peek 0 0 1))
abbrev preReverseBody : PreReverseCode := .seq preReverseStep preReversePeek
abbrev preReverseLoop : PreReverseCode := .while 1 preReverseBody
abbrev preReverseCommand : PreReverseCode := .seq preReversePeek preReverseLoop
abbrev preReverseProgram := compiled preReverseCommand 0 3

abbrev preReverseReady (regs : Fin 8 → Bool) (xs : List (List Bool))
    (out : List Bool) : PreReverseData :=
  preReverseState (readRegs regs 0 1 (words xs).head?) xs out

def preReverseCost (xs : List (List Bool)) : ℕ :=
  (xs.map (fun x => 17*x.length+17)).sum+1

theorem preReversePeek_eval (regs : Fin 8 → Bool) (xs : List (List Bool))
    (out : List Bool) : Eval preReversePeek 1 (preReverseState regs xs out)
      (preReverseReady regs xs out) := Eval.base (StructuredProgram.Eval.atom _ _)

theorem preReverseLoop_eval (regs : Fin 8 → Bool) (xs : List (List Bool))
    (out : List Bool) : ∃ rf,
    Eval preReverseLoop (preReverseCost xs) (preReverseReady regs xs out)
      (preReverseState rf [] (words xs.reverse++out)) := by
  induction xs generalizing regs out with
  | nil =>
      refine ⟨(preReverseReady regs [] out).regs, ?_⟩
      change Eval preReverseLoop 1 (preReverseReady regs [] out) (preReverseReady regs [] out)
      exact Eval.while_false (show (preReverseReady regs [] out).regs 1 = false by
        simp [words, readRegs])
  | cons x xs ih =>
      obtain ⟨rm,hm⟩ := preReverseStep_eval (preReverseReady regs (x::xs) out).regs x xs out
      obtain ⟨rf,hf⟩ := ih rm (Encoding.frame x++out)
      have hg : (preReverseReady regs (x::xs) out).regs 1=true := by
        cases x <;> simp [words,Encoding.frame,readRegs]
      have he := Eval.while_true hg (hm.seq (preReversePeek_eval rm xs _)) hf
      refine ⟨rf, ?_⟩
      convert he using 1 <;>
        simp [preReverseCost,List.reverse_cons,words_append,words,List.append_assoc] ; omega

theorem preReverseCommand_eval (regs : Fin 8 → Bool) (xs : List (List Bool))
    (out : List Bool) : ∃ rf,
    Eval preReverseCommand (preReverseCost xs+1) (preReverseState regs xs out)
      (preReverseState rf [] (words xs.reverse++out)) := by
  obtain ⟨rf,hf⟩ := preReverseLoop_eval regs xs out
  exact ⟨rf, by simpa [Nat.add_comm] using (preReversePeek_eval regs xs out).seq hf⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
