import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramSupport

namespace OAI.Algorithms

/-! Native scan used by exact-support projection: consume a mask while
copying its bits and an equally long zero mask to reversed accumulators. -/
namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

abbrev MaskData := State 3 3

def maskData (regs : Fin 3 → Bool) (source copy zeros : List Bool) : MaskData :=
  ⟨regs, ![source,copy,zeros]⟩

def ready (regs : Fin 3 → Bool) (source copy zeros : List Bool) : MaskData :=
  maskData (readRegs regs 0 1 source.head?) source copy zeros

abbrev body : Cmd 3 3 :=
  .seq (.atom (.pop 0 0 1)) (.seq (.atom (.push 1 0))
    (.seq (.atom (.set 2 false)) (.seq (.atom (.push 2 2)) (.atom (.peek 0 0 1)))))
abbrev loop : Cmd 3 3 := .while 1 body
abbrev scan : Cmd 3 3 := .seq (.atom (.peek 0 0 1)) loop

theorem body_eval (regs : Fin 3 → Bool) (b : Bool) (source copy zeros : List Bool) :
    ∃ rf, Eval body 5 (maskData regs (b::source) copy zeros)
      (ready rf source (b::copy) (false::zeros)) := by
  let d := maskData regs (b::source) copy zeros
  let d1 := (Atom.pop (0:Fin 3) (0:Fin 3) 1).eval d
  let d2 := (Atom.push (1:Fin 3) (0:Fin 3)).eval d1
  let d3 := (Atom.set (2:Fin 3) false).eval d2
  let d4 := (Atom.push (2:Fin 3) (2:Fin 3)).eval d3
  refine ⟨d3.regs, ?_⟩
  have h := (Eval.atom (Atom.pop (0:Fin 3) (0:Fin 3) 1) d).seq
    ((Eval.atom (Atom.push (1:Fin 3) (0:Fin 3)) d1).seq
    ((Eval.atom (Atom.set (2:Fin 3) false) d2).seq
    ((Eval.atom (Atom.push (2:Fin 3) (2:Fin 3)) d3).seq
     (Eval.atom (Atom.peek (0:Fin 3) (0:Fin 3) 1) d4))))
  convert h using 1 ;
    simp [d,d1,d2,d3,d4,ready,maskData,Atom.eval,Atom.instr,
      State.ofCfg,execInstr,readRegs,Function.update] ;
    try (funext i; fin_cases i <;> rfl)

@[simp] theorem ready_guard (regs : Fin 3 → Bool) (source copy zeros : List Bool) :
    (ready regs source copy zeros).regs 1 = !source.isEmpty := by
  cases source <;> simp [ready,maskData,readRegs]

theorem loop_eval (source copy zeros : List Bool) (regs : Fin 3 → Bool) :
    ∃ rf, Eval loop (6*source.length+1) (ready regs source copy zeros)
      (maskData rf [] (source.reverse++copy) (List.replicate source.length false++zeros)) := by
  induction source generalizing copy zeros regs with
  | nil =>
      refine ⟨(ready regs [] copy zeros).regs, ?_⟩
      simpa [loop,ready,maskData] using
        (Eval.while_false (body:=body) (ready_guard regs [] copy zeros))
  | cons b source ih =>
      obtain ⟨mid,hm⟩ := body_eval (ready regs (b::source) copy zeros).regs b source copy zeros
      obtain ⟨rf,hf⟩ := ih (b::copy) (false::zeros) mid
      refine ⟨rf,?_⟩
      have h := Eval.while_true
        (by simp : (ready regs (b::source) copy zeros).regs 1 = true) hm hf
      have ht : 5+(6*source.length+1)+1 = 6*(b::source).length+1 := by simp;omega
      rw [ht] at h
      have hz : List.replicate source.length false ++ false :: zeros =
          false :: (List.replicate source.length false ++ zeros) := by
        simpa [List.replicate_add,List.append_assoc] using
          congrArg (fun n => List.replicate n false ++ zeros) (Nat.add_comm source.length 1)
      simpa [loop,ready,maskData,List.reverse_cons,List.append_assoc,
        List.replicate_succ,hz] using h

theorem scan_eval (source copy zeros : List Bool) (regs : Fin 3 → Bool) :
    ∃ rf, Eval scan (6*source.length+2) (maskData regs source copy zeros)
      (maskData rf [] (source.reverse++copy) (List.replicate source.length false++zeros)) := by
  obtain ⟨rf,hf⟩ := loop_eval source copy zeros regs
  refine ⟨rf,?_⟩
  have hp : Eval (.atom (.peek 0 0 1)) 1 (maskData regs source copy zeros)
      (ready regs source copy zeros) := Eval.atom _ _
  have ht : 1+(6*source.length+1) = 6*source.length+2 := by omega
  simpa only [scan,ht] using hp.seq hf

def scanProgram := compiled scan 0 1

theorem scan_trace (source copy zeros : List Bool) (regs : Fin 3 → Bool) :
    ∃ rf, Trace scanProgram (6*source.length+3)
      ((maskData regs source copy zeros).withPC (some scanProgram.entry))
      ((maskData rf [] (source.reverse++copy) (List.replicate source.length false++zeros)).withPC none) := by
  obtain ⟨rf,h⟩ := scan_eval source copy zeros regs
  exact ⟨rf,by simpa [scanProgram,Nat.add_assoc] using compiled_halt_trace h 0 1⟩

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
