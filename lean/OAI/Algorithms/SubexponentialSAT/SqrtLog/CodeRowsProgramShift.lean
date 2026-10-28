import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramShiftBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def result (side : Bool) (pairs : List (Bool × Bool)) : List Bool :=
  pairs.map fun p => bit side p.1 p.2

private theorem split_seq {c d : Cmd 8 4} {n : ℕ} {a b : Data}
    (h : Eval (.seq c d) n a b) :
    ∃ nc nd middle, n=nc+nd ∧ Eval c nc a middle ∧ Eval d nd middle b := by
  cases h with
  | seq hc hd => exact ⟨_,_,_,rfl,hc,hd⟩

theorem loop_eval (pairs : List (Bool × Bool)) (side : Bool)
    (regs : Fin 8 → Bool) (hside : regs 7=side) (tail accum out : List Bool) :
    ∃ rf, rf 7=side ∧ Eval loop (11*pairs.length+2)
      (state regs (frames (pairs.map Prod.snd)++tail) (pairs.map Prod.fst) accum out)
      (state rf tail [] ((result side pairs).reverse++accum) out) := by
  induction pairs generalizing regs accum with
  | nil =>
    let rr := readRegs regs 4 5 none
    refine ⟨rr,by simpa [rr,readRegs] using hside,?_⟩
    have h := (pop_nil regs tail accum out).seq (Eval.while_false (body := .seq step pop)
      (show (state rr tail [] accum out).regs 5=false by simp [state,rr,readRegs]))
    simpa [loop,frames,result] using h
  | cons p pairs ih =>
    rcases p with ⟨v,s⟩
    let source := frames (pairs.map Prod.snd)++tail
    let rr := readRegs regs 4 5 (some v)
    have hp := pop_cons regs v (Cell.frame s false++source) (pairs.map Prod.fst) accum out
    obtain ⟨rs,hrs,hs⟩ := step_eval rr side v s (by simpa [rr,readRegs] using hside)
      (by simp [rr,readRegs]) source (pairs.map Prod.fst) accum out
    obtain ⟨rf,hrf,hi⟩ := ih rs hrs (bit side v s::accum)
    obtain ⟨tn,tw,between,hncost,hn,hw⟩ := split_seq hi
    refine ⟨rf,hrf,?_⟩
    have hg : (state rr (Cell.frame s false++source) (pairs.map Prod.fst) accum out).regs 5=true := by
      simp [state,rr,readRegs]
    have he := hp.seq (Eval.while_true hg (hs.seq hn) hw)
    convert he using 1 <;>
      simp_all [frames,source,result,List.append_assoc,List.reverse_cons] ; omega

theorem command_eval (pairs : List (Bool × Bool)) (side : Bool)
    (regs : Fin 8 → Bool) (hside : regs 7=side) (tail : List Bool) :
    ∃ rf, rf 7=side ∧ Eval command (14*pairs.length+5)
      (state regs (frames (pairs.map Prod.snd)++tail) (pairs.map Prod.fst) [] [])
      (state rf tail [] [] (result side pairs)) := by
  obtain ⟨rr,hrr,hl⟩ := loop_eval pairs side regs hside tail [] []
  have ht := Subexp.TupleProgram.transfer_eval (2 : Fin 4) 3 (0 : Fin 8) 1
    (by decide) (by decide) (state rr tail [] ((result side pairs).reverse++[]) [])
  let rf := readRegs rr 0 1 none
  refine ⟨rf,by simpa [rf,readRegs] using hrr,?_⟩
  have he := hl.seq ht
  convert he using 1
  · simp [state,result]
    omega
  · apply congrArg (StructuredProgram.State.mk rf)
    funext i
    fin_cases i <;> simp [state,StackRoutines.transferStacks,result]

theorem program_runsIn (pairs : List (Bool × Bool)) (side : Bool)
    (regs : Fin 8 → Bool) (hside : regs 7=side) (tail : List Bool) :
    ∃ rf, rf 7=side ∧ RunsIn program (14*pairs.length+6)
      ((state regs (frames (pairs.map Prod.snd)++tail) (pairs.map Prod.fst) [] []).withPC
        (some program.entry))
      ((state rf tail [] [] (result side pairs)).withPC none) := by
  obtain ⟨rf,hr,he⟩ := command_eval pairs side regs hside tail
  exact ⟨rf,hr,14*pairs.length+6,le_rfl,compiled_halt_trace he 0 3⟩

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

end OAI.Algorithms
