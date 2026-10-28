import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentCode

namespace OAI.Algorithms

/-!
# Fixed-control generation of the sparse keys used by incidence arguments

Counters are runtime unary stacks. No dimension or degree parameter occurs in
the instruction table. The output buffer is built in reverse order for direct
consumption by the framed-record writer.
-/

namespace SubexponentialSAT.SubexpArgumentKeyProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 4 5

def regs (v p mark u : Bool) : Fin 4 → Bool := SubexpPostfixControl.quadruple v p mark u

def counterPort (i : Fin 3) : Fin 5 := Fin.castAdd 2 i

def storage (counts : Fin 3 → List Bool) (width output : List Bool) : Fin 5 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (3 + 2) => List Bool) counts (ParserProgram.pair width output)

def state (v p mark u : Bool) (counts : Fin 3 → List Bool) (width output : List Bool) : Data :=
  ⟨regs v p mark u, storage counts width output⟩

@[simp] theorem stacks_counter (counts : Fin 3 → List Bool) (width output : List Bool) (i : Fin 3) :
    storage counts width output (counterPort i) = counts i := by
  fin_cases i <;> rfl

@[simp] theorem stacks_width (counts : Fin 3 → List Bool) (width output : List Bool) :
    storage counts width output 3 = width := rfl

@[simp] theorem stacks_output (counts : Fin 3 → List Bool) (width output : List Bool) :
    storage counts width output 4 = output := rfl

theorem update_counter (counts : Fin 3 → List Bool) (width output word : List Bool) (i : Fin 3) :
    Function.update (storage counts width output) (counterPort i) word =
      storage (Function.update counts i word) width output := by
  funext j
  fin_cases i <;> fin_cases j <;> rfl

theorem update_width (counts : Fin 3 → List Bool) (width output word : List Bool) :
    Function.update (storage counts width output) 3 word = storage counts word output := by
  funext j
  fin_cases j <;> rfl

theorem update_output (counts : Fin 3 → List Bool) (width output word : List Bool) :
    Function.update (storage counts width output) 4 word = storage counts width word := by
  funext j
  fin_cases j <;> rfl

abbrev atom (a : StructuredProgram.Atom 4 5) : Cmd 4 5 := .base (.atom a)

/-- Emit one key bit and account for one position in the target width. -/
abbrev emitBit (b : Bool) : Cmd 4 5 :=
  .seq (atom (.set 0 b)) (.seq (atom (.push 4 0)) (atom (.pop 3 0 1)))

theorem emitBit_eval (b v p mark u : Bool) (counts : Fin 3 → List Bool)
    (width output : List Bool) :
    Eval (emitBit b) 3 (state v p mark u counts width output)
      (state (width.head?.getD false) width.head?.isSome mark u counts width.tail (b :: output)) := by
  have hs : Eval (atom (.set 0 b)) 1 (state v p mark u counts width output)
      (state b p mark u counts width output) := by
    have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.set (0 : Fin 4) b)
      (state v p mark u counts width output)
    apply Eval.base
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
      state, regs, SubexpPostfixControl.quadruple] using h
  have hp : Eval (atom (.push 4 0)) 1 (state b p mark u counts width output)
      (state b p mark u counts width (b :: output)) := by
    have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.push (4 : Fin 5) (0 : Fin 4))
      (state b p mark u counts width output)
    apply Eval.base
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
      state, regs, SubexpPostfixControl.quadruple, update_output] using h
  have ht : Eval (atom (.pop 3 0 1)) 1 (state b p mark u counts width (b :: output))
      (state (width.head?.getD false) width.head?.isSome mark u counts width.tail (b :: output)) := by
    have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (3 : Fin 5) (0 : Fin 4) 1)
      (state b p mark u counts width (b :: output))
    apply Eval.base
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
      state, regs, readRegs, SubexpPostfixControl.quadruple, update_width] using h
  exact Eval.seq hs (Eval.seq hp ht)

abbrev popCounter (i : Fin 3) : Cmd 4 5 := atom (.pop (counterPort i) 0 1)

theorem popCounter_eval (i : Fin 3) (v p mark u : Bool) (counts : Fin 3 → List Bool)
    (width output : List Bool) :
    Eval (popCounter i) 1 (state v p mark u counts width output)
      (state ((counts i).head?.getD false) (counts i).head?.isSome mark u
        (Function.update counts i (counts i).tail) width output) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (counterPort i) (0 : Fin 4) 1)
    (state v p mark u counts width output)
  apply Eval.base
  simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    state, regs, readRegs, SubexpPostfixControl.quadruple, update_counter] using h

abbrev repeatLoop (i : Fin 3) (b : Bool) : Cmd 4 5 :=
  .while 1 (.seq (emitBit b) (popCounter i))

abbrev repeatBit (i : Fin 3) (b : Bool) : Cmd 4 5 := .seq (popCounter i) (repeatLoop i b)

theorem repeatLoop_eval (i : Fin 3) (b mark u : Bool) (word : List Bool)
    (counts : Fin 3 → List Bool) (width output : List Bool) :
    Eval (repeatLoop i b) (5 * word.length + 1)
      (state (word.head?.getD false) word.head?.isSome mark u
        (Function.update counts i word.tail) width output)
      (state false false mark u (Function.update counts i [])
        (width.drop word.length) (List.replicate word.length b ++ output)) := by
  induction word generalizing width output with
  | nil =>
    apply Eval.while_false
    rfl
  | cons a word ih =>
    have he := emitBit_eval b a true mark u (Function.update counts i word) width output
    have hp := popCounter_eval i (width.head?.getD false) width.head?.isSome mark u
      (Function.update counts i word) width.tail (b :: output)
    have hb : Eval (.seq (emitBit b) (popCounter i)) 4
        (state a true mark u (Function.update counts i word) width output)
        (state (word.head?.getD false) word.head?.isSome mark u
          (Function.update counts i word.tail) width.tail (b :: output)) := by
      simpa only [Function.update_self, Function.update_idem] using Eval.seq he hp
    have hrest := ih width.tail (b :: output)
    have h := Eval.while_true (test := (1 : Fin 4)) (by rfl) hb hrest
    have hd : width.tail.drop word.length = width.drop (word.length + 1) := by
      simpa only [List.drop_one, Nat.add_comm] using
        (List.drop_drop (i := word.length) (j := 1) (l := width))
    have ho : List.replicate word.length b ++ b :: output =
        List.replicate (word.length + 1) b ++ output := by
      simp [List.replicate_succ', List.append_assoc]
    have hn : 4 + (5 * word.length + 1) + 1 = 5 * (word.length + 1) + 1 := by omega
    simpa only [repeatLoop, List.head?_cons, Option.getD_some, Option.isSome_some,
      List.tail_cons, List.length_cons, hd, ho, hn] using h

theorem repeatBit_eval (i : Fin 3) (b v p mark u : Bool) (counts : Fin 3 → List Bool)
    (width output : List Bool) :
    Eval (repeatBit i b) (5 * (counts i).length + 2)
      (state v p mark u counts width output)
      (state false false mark u (Function.update counts i [])
        (width.drop (counts i).length) (List.replicate (counts i).length b ++ output)) := by
  have h := Eval.seq (popCounter_eval i v p mark u counts width output)
    (repeatLoop_eval i b mark u (counts i) counts width output)
  have hn : 1 + (5 * (counts i).length + 1) = 5 * (counts i).length + 2 := by omega
  simpa only [repeatBit, hn] using h

end SubexponentialSAT.SubexpArgumentKeyProgram

end OAI.Algorithms
