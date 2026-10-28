import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramReuse
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-! Explicit framed input parsing for streams of signed binary word pairs. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev WordPair := List Bool × List Bool
abbrev StreamData := State 8 16

def pairValue (w : WordPair) : ℤ := signedValue w.1 w.2
def pairLength (w : WordPair) : ℕ := w.1.length+w.2.length

def streamData (regs : Fin 8 → Bool) (acc next : WordPair) (queue : List Bool) : StreamData :=
  ⟨regs, fun j => if j=0 then acc.1 else if j=1 then acc.2 else
    if j=2 then next.1 else if j=3 then next.2 else if j=15 then queue else []⟩

def pairEncoding : List WordPair → List Bool
  | [] => [false]
  | a :: rest => true :: (Encoding.frame a.1.reverse ++
      (Encoding.frame a.2.reverse ++ pairEncoding rest))

def positiveReader : RecordPrograms.Ports 8 16 :=
  ⟨0,1,7,15,2, by decide, by decide, by decide, by decide⟩
def negativeReader : RecordPrograms.Ports 8 16 :=
  ⟨0,1,7,15,3, by decide, by decide, by decide, by decide⟩

abbrev parsePair : Cmd 8 16 :=
  .seq (.base (.atom (.pop 15 7 6)))
    (.ite 7 (.seq (RecordPrograms.reader positiveReader)
      (RecordPrograms.reader negativeReader)) (.base .skip))

private theorem atom_pop_nil (regs : Fin 8 → Bool) (acc : WordPair) :
    ∃ regs', regs' 7 = false ∧
      Eval parsePair 2 (streamData regs acc ([],[]) [false])
        (streamData regs' acc ([],[]) []) := by
  let d := streamData regs acc ([],[]) [false]
  let a := (StructuredProgram.Atom.pop 15 7 6).eval d
  have hg : a.regs 7 = false := by
    simp [a, d, streamData, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs]
  have ha : a = streamData a.regs acc ([],[]) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases j <;>
        simp [ d, streamData, StructuredProgram.Atom.instr, execInstr]
  refine ⟨a.regs, hg, ?_⟩
  rw [← ha]
  exact (Eval.base (StructuredProgram.Eval.atom (.pop 15 7 6) d)).seq
    (Eval.ite_false hg (.base (.skip a)))

theorem parsePair_nil (regs : Fin 8 → Bool) (acc : WordPair) :
    ∃ regs', regs' 7 = false ∧
      Eval parsePair 2 (streamData regs acc ([],[]) (pairEncoding []))
        (streamData regs' acc ([],[]) []) := atom_pop_nil regs acc

theorem parsePair_cons (regs : Fin 8 → Bool) (acc next : WordPair) (rest : List WordPair) :
    ∃ regs', regs' 7 = true ∧
      Eval parsePair (6*pairLength next+10)
        (streamData regs acc ([],[]) (pairEncoding (next::rest)))
        (streamData regs' acc next (pairEncoding rest)) := by
  let d := streamData regs acc ([],[]) (pairEncoding (next::rest))
  let a := (StructuredProgram.Atom.pop 15 7 6).eval d
  have hg : a.regs 7 = true := by
    simp [a, d, streamData, pairEncoding, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  have hs : a.stacks 15 = Encoding.frame next.1.reverse ++
      (Encoding.frame next.2.reverse ++ pairEncoding rest) := by
    simp [a, d, streamData, pairEncoding, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  have hp : a.stacks 2 = [] := rfl
  have hi := RecordPrograms.state_eq_self positiveReader a (a.regs 0) (a.regs 1)
    (a.regs 7) _ [] rfl rfl rfl hs hp
  have hr := RecordPrograms.reader_eval positiveReader a next.1.reverse
    (Encoding.frame next.2.reverse ++ pairEncoding rest) [] (a.regs 0) (a.regs 1) (a.regs 7)
  rw [hi] at hr
  let b := RecordPrograms.state positiveReader a false true (a.regs 7)
    (Encoding.frame next.2.reverse ++ pairEncoding rest) next.1
  have hr' : Eval (RecordPrograms.reader positiveReader) (6*next.1.length+4) a b := by
    simpa [b] using hr
  have hs2 : b.stacks 15 = Encoding.frame next.2.reverse ++ pairEncoding rest := by
    simp [b, positiveReader, RecordPrograms.state]
  have hn : b.stacks 3 = [] := by
    simp [b, a, d, positiveReader, RecordPrograms.state, streamData,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  have hi2 := RecordPrograms.state_eq_self negativeReader b (b.regs 0) (b.regs 1)
    (b.regs 7) _ [] rfl rfl rfl hs2 hn
  have hr2 := RecordPrograms.reader_eval negativeReader b next.2.reverse
    (pairEncoding rest) [] (b.regs 0) (b.regs 1) (b.regs 7)
  rw [hi2] at hr2
  let c := RecordPrograms.state negativeReader b false true (b.regs 7)
    (pairEncoding rest) next.2
  have hr2' : Eval (RecordPrograms.reader negativeReader) (6*next.2.length+4) b c := by
    simpa [c] using hr2
  have hc : c = streamData c.regs acc next (pairEncoding rest) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases j <;>
        simp [ b, a, d, positiveReader, negativeReader, RecordPrograms.state,
          streamData, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
  refine ⟨c.regs, ?_, ?_⟩
  · simpa [c, b, negativeReader, positiveReader, RecordPrograms.state] using hg
  · rw [← hc]
    convert (Eval.base (StructuredProgram.Eval.atom (.pop 15 7 6) d)).seq
      (Eval.ite_true (no := .base .skip) hg (hr'.seq hr2')) using 1 ;
      simp [ pairLength] ; omega

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
