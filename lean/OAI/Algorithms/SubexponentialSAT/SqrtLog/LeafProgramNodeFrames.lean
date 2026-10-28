import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramWords

namespace OAI.Algorithms

/-! Paid conversion of flat fixed-width node words to framed node records.
Both the width and the number of nodes are read from runtime unary tapes. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeFrames

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpTaylorFrames
open SubexponentialSAT.SubexpExponentProgram

theorem chunks_flatten (B : ℕ) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = B) :
    chunks B words.length words.flatten = words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    have hword := hw word (by simp)
    have hrest : ∀ w ∈ words, w.length = B := fun w h => hw w (by simp [h])
    simp only [List.length_cons, List.flatten_cons, chunks]
    rw [show padTake B (word ++ words.flatten) = word by
      rw [← hword]
      simp [padTake ]]
    rw [show (word ++ words.flatten).drop B = words.flatten by
      rw [← hword]; simp]
    rw [ih hrest]

theorem flatten_length (B : ℕ) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = B) : words.flatten.length = words.length * B := by
  induction words with
  | nil => simp
  | cons word words ih =>
    have hword := hw word (by simp)
    have hrest : ∀ w ∈ words, w.length = B := fun w h => hw w (by simp [h])
    simp [hword, ih hrest, Nat.add_mul, Nat.add_comm]

/-- Every output delimiter is written by the audited frame-producing loop. -/
theorem trace (width : List Bool) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = width.length) (regs : Fin 5 → Bool) :
    ∃ finalRegs, Trace program (words.length * (28 * width.length + 33) + 11)
      ((state regs (data width words.length words.flatten [])).withPC (some program.entry))
      ((state finalRegs {data width 0 [] [] with
        output := Encoding.encodeList id words}).withPC none) := by
  obtain ⟨rf, he⟩ := program_trace width words.length words.flatten regs
  rw [chunks_flatten _ _ hw] at he
  have hdrop : words.flatten.drop (words.length * width.length) = [] := by
    rw [← flatten_length _ _ hw]
    simp
  exact ⟨rf, by simpa only [hdrop] using he⟩

theorem ringWords_trace {d B : ℕ} (width : List Bool)
    (hw : width.length = d * B)
    (words : List (RingProgram.Code (SubexponentialSAT.SubexpQuarticRing.Word B) d))
    (regs : Fin 5 → Bool) :
    ∃ finalRegs, Trace program (words.length * (28 * width.length + 33) + 11)
      ((state regs (data width words.length (words.map RingProgram.flat).flatten [])).withPC
        (some program.entry))
      ((state finalRegs {data width 0 [] [] with
        output := Encoding.encodeList id (words.map RingProgram.flat)}).withPC none) := by
  have hwords : ∀ word ∈ words.map RingProgram.flat, word.length = width.length := by
    intro word hm
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hm
    simpa only [RingProgram.flat_length] using hw.symm
  simpa only [List.length_map] using trace width (words.map RingProgram.flat) hwords regs

/-- The old flat-node slot becomes empty and the preserved master framed list
is installed at300, exactly as required by the node moment iterator. -/
def callerRegisters (i : Fin 5) : Fin 16 := i.castAdd 11
def callerStacks : Fin 9 → Fin 320 := ![256,280,295,296,297,298,299,306,300]
abbrev callerCommand : Cmd 16 320 :=
  .call (ProgramLinking.liftProgram program callerRegisters callerStacks)

theorem caller_trace {d B : ℕ} (width : List Bool) (hw : width.length = d * B)
    (words : List (RingProgram.Code (SubexponentialSAT.SubexpQuarticRing.Word B) d))
    (regs : Fin 5 → Bool) (frame : State 16 320) :
    ∃ finalRegs, Eval callerCommand (words.length * (28 * width.length + 33) + 11)
      (embedState callerRegisters callerStacks frame
        (state regs (data width words.length (words.map RingProgram.flat).flatten [])))
      (embedState callerRegisters callerStacks frame
        (state finalRegs {data width 0 [] [] with
          output := Encoding.encodeList id (words.map RingProgram.flat)})) := by
  obtain ⟨rf, he⟩ := ringWords_trace width hw words regs
  exact ⟨rf, eval_call_lifted program callerRegisters callerStacks frame
    (Fin.castAdd_injective 5 11) (by decide) he⟩

end SubexponentialSAT.SqrtLog.LeafProgram.NodeFrames

end OAI.Algorithms
