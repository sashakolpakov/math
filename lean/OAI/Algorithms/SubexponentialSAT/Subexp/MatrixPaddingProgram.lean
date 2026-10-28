import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Append a runtime number of explicit zero scalar frames to a coefficient
row. This is an actual fixed program; the repeated block is constructed from
the supplied canonical zero word before invoking the block-copy routine. -/

namespace SubexponentialSAT.Subexp.MatrixPaddingProgram

open BitProgram StructuredCalls StackRoutines MatrixProgramSupport

abbrev Data := State 8 18

def smallRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def ports : Fin 4 → Fin 18 := ![10, 8, 9, 16]

theorem smallRegs_injective : Function.Injective smallRegs := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 8 => k.val) h

theorem ports_injective : Function.Injective ports := by decide

abbrev repeatBlock : Cmd 8 18 := .call
  (ProgramLinking.liftProgram BlockCopyProgram.program smallRegs ports)

def repeated (a : Data) (n : ℕ) : Data :=
  ⟨a.regs, Function.update (Function.update a.stacks 16 []) 8
    (BlockCopyProgram.copies n (a.stacks 10) ++ a.stacks 8)⟩

theorem repeatBlock_eval (a : Data) (n : ℕ)
    (hr : ∀ j : Fin 3, a.regs (smallRegs j) = false)
    (hc : a.stacks 16 = List.replicate n true) (h9 : a.stacks 9 = []) :
    Eval repeatBlock (n * (7 * (a.stacks 10).length + 7) + 3) a (repeated a n) := by
  let inner := BlockCopyProgram.initialState n (a.stacks 10) (a.stacks 8)
  have hstart : embedState smallRegs ports a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective ports_injective
    · intro j
      fin_cases j <;> simpa [inner, BlockCopyProgram.initialState, BlockCopyProgram.data] using hr _
    · intros; rfl
    · intro j
      fin_cases j <;> simp [inner, ports, BlockCopyProgram.initialState, BlockCopyProgram.data, hc, h9]
    · intros; rfl
  have hfinish : embedState smallRegs ports a
      (BlockCopyProgram.data false false (a.stacks 10)
        (BlockCopyProgram.copies n (a.stacks 10) ++ a.stacks 8) []) = repeated a n := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective ports_injective
    · intro j
      fin_cases j <;> simpa [repeated, BlockCopyProgram.data] using hr _
    · intros; rfl
    · intro j
      fin_cases j <;> simp [repeated, ports, BlockCopyProgram.data, h9]
    · intro j hj
      have h8 : j ≠ 8 := fun h => hj ⟨1, h.symm⟩
      have h16 : j ≠ 16 := fun h => hj ⟨3, h.symm⟩
      simp [repeated, h8, h16]
  have he := eval_call_lifted BlockCopyProgram.program smallRegs ports a
    smallRegs_injective ports_injective
    (BlockCopyProgram.program_trace n (a.stacks 10) (a.stacks 8))
  rw [hstart, hfinish] at he
  exact he

abbrev reset : Cmd 8 18 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 false))) (.base (.atom (.set 2 false))))

def resetState (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 false) 2 false, a.stacks⟩

theorem reset_eval (a : Data) : Eval reset 3 a (resetState a) := by
  let a1 := (StructuredProgram.Atom.set (0 : Fin 8) false).eval a
  let a2 := (StructuredProgram.Atom.set (1 : Fin 8) false).eval a1
  have he := (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (0 : Fin 8) false) a)).seq
    ((Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (1 : Fin 8) false) a1)).seq
      (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (2 : Fin 8) false) a2)))
  simpa [reset, resetState, a1, a2, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using he

abbrev command : Cmd 8 18 :=
  .seq (copy 16 17 9) (.seq (copy 14 0 9) (.seq (emitFrame 0 10 9 (by decide))
    (.seq reset (.seq repeatBlock (.seq (copy 12 8 9)
      (.seq (.call (clearProgram 12 0 1))
        (.seq (move 8 12 9) (.call (clearProgram 10 0 1)))))))))

def state (regs : Fin 8 → Bool) (coefficients zero modulus count lengthWord : List Bool) : Data :=
  ⟨regs, ![[], [], [], [], [], modulus, [], [], [], [], [], [], coefficients, [], zero, [],
    count, lengthWord]⟩

def cost (C Z n : ℕ) : ℕ :=
  (7 * n + 5) + ((7 * Z + 5) + ((8 * Z + 8) +
    (3 + ((n * (7 * (2 * Z + 1) + 7) + 3) + ((7 * C + 5) +
      ((2 * C + 3) + ((6 * (C + n * (2 * Z + 1)) + 6) + (2 * (2 * Z + 1) + 3))))))))

theorem words_replicate (n : ℕ) (zero : List Bool) :
    words (List.replicate n zero) = BlockCopyProgram.copies n (Encoding.frame zero) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ', words_append, BlockCopyProgram.copies_succ, ih]
      simp [words]

theorem command_eval (regs : Fin 8 → Bool) (xs : List (List Bool))
    (zero modulus lengthWord : List Bool) (n : ℕ) :
    ∃ regs', Eval command (cost (words xs).length zero.length n)
      (state regs (words xs) zero modulus (List.replicate n true) lengthWord)
      (state regs' (words (xs ++ List.replicate n zero)) zero modulus []
        (List.replicate n true ++ lengthWord)) := by
  let a := state regs (words xs) zero modulus (List.replicate n true) lengthWord
  obtain ⟨a0, h0, hs0⟩ := copy_eval (16 : Fin 18) 17 9
    (by decide) (by decide) (by decide) a rfl
  obtain ⟨a1, h1, hs1⟩ := copy_eval (14 : Fin 18) 0 9
    (by decide) (by decide) (by decide) a0
    (by rw [hs0]; simp [a, state, copyStacks])
  obtain ⟨a2, h2, hs2⟩ := emitFrame_eval (0 : Fin 18) 10 9
    (by decide) (by decide) (by decide) a1
    (by rw [hs1, hs0]; simp [a, state, copyStacks])
  let a3 := resetState a2
  have h3 := reset_eval a2
  have h4 := repeatBlock_eval a3 n
    (by intro j; fin_cases j <;> simp [a3, resetState, smallRegs])
    (by simp only [a3, resetState]; rw [hs2, hs1, hs0]; simp [a, state, copyStacks])
    (by simp only [a3, resetState]; rw [hs2, hs1, hs0]; simp [a, state, copyStacks])
  let a4 := repeated a3 n
  obtain ⟨a5, h5, hs5⟩ := copy_eval (12 : Fin 18) 8 9
    (by decide) (by decide) (by decide) a4
    (by simp only [a4, repeated, a3, resetState]; rw [hs2, hs1, hs0]; simp [a, state, copyStacks])
  let a6 : Data := ⟨readRegs a5.regs 0 1 none, clearStacks 12 a5.stacks⟩
  have h6 := TupleProgram.clear_eval (12 : Fin 18) (0 : Fin 8) 1 a5
  obtain ⟨a7, h7, hs7⟩ := move_eval (8 : Fin 18) 12 9
    (by decide) (by decide) (by decide) a6
    (by simp [a6, clearStacks])
    (by simp only [a6]; rw [hs5]; simp only [a4, repeated, a3, resetState];
        rw [hs2, hs1, hs0]; simp [a, state, copyStacks, clearStacks])
  let a8 : Data := ⟨readRegs a7.regs 0 1 none, clearStacks 10 a7.stacks⟩
  have h8 := TupleProgram.clear_eval (10 : Fin 18) (0 : Fin 8) 1 a7
  have hs8 : a8 = state a8.regs (words (xs ++ List.replicate n zero)) zero modulus []
      (List.replicate n true ++ lengthWord) := by
    apply data_ext
    · rfl
    · funext j
      simp only [a8]
      rw [hs7]
      simp only [a6]
      rw [hs5]
      simp only [a4, repeated, a3, resetState]
      rw [hs2, hs1, hs0]
      fin_cases j <;> simp [a, state, copyStacks, clearStacks, words_append, words_replicate]
  change Eval _ _ _ a8 at h8
  rw [hs8] at h8
  have he := h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8)))))))
  refine ⟨a8.regs, ?_⟩
  convert he using 1
  simp only [cost]
  rw [hs7]
  simp only [a6]
  rw [hs5]
  simp only [a4, repeated, a3, resetState]
  rw [hs2, hs1, hs0]
  simp [a, state, copyStacks, clearStacks, Encoding.length_frame, BlockCopyProgram.copies_length]

def program := compiled command 12 12

theorem program_runsIn (regs : Fin 8 → Bool) (xs : List (List Bool))
    (zero modulus lengthWord : List Bool) (n : ℕ) :
    ∃ regs', RunsIn program (cost (words xs).length zero.length n + 1)
      ((state regs (words xs) zero modulus (List.replicate n true) lengthWord).withPC
        (some program.entry))
      ((state regs' (words (xs ++ List.replicate n zero)) zero modulus []
        (List.replicate n true ++ lengthWord)).withPC none) := by
  obtain ⟨r, ht⟩ := command_eval regs xs zero modulus lengthWord n
  exact ⟨r, _, le_rfl, compiled_halt_trace ht 12 12⟩

end SubexponentialSAT.Subexp.MatrixPaddingProgram

end OAI.Algorithms
