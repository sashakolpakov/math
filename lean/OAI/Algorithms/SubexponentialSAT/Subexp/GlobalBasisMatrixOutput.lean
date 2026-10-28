import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisProgram

namespace OAI.Algorithms

/-!
# Framing the computed global basis matrix

The finite source command consumes its forward matrix, count word, and
column descriptors, and prepends one fully framed matrix record. The cost
includes the three lifted framing calls, copying, and both cleanup scans.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMatrixOutput

open BitProgram StructuredCalls

abbrev Data := GlobalBasisProgram.Data

/-- A matrix record carries the count word before the forward matrix. -/
def payload (countWord matrix : List Bool) : List Bool :=
  Encoding.frame countWord ++ Encoding.frame matrix

def record (countWord matrix : List Bool) : List Bool :=
  true :: Encoding.frame (payload countWord matrix)

def resultStacks (s : Fin 64 → List Bool) (countWord matrix : List Bool) :
    Fin 64 → List Bool :=
  Function.update (Function.update (Function.update (Function.update s
    35 []) 50 []) 51 []) 63 (record countWord matrix ++ s 63)

def cost (countWord matrix descriptors : List Bool) : ℕ :=
  24 * matrix.length + 33 * countWord.length + 2 * descriptors.length + 56

private theorem regs_injective : Function.Injective GlobalBasisProgram.regs8 :=
  Fin.castAdd_injective 8 8

private theorem frame_eval (src dst tmp : Fin 64)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (d : Data) (ht : d.stacks tmp = []) :
    ∃ e, Eval (GlobalBasisProgram.emitFrame src dst tmp htd)
      (8 * (d.stacks src).length + 9) d e ∧
      e.stacks = Function.update (Function.update d.stacks src []) dst
        (Encoding.frame (d.stacks src) ++ d.stacks dst) := by
  obtain ⟨e, he, hs⟩ := MatrixProgramSupport.emitFrame_eval src dst tmp hsd hst htd
    (projectState GlobalBasisProgram.regs8 id d) ht
  refine ⟨embedState GlobalBasisProgram.regs8 id d e, ?_, ?_⟩
  · simpa only [GlobalBasisProgram.emitFrame, projectState, Function.comp_apply,
      id_eq, Nat.add_assoc] using
      eval_liftCommand_from_state _ src dst GlobalBasisProgram.regs8 id d
        regs_injective Function.injective_id he
  · simpa only [embedState, ProgramLinking.extend_id, projectState,
      Function.comp_def, id_eq] using hs

private def copied (src dst : Fin 64) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

private theorem copy_eval (src dst : Fin 64) (d : Data)
    (hsd : src ≠ dst) (hs31 : src ≠ 31) (h31d : (31 : Fin 64) ≠ dst)
    (h31 : d.stacks 31 = []) :
    Eval (GlobalBasisProgram.copy src dst) (7 * (d.stacks src).length + 5)
      d (copied src dst d) :=
  .call _ (ListRegisterProgram.copy_run src dst 31 0 1 hsd hs31 h31d (by decide)
    d.regs d.stacks h31)

private def cleared (src : Fin 64) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

private theorem clear_eval (src : Fin 64) (d : Data) :
    Eval (GlobalBasisProgram.clear src) (2 * (d.stacks src).length + 3)
      d (cleared src d) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

/-- Exact execution of the existing native 16-register, 64-stack command.
The count is runtime data; the statement allows any count word. -/
theorem command_eval (countWord matrix : List Bool) (d : Data)
    (h50 : d.stacks 50 = countWord) (h51 : d.stacks 51 = matrix)
    (h31 : d.stacks 31 = []) (h56 : d.stacks 56 = [])
    (h57 : d.stacks 57 = []) (h58 : d.stacks 58 = []) :
    ∃ e, Eval GlobalBasisProgram.emitMatrix (cost countWord matrix (d.stacks 35)) d e ∧
      e.stacks = resultStacks d.stacks countWord matrix := by
  obtain ⟨a, ha, hsa⟩ := frame_eval 51 56 57 (by decide) (by decide) (by decide) d h57
  have ha50 : a.stacks 50 = countWord := by simp [hsa, h50]
  have ha31 : a.stacks 31 = [] := by simp [hsa, h31]
  let b := copied 50 58 a
  have hb := copy_eval 50 58 a (by decide) (by decide) (by decide) ha31
  have hb57 : b.stacks 57 = [] := by
    simp [b, copied, StackRoutines.copyStacks, hsa, h57]
  have hb58 : b.stacks 58 = countWord := by
    simp [b, copied, StackRoutines.copyStacks, hsa, h50, h58]
  obtain ⟨c, hc, hsc⟩ := frame_eval 58 56 57 (by decide) (by decide) (by decide) b hb57
  have hc57 : c.stacks 57 = [] := by simp [hsc, hb57]
  have hc56 : c.stacks 56 = payload countWord matrix := by
    simp [hsc, b, copied, StackRoutines.copyStacks, hsa, h50, h51, h56, h58, payload]
  obtain ⟨f, hf, hsf⟩ := frame_eval 56 63 57 (by decide) (by decide) (by decide) c hc57
  let g := TupleProgram.pushedState 63 0 true f
  have hg : Eval (GlobalBasisProgram.push 63 true) 2 f g :=
    TupleProgram.pushConst_eval 63 0 true f
  let h := cleared 50 g
  have hh := clear_eval 50 g
  let e := cleared 35 h
  have he := clear_eval 35 h
  have hg50 : g.stacks 50 = countWord := by
    simp [g, hsf, hsc, b, copied,
      StackRoutines.copyStacks, hsa, h50]
  have hh35 : h.stacks 35 = d.stacks 35 := by
    simp [h, cleared, g, hsf, hsc, b, copied,
      StackRoutines.copyStacks, hsa]
  refine ⟨e, ?_, ?_⟩
  · have total := ha.seq (hb.seq (hc.seq (hf.seq (hg.seq (hh.seq
      (he.seq (.base (.skip e))))))))
    rw [h51, ha50, hb58, hc56, hg50, hh35] at total
    have htime : (8 * matrix.length + 9) +
        ((7 * countWord.length + 5) + ((8 * countWord.length + 9) +
        ((8 * (payload countWord matrix).length + 9) +
        (2 + ((2 * countWord.length + 3) + ((2 * (d.stacks 35).length + 3) + 0)))))) =
        cost countWord matrix (d.stacks 35) := by
      simp only [payload, List.length_append, Encoding.length_frame, cost]
      omega
    rw [htime] at total
    exact total
  · simp only [e, h, cleared, g, hsf, hsc,
      b, copied, StackRoutines.copyStacks, hsa]
    funext i
    by_cases hi35 : i = 35
    · subst i
      simp [resultStacks]
    by_cases hi50 : i = 50
    · subst i
      simp [resultStacks]
    by_cases hi51 : i = 51
    · subst i
      simp [resultStacks]
    by_cases hi56 : i = 56
    · subst i
      simp [resultStacks, h56]
    by_cases hi58 : i = 58
    · subst i
      simp [resultStacks, h58]
    by_cases hi63 : i = 63
    · subst i
      simp [resultStacks, h50, h51, h56, h58, record, payload]
    simp [resultStacks, hi35, hi50, hi51, hi56, hi58, hi63]

def program := compiled GlobalBasisProgram.emitMatrix 51 63

theorem program_runsIn (countWord matrix : List Bool) (d : Data)
    (h50 : d.stacks 50 = countWord) (h51 : d.stacks 51 = matrix)
    (h31 : d.stacks 31 = []) (h56 : d.stacks 56 = [])
    (h57 : d.stacks 57 = []) (h58 : d.stacks 58 = []) :
    ∃ e : Data, RunsIn program (cost countWord matrix (d.stacks 35) + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = resultStacks d.stacks countWord matrix := by
  obtain ⟨e, he, hs⟩ := command_eval countWord matrix d h50 h51 h31 h56 h57 h58
  exact ⟨e, ⟨_, le_rfl, compiled_halt_trace he 51 63⟩, hs⟩

theorem cost_le_linear (countWord matrix descriptors : List Bool) :
    cost countWord matrix descriptors ≤
      56 * (countWord.length + matrix.length + descriptors.length + 1) := by
  unfold cost
  omega

@[simp] theorem result_output (s : Fin 64 → List Bool) (countWord matrix : List Bool) :
    resultStacks s countWord matrix 63 = record countWord matrix ++ s 63 := by
  simp [resultStacks]

theorem result_frame (s : Fin 64 → List Bool) (countWord matrix : List Bool)
    (i : Fin 64) (h35 : i ≠ 35) (h50 : i ≠ 50) (h51 : i ≠ 51) (h63 : i ≠ 63) :
    resultStacks s countWord matrix i = s i := by
  simp [resultStacks, h35, h50, h51, h63]

theorem unary_command_eval (count : ℕ) (matrix : List Bool) (d : Data)
    (h50 : d.stacks 50 = List.replicate count true) (h51 : d.stacks 51 = matrix)
    (h31 : d.stacks 31 = []) (h56 : d.stacks 56 = [])
    (h57 : d.stacks 57 = []) (h58 : d.stacks 58 = []) :
    ∃ e, Eval GlobalBasisProgram.emitMatrix
      (24 * matrix.length + 33 * count + 2 * (d.stacks 35).length + 56) d e ∧
      e.stacks = resultStacks d.stacks (List.replicate count true) matrix := by
  simpa only [cost, List.length_replicate] using
    command_eval (List.replicate count true) matrix d h50 h51 h31 h56 h57 h58

end SubexponentialSAT.Subexp.GlobalBasisMatrixOutput

end OAI.Algorithms
