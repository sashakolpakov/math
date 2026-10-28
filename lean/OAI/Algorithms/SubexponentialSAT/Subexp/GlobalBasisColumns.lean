import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-!
# Physical column descriptors for global basis matrices

Descriptors contain only block, color, and local-column indices, or a
leftover rank. They are constructed by actual framed-word emitters; no
matrix entries or global read plan are supplied to these programs.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisColumns

open BitProgram StructuredCalls MatrixProgramSupport

abbrev Data := State 8 10
abbrev Code := Cmd 8 10

def unary (n : ℕ) := List.replicate n true

inductive Descriptor where
  | localColumn (block color column : ℕ)
  | leftover (rank : ℕ)

def localPayload (block color column : List Bool) : List Bool :=
  true :: (Encoding.frame block ++ Encoding.frame color ++ Encoding.frame column)

def Descriptor.encode : Descriptor → List Bool
  | .localColumn block color column => localPayload (unary block) (unary color) (unary column)
  | .leftover rank => false :: Encoding.frame (unary rank)

def record (payload : List Bool) : List Bool := true :: Encoding.frame payload

def source (i : Fin 3) : Fin 10 := Fin.castAdd 7 i

def field (i : Fin 3) : Code :=
  .seq (MatrixProgramSupport.copy (source i) 6 8)
    (MatrixProgramSupport.emitFrame 6 7 9 (by decide))

/-- Copy and frame one retained descriptor field. Only the payload
accumulator changes; the source word and all surrounding data are preserved. -/
theorem field_eval (i : Fin 3) (d : Data)
    (h6 : d.stacks 6 = []) (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ e, Eval (field i) (15 * (d.stacks (source i)).length + 13) d e ∧
      e.stacks = Function.update d.stacks 7
        (Encoding.frame (d.stacks (source i)) ++ d.stacks 7) := by
  have hs6 : source i ≠ 6 := by fin_cases i <;> decide
  have hs8 : source i ≠ 8 := by fin_cases i <;> decide
  obtain ⟨a, ha, hsa⟩ := MatrixProgramSupport.copy_eval (source i) 6 8
    hs6 hs8 (by decide) d h8
  have ha6 : a.stacks 6 = d.stacks (source i) := by
    simp [hsa, StackRoutines.copyStacks, h6]
  have ha9 : a.stacks 9 = [] := by
    simp [hsa, StackRoutines.copyStacks, h9]
  obtain ⟨e, he, hse⟩ := MatrixProgramSupport.emitFrame_eval 6 7 9
    (by decide) (by decide) (by decide) a ha9
  refine ⟨e, ?_, ?_⟩
  · have h := ha.seq he
    rw [ha6] at h
    convert h using 1
    · rfl
    · omega
  · rw [hse, hsa]
    funext j
    fin_cases i <;> fin_cases j <;>
      simp [StackRoutines.copyStacks, source, h6]

def finishPayload (tag : Bool) : Code :=
  .seq (TupleProgram.pushConst 7 0 tag)
    (.seq (MatrixProgramSupport.emitFrame 7 3 9 (by decide))
      (TupleProgram.pushConst 3 0 true))

theorem finishPayload_eval (tag : Bool) (d : Data) (h9 : d.stacks 9 = []) :
    ∃ e, Eval (finishPayload tag) (8 * (d.stacks 7).length + 20) d e ∧
      e.stacks = Function.update (Function.update d.stacks 7 []) 3
        (record (tag :: d.stacks 7) ++ d.stacks 3) := by
  let a := TupleProgram.pushedState 7 0 tag d
  have h1 := TupleProgram.pushConst_eval (7 : Fin 10) (0 : Fin 8) tag d
  obtain ⟨b, h2, hsb⟩ := MatrixProgramSupport.emitFrame_eval 7 3 9
    (by decide) (by decide) (by decide) a (by simp [a, h9])
  let e := TupleProgram.pushedState 3 0 true b
  have h3 := TupleProgram.pushConst_eval (3 : Fin 10) (0 : Fin 8) true b
  refine ⟨e, ?_, ?_⟩
  · have h := h1.seq (h2.seq h3)
    convert h using 1
    · rfl
    · simp [a]
      omega
  · funext j
    fin_cases j <;> simp [e, a, hsb, record]

def emitLocal : Code := .seq (field 2) (.seq (field 1) (.seq (field 0) (finishPayload true)))

def localCost (block color column : List Bool) : ℕ :=
  31 * (block.length + color.length + column.length) + 83

theorem emitLocal_eval (d : Data)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ e, Eval emitLocal (localCost (d.stacks 0) (d.stacks 1) (d.stacks 2)) d e ∧
      e.stacks = Function.update d.stacks 3
        (record (localPayload (d.stacks 0) (d.stacks 1) (d.stacks 2)) ++ d.stacks 3) := by
  obtain ⟨a, h1, hsa⟩ := field_eval 2 d h6 h8 h9
  obtain ⟨b, h2, hsb⟩ := field_eval 1 a
    (by simp [hsa, h6]) (by simp [hsa, h8]) (by simp [hsa, h9])
  obtain ⟨c, h3, hsc⟩ := field_eval 0 b
    (by simp [hsb, hsa, h6]) (by simp [hsb, hsa, h8]) (by simp [hsb, hsa, h9])
  obtain ⟨e, h4, hse⟩ := finishPayload_eval true c (by simp [hsc, hsb, hsa, h9])
  have hs1 : a.stacks (source 1) = d.stacks 1 := by simp [source, hsa]
  have hs0 : b.stacks (source 0) = d.stacks 0 := by simp [source, hsb, hsa]
  have hc7 : c.stacks 7 = Encoding.frame (d.stacks 0) ++
      Encoding.frame (d.stacks 1) ++ Encoding.frame (d.stacks 2) := by
    simp [hsc, hsb, hsa, source, h7]
  refine ⟨e, ?_, ?_⟩
  · have h := h1.seq (h2.seq (h3.seq h4))
    rw [hs1, hs0, hc7] at h
    convert h using 1
    · rfl
    · simp [localCost, source]
      omega
  · rw [hse, hsc, hsb, hsa]
    funext j
    fin_cases j <;> simp [source, record, localPayload, h7, List.append_assoc]

def emitLeftover : Code := .seq (field 2) (finishPayload false)

theorem emitLeftover_eval (d : Data)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ e, Eval emitLeftover (31 * (d.stacks 2).length + 41) d e ∧
      e.stacks = Function.update d.stacks 3
        (record (false :: Encoding.frame (d.stacks 2)) ++ d.stacks 3) := by
  obtain ⟨a, h1, hsa⟩ := field_eval 2 d h6 h8 h9
  obtain ⟨e, h2, hse⟩ := finishPayload_eval false a (by simp [hsa, h9])
  have ha7 : a.stacks 7 = Encoding.frame (d.stacks 2) := by simp [hsa, source, h7]
  refine ⟨e, ?_, ?_⟩
  · have h := h1.seq h2
    rw [ha7] at h
    convert h using 1
    · rfl
    · simp [source]
      omega
  · rw [hse, hsa]
    funext j
    fin_cases j <;> simp [source, record, h7]

def segmentStep : Code :=
  .seq (MatrixProgramSupport.copy 5 2 8)
    (.seq (MatrixProgramSupport.copy 4 2 8)
      (.seq emitLocal (.call (StackRoutines.clearProgram 2 0 1))))

def stepCost (block color offset index : ℕ) : ℕ :=
  40 * (offset + index) + 31 * (block + color) + 96

theorem segmentStep_eval (block color offset index : ℕ) (d : Data)
    (h0 : d.stacks 0 = unary block) (h1 : d.stacks 1 = unary color)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = unary offset)
    (h5 : d.stacks 5 = unary index) (h6 : d.stacks 6 = [])
    (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ e, Eval segmentStep (stepCost block color offset index) d e ∧
      e.stacks = Function.update d.stacks 3
        (record (Descriptor.encode (.localColumn block color (offset + index))) ++ d.stacks 3) := by
  obtain ⟨a, ha, hsa⟩ := MatrixProgramSupport.copy_eval 5 2 8
    (by decide) (by decide) (by decide) d h8
  obtain ⟨b, hb, hsb⟩ := MatrixProgramSupport.copy_eval 4 2 8
    (by decide) (by decide) (by decide) a (by simp [hsa, StackRoutines.copyStacks, h8])
  have hb2 : b.stacks 2 = unary (offset + index) := by
    calc
      b.stacks 2 = unary offset ++ unary index := by
        simp [hsb, hsa, StackRoutines.copyStacks, h2, h4, h5]
      _ = unary (offset + index) := (List.replicate_add offset index true).symm
  have hb0 : b.stacks 0 = unary block := by simp [hsb, hsa, StackRoutines.copyStacks, h0]
  have hb1 : b.stacks 1 = unary color := by simp [hsb, hsa, StackRoutines.copyStacks, h1]
  obtain ⟨c, hc, hsc⟩ := emitLocal_eval b
    (by simp [hsb, hsa, StackRoutines.copyStacks, h6])
    (by simp [hsb, hsa, StackRoutines.copyStacks, h7])
    (by simp [hsb, hsa, StackRoutines.copyStacks, h8])
    (by simp [hsb, hsa, StackRoutines.copyStacks, h9])
  let e : Data := ⟨readRegs c.regs 0 1 none, StackRoutines.clearStacks 2 c.stacks⟩
  have hd := TupleProgram.clear_eval (2 : Fin 10) (0 : Fin 8) 1 c
  refine ⟨e, ?_, ?_⟩
  · have h := ha.seq (hb.seq (hc.seq hd))
    have ha4 : a.stacks 4 = unary offset := by simp [hsa, StackRoutines.copyStacks, h4]
    have hc2 : c.stacks 2 = unary (offset + index) := by simp [hsc, hb2]
    rw [h5, ha4, hb0, hb1, hb2, hc2] at h
    convert h using 1
    · rfl
    · simp [stepCost, localCost, unary]
      omega
  · funext j
    have hb3 : b.stacks 3 = d.stacks 3 := by simp [hsb, hsa, StackRoutines.copyStacks]
    by_cases hj : j = 3
    · subst j
      simp [e, StackRoutines.clearStacks, hsc, hb0, hb1, hb2, hb3,
        Descriptor.encode]
    · fin_cases j <;> simp_all [e, StackRoutines.clearStacks,
        StackRoutines.copyStacks]

def segmentPorts : UnaryForPrograms.Ports 8 10 := ⟨5, 0, 1⟩
def segment : Code := UnaryForPrograms.forCmd segmentPorts segmentStep

def segmentPrefix (block color offset count : ℕ) : List Bool :=
  (List.range count).flatMap (fun i =>
    record (Descriptor.encode (.localColumn block color (offset + i))))

@[simp] theorem segmentPrefix_zero (block color offset : ℕ) :
    segmentPrefix block color offset 0 = [] := rfl

theorem segmentPrefix_succ (block color offset n : ℕ) :
    segmentPrefix block color offset (n + 1) = segmentPrefix block color offset n ++
      record (Descriptor.encode (.localColumn block color (offset + n))) := by
  simp [segmentPrefix, List.range_succ]

def segmentCost (block color offset : ℕ) : ℕ → ℕ
  | 0 => 2
  | n + 1 => stepCost block color offset n + segmentCost block color offset n + 2

theorem segment_visits (block color offset count : ℕ) :
    ∀ d : Data, d.stacks 0 = unary block → d.stacks 1 = unary color →
      d.stacks 2 = [] → d.stacks 4 = unary offset → d.stacks 5 = unary count →
      d.stacks 6 = [] → d.stacks 7 = [] → d.stacks 8 = [] → d.stacks 9 = [] →
      ∃ costs e, UnaryForPrograms.Visits segmentPorts segmentStep costs
        (segmentCost block color offset count) d e ∧
        e.stacks = Function.update (Function.update d.stacks 5 []) 3
          (segmentPrefix block color offset count ++ d.stacks 3) := by
  induction count with
  | zero =>
    intro d h0 h1 h2 h4 h5 h6 h7 h8 h9
    refine ⟨[], UnaryForPrograms.popped segmentPorts d, .done d h5, ?_⟩
    funext i
    fin_cases i <;> simp [UnaryForPrograms.popped, segmentPorts, h5, unary]
  | succ count ih =>
    intro d h0 h1 h2 h4 h5 h6 h7 h8 h9
    let p := UnaryForPrograms.popped segmentPorts d
    have hp5 : p.stacks 5 = unary count := by
      simp [p, UnaryForPrograms.popped, segmentPorts, h5, unary, List.replicate_succ]
    obtain ⟨e, he, hse⟩ := segmentStep_eval block color offset count p
      (by simp [p, UnaryForPrograms.popped, segmentPorts, h0])
      (by simp [p, UnaryForPrograms.popped, segmentPorts, h1])
      (by simp [p, UnaryForPrograms.popped, segmentPorts, h2])
      (by simp [p, UnaryForPrograms.popped, segmentPorts, h4]) hp5
      (by simp [p, UnaryForPrograms.popped, segmentPorts, h6])
      (by simp [p, UnaryForPrograms.popped, segmentPorts, h7])
      (by simp [p, UnaryForPrograms.popped, segmentPorts, h8])
      (by simp [p, UnaryForPrograms.popped, segmentPorts, h9])
    obtain ⟨costs, f, hf, hsf⟩ := ih e
      (by simp [hse, p, UnaryForPrograms.popped, segmentPorts, h0])
      (by simp [hse, p, UnaryForPrograms.popped, segmentPorts, h1])
      (by simp [hse, p, UnaryForPrograms.popped, segmentPorts, h2])
      (by simp [hse, p, UnaryForPrograms.popped, segmentPorts, h4])
      (by simp [hse, hp5])
      (by simp [hse, p, UnaryForPrograms.popped, segmentPorts, h6])
      (by simp [hse, p, UnaryForPrograms.popped, segmentPorts, h7])
      (by simp [hse, p, UnaryForPrograms.popped, segmentPorts, h8])
      (by simp [hse, p, UnaryForPrograms.popped, segmentPorts, h9])
    refine ⟨stepCost block color offset count :: costs, f,
      .step (by simp [segmentPorts, h5, unary]) he (by simp [hse, segmentPorts, p]) hf, ?_⟩
    funext i
    fin_cases i <;> simp [hsf, hse, p, UnaryForPrograms.popped, segmentPorts,
      segmentPrefix_succ, List.append_assoc]

theorem segment_eval (block color offset count : ℕ) (d : Data)
    (h0 : d.stacks 0 = unary block) (h1 : d.stacks 1 = unary color)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = unary offset)
    (h5 : d.stacks 5 = unary count) (h6 : d.stacks 6 = [])
    (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ e, Eval segment (segmentCost block color offset count) d e ∧
      e.stacks = Function.update (Function.update d.stacks 5 []) 3
        (segmentPrefix block color offset count ++ d.stacks 3) := by
  obtain ⟨costs, e, he, hs⟩ := segment_visits block color offset count d
    h0 h1 h2 h4 h5 h6 h7 h8 h9
  exact ⟨e, he.eval, hs⟩

theorem segmentCost_le (block color offset count : ℕ) :
    segmentCost block color offset count ≤
      count * (stepCost block color offset count + 2) + 2 := by
  induction count with
  | zero => simp [segmentCost]
  | succ count ih =>
    simp only [segmentCost]
    unfold stepCost at *
    nlinarith

theorem segmentCost_polynomial (block color offset count : ℕ) :
    segmentCost block color offset count + 1 ≤
      200 * (block + color + offset + count + 1) ^ 2 := by
  have h := segmentCost_le block color offset count
  unfold stepCost at h
  nlinarith

def segmentProgram := compiled segment 5 3

theorem segment_program_runsIn (block color offset count : ℕ) (d : Data)
    (h0 : d.stacks 0 = unary block) (h1 : d.stacks 1 = unary color)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = unary offset)
    (h5 : d.stacks 5 = unary count) (h6 : d.stacks 6 = [])
    (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ e : Data, RunsIn segmentProgram (200 * (block + color + offset + count + 1) ^ 2)
      (d.withPC (some segmentProgram.entry)) (e.withPC none) ∧
      e.stacks = Function.update (Function.update d.stacks 5 []) 3
        (segmentPrefix block color offset count ++ d.stacks 3) := by
  obtain ⟨e, he, hs⟩ := segment_eval block color offset count d
    h0 h1 h2 h4 h5 h6 h7 h8 h9
  exact ⟨e, ⟨segmentCost block color offset count + 1,
    segmentCost_polynomial block color offset count, compiled_halt_trace he 5 3⟩, hs⟩

end SubexponentialSAT.Subexp.GlobalBasisColumns

end OAI.Algorithms
