import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-!
# Preserving unary-indexed access to framed records

Both the record stream and unary index are copied by real stack programs.
The copied counter controls a fixed loop, each iteration consumes one record,
and the selected payload is decoded into the output.  All temporary stacks
are cleared.  This is used to select a current type group and then a color's
local table; the index is not interpreted by a semantic machine primitive.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisRecordLookup

open BitProgram StructuredCalls

abbrev Data := State 8 8
abbrev Code := Cmd 8 8

def unary (n : ℕ) := List.replicate n true
def record (bits : List Bool) := true :: Encoding.frame bits
def recordsPrefix (records : List (List Bool)) := records.flatMap record

def popTag : Code := .base (.atom (.pop 3 0 1))
abbrev popped (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks 3).head?, Function.update d.stacks 3 (d.stacks 3).tail⟩

theorem popTag_eval (d : Data) : Eval popTag 1 d (popped d) := .base (.atom _ _)

def skip : Code := .seq popTag
  (.seq (MatrixProgramSupport.readFrame 3 5 (by decide))
    (.call (StackRoutines.clearProgram 5 0 1)))

theorem skip_eval (bits tail : List Bool) (d : Data)
    (h3 : d.stacks 3 = record bits ++ tail) (h5 : d.stacks 5 = []) :
    ∃ e, Eval skip (8 * bits.length + 8) d e ∧
      e.stacks = Function.update d.stacks 3 tail := by
  let a := popped d
  obtain ⟨b, hb, hsb⟩ := MatrixProgramSupport.readFrame_eval 3 5 (by decide) a bits tail
    (by simp [a, h3, record]) (by simp [a, h5])
  let e : Data := ⟨readRegs b.regs 0 1 none, StackRoutines.clearStacks 5 b.stacks⟩
  have hc := TupleProgram.clear_eval (5 : Fin 8) (0 : Fin 8) 1 b
  have hb5 : b.stacks 5 = bits.reverse := by simp [hsb]
  refine ⟨e, ?_, ?_⟩
  · have h := (popTag_eval d).seq (hb.seq hc)
    rw [hb5] at h
    convert h using 1
    · rfl
    · simp only [List.length_reverse]
      omega
  · funext i
    fin_cases i <;> simp [e, StackRoutines.clearStacks, hsb, a, h5]

def loopPorts : UnaryForPrograms.Ports 8 8 := ⟨4, 0, 1⟩
def skipMany : Code := UnaryForPrograms.forCmd loopPorts skip

def skipCost : List (List Bool) → ℕ
  | [] => 2
  | bits :: rest => (8 * bits.length + 8) + skipCost rest + 2

theorem skipMany_visits (records : List (List Bool)) (tail : List Bool) :
    ∀ d : Data, d.stacks 3 = recordsPrefix records ++ tail →
      d.stacks 4 = unary records.length → d.stacks 5 = [] →
      ∃ costs e, UnaryForPrograms.Visits loopPorts skip costs (skipCost records) d e ∧
        e.stacks = Function.update (Function.update d.stacks 3 tail) 4 [] := by
  induction records with
  | nil =>
    intro d h3 h4 h5
    refine ⟨[], UnaryForPrograms.popped loopPorts d, .done d h4, ?_⟩
    funext i
    fin_cases i <;> simp_all [recordsPrefix, UnaryForPrograms.popped, loopPorts, unary]
  | cons bits rest ih =>
    intro d h3 h4 h5
    let p := UnaryForPrograms.popped loopPorts d
    have hp4 : p.stacks 4 = unary rest.length := by
      simp [p, UnaryForPrograms.popped, loopPorts, h4, unary, List.replicate_succ]
    obtain ⟨e, he, hse⟩ := skip_eval bits (recordsPrefix rest ++ tail) p
      (by simp [p, UnaryForPrograms.popped, loopPorts, h3, recordsPrefix, List.append_assoc])
      (by simp [p, UnaryForPrograms.popped, loopPorts, h5])
    obtain ⟨costs, f, hf, hsf⟩ := ih e (by simp [hse])
      (by simp [hse, hp4]) (by simp [hse, p, UnaryForPrograms.popped, loopPorts, h5])
    refine ⟨(8 * bits.length + 8) :: costs, f,
      .step (by simp [loopPorts, h4, unary]) he (by simp [hse, loopPorts, p]) hf, ?_⟩
    funext i
    fin_cases i <;> simp [hsf, hse, p, UnaryForPrograms.popped, loopPorts]

theorem skipMany_eval (records : List (List Bool)) (tail : List Bool) (d : Data)
    (h3 : d.stacks 3 = recordsPrefix records ++ tail)
    (h4 : d.stacks 4 = unary records.length) (h5 : d.stacks 5 = []) :
    ∃ e, Eval skipMany (skipCost records) d e ∧
      e.stacks = Function.update (Function.update d.stacks 3 tail) 4 [] := by
  obtain ⟨costs, e, he, hs⟩ := skipMany_visits records tail d h3 h4 h5
  exact ⟨e, he.eval, hs⟩

theorem skipCost_le (records : List (List Bool)) :
    skipCost records ≤ 5 * (recordsPrefix records).length + 2 := by
  induction records with
  | nil => simp [skipCost, recordsPrefix]
  | cons bits rest ih =>
    simp only [skipCost, recordsPrefix, List.flatMap_cons, List.length_append,
      record, List.length_cons, Encoding.length_frame] at *
    omega

def read : Code := .seq popTag (MatrixProgramSupport.readWord 3 2 5 (by decide))

theorem read_eval (bits tail : List Bool) (d : Data)
    (h3 : d.stacks 3 = record bits ++ tail)
    (h2 : d.stacks 2 = []) (h5 : d.stacks 5 = []) :
    ∃ e, Eval read (9 * bits.length + 8) d e ∧
      e.stacks = Function.update (Function.update d.stacks 3 tail) 2 bits := by
  obtain ⟨e, he, hse⟩ := MatrixProgramSupport.readWord_eval 3 2 5
    (by decide) (by decide) (by decide) (popped d) bits tail
    (by simp [ h3, record]) (by simp [ h2]) (by simp [ h5])
  refine ⟨e, ?_, ?_⟩
  · have h := (popTag_eval d).seq he
    convert h using 1
    · rfl
    · omega
  · rw [hse]
    funext i
    fin_cases i <;> simp []

def command : Code :=
  .seq (MatrixProgramSupport.copy 0 3 6)
    (.seq (MatrixProgramSupport.copy 1 4 6)
      (.seq skipMany (.seq read (.call (StackRoutines.clearProgram 3 0 1)))))

def cost (before : List (List Bool)) (bits tail : List Bool) : ℕ :=
  7 * (recordsPrefix before ++ record bits ++ tail).length + 7 * before.length +
    skipCost before + 9 * bits.length + 2 * tail.length + 21

theorem command_eval (before : List (List Bool)) (bits tail : List Bool) (d : Data)
    (h0 : d.stacks 0 = recordsPrefix before ++ record bits ++ tail)
    (h1 : d.stacks 1 = unary before.length)
    (h2 : d.stacks 2 = []) (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = [])
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) :
    ∃ e, Eval command (cost before bits tail) d e ∧
      e.stacks = Function.update d.stacks 2 bits := by
  obtain ⟨a, ha, hsa⟩ := MatrixProgramSupport.copy_eval 0 3 6
    (by decide) (by decide) (by decide) d h6
  obtain ⟨b, hb, hsb⟩ := MatrixProgramSupport.copy_eval 1 4 6
    (by decide) (by decide) (by decide) a (by simp [hsa, StackRoutines.copyStacks, h6])
  obtain ⟨c, hc, hsc⟩ := skipMany_eval before (record bits ++ tail) b
    (by simp [hsb, hsa, StackRoutines.copyStacks, h0, h3, List.append_assoc])
    (by simp [hsb, hsa, StackRoutines.copyStacks, h1, h4])
    (by simp [hsb, hsa, StackRoutines.copyStacks, h5])
  obtain ⟨e, he, hse⟩ := read_eval bits tail c
    (by simp [hsc])
    (by simp [hsc, hsb, hsa, StackRoutines.copyStacks, h2])
    (by simp [hsc, hsb, hsa, StackRoutines.copyStacks, h5])
  let f : Data := ⟨readRegs e.regs 0 1 none, StackRoutines.clearStacks 3 e.stacks⟩
  have hf := TupleProgram.clear_eval (3 : Fin 8) (0 : Fin 8) 1 e
  have he3 : e.stacks 3 = tail := by simp [hse, hsc]
  have ha1 : a.stacks 1 = unary before.length := by simp [hsa, StackRoutines.copyStacks, h1]
  refine ⟨f, ?_, ?_⟩
  · have h := ha.seq (hb.seq (hc.seq (he.seq hf)))
    rw [h0, ha1, he3] at h
    convert h using 1
    · rfl
    · simp only [cost, unary, List.length_replicate]
      omega
  · funext i
    fin_cases i <;> simp [f, StackRoutines.clearStacks, hse, hsc, hsb, hsa,
      StackRoutines.copyStacks, h3, h4]

theorem cost_le (before : List (List Bool)) (bits tail : List Bool) :
    cost before bits tail + 1 ≤
      30 * ((recordsPrefix before ++ record bits ++ tail).length + before.length + 1) := by
  have h := skipCost_le before
  simp only [cost, List.length_append, record, List.length_cons, Encoding.length_frame]
  omega

def program := compiled command 0 2

theorem program_runsIn (before : List (List Bool)) (bits tail : List Bool) (d : Data)
    (h0 : d.stacks 0 = recordsPrefix before ++ record bits ++ tail)
    (h1 : d.stacks 1 = unary before.length)
    (h2 : d.stacks 2 = []) (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = [])
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) :
    ∃ e : Data, RunsIn program (30 * ((d.stacks 0).length + (d.stacks 1).length + 1))
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 2 bits := by
  obtain ⟨e, he, hs⟩ := command_eval before bits tail d h0 h1 h2 h3 h4 h5 h6
  refine ⟨e, ⟨cost before bits tail + 1, ?_, compiled_halt_trace he 0 2⟩, hs⟩
  simpa only [h0, h1, unary, List.length_replicate] using cost_le before bits tail

end SubexponentialSAT.Subexp.GlobalBasisRecordLookup

end OAI.Algorithms
