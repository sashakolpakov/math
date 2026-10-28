import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisColumns
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Counted block and leftover column generation

The block count and local dimension are runtime unary words.  Each iteration
executes the concrete descriptor emitter, and the final stream follows
ascending block and column order.  No descriptor list is an input.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisColumnBlocks

open BitProgram StructuredCalls
open GlobalBasisColumns (unary Descriptor record segmentPrefix segmentCost)

abbrev Data := State 8 11
abbrev Code := Cmd 8 11

def low (i : Fin 10) : Fin 11 := Fin.castAdd 1 i

theorem low_injective : Function.Injective low := Fin.castAdd_injective 10 1

def segment : Code := liftCommand GlobalBasisColumns.segment 5 3 id low

theorem segment_eval (block color offset count : ℕ) (d : Data)
    (h0 : d.stacks 0 = unary block) (h1 : d.stacks 1 = unary color)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = unary offset)
    (h5 : d.stacks 5 = unary count) (h6 : d.stacks 6 = [])
    (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ e, Eval segment (segmentCost block color offset count + 1) d e ∧
      e.stacks = Function.update (Function.update d.stacks 5 []) 3
        (segmentPrefix block color offset count ++ d.stacks 3) := by
  obtain ⟨b, hb, hbs⟩ := GlobalBasisColumns.segment_eval block color offset count
    (projectState id low d) h0 h1 h2 h4 h5 h6 h7 h8 h9
  refine ⟨embedState id low d b,
    eval_liftCommand_from_state _ 5 3 id low d Function.injective_id low_injective hb, ?_⟩
  change Function.extend low b.stacks d.stacks = _
  rw [hbs, ProgramLinking.extend_update low_injective,
    ProgramLinking.extend_update low_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project id low d Function.injective_id low_injective)
  change Function.extend low (projectState id low d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

def blockStep : Code := .seq (MatrixProgramSupport.copy 10 5 8) segment

def blockStepCost (block color dimension : ℕ) : ℕ :=
  7 * dimension + 6 + segmentCost block color 0 dimension

theorem blockStep_eval (block color dimension : ℕ) (d : Data)
    (h0 : d.stacks 0 = unary block) (h1 : d.stacks 1 = unary color)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = [])
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = [])
    (h10 : d.stacks 10 = unary dimension) :
    ∃ e, Eval blockStep (blockStepCost block color dimension) d e ∧
      e.stacks = Function.update d.stacks 3
        (segmentPrefix block color 0 dimension ++ d.stacks 3) := by
  obtain ⟨a, ha, hsa⟩ := MatrixProgramSupport.copy_eval 10 5 8
    (by decide) (by decide) (by decide) d h8
  obtain ⟨e, he, hse⟩ := segment_eval block color 0 dimension a
    (by simp [hsa, StackRoutines.copyStacks, h0])
    (by simp [hsa, StackRoutines.copyStacks, h1])
    (by simp [hsa, StackRoutines.copyStacks, h2])
    (by simp [hsa, StackRoutines.copyStacks, h4, unary])
    (by simp [hsa, StackRoutines.copyStacks, h5, h10])
    (by simp [hsa, StackRoutines.copyStacks, h6])
    (by simp [hsa, StackRoutines.copyStacks, h7])
    (by simp [hsa, StackRoutines.copyStacks, h8])
    (by simp [hsa, StackRoutines.copyStacks, h9])
  refine ⟨e, ?_, ?_⟩
  · have h := ha.seq he
    rw [h10] at h
    convert h using 1 <;> simp [blockStep, blockStepCost, unary] ; omega
  · rw [hse, hsa]
    funext i
    fin_cases i <;> simp [StackRoutines.copyStacks, h5]

def blockPorts : UnaryForPrograms.Ports 8 11 := ⟨0, 0, 1⟩
def blocks : Code := UnaryForPrograms.forCmd blockPorts blockStep

def blockPrefix (count color dimension : ℕ) : List Bool :=
  (List.range count).flatMap (fun block => segmentPrefix block color 0 dimension)

@[simp] theorem blockPrefix_zero (color dimension : ℕ) : blockPrefix 0 color dimension = [] := rfl

theorem blockPrefix_succ (count color dimension : ℕ) :
    blockPrefix (count + 1) color dimension = blockPrefix count color dimension ++
      segmentPrefix count color 0 dimension := by
  simp [blockPrefix, List.range_succ]

def blockCost (color dimension : ℕ) : ℕ → ℕ
  | 0 => 2
  | n + 1 => blockStepCost n color dimension + blockCost color dimension n + 2

theorem blocks_visits (count color dimension : ℕ) :
    ∀ d : Data, d.stacks 0 = unary count → d.stacks 1 = unary color →
      d.stacks 2 = [] → d.stacks 4 = [] → d.stacks 5 = [] →
      d.stacks 6 = [] → d.stacks 7 = [] → d.stacks 8 = [] → d.stacks 9 = [] →
      d.stacks 10 = unary dimension →
      ∃ costs e, UnaryForPrograms.Visits blockPorts blockStep costs
        (blockCost color dimension count) d e ∧
        e.stacks = Function.update (Function.update d.stacks 0 []) 3
          (blockPrefix count color dimension ++ d.stacks 3) := by
  induction count with
  | zero =>
    intro d h0 h1 h2 h4 h5 h6 h7 h8 h9 h10
    refine ⟨[], UnaryForPrograms.popped blockPorts d, .done d h0, ?_⟩
    funext i
    fin_cases i <;> simp [UnaryForPrograms.popped, blockPorts, h0, unary]
  | succ count ih =>
    intro d h0 h1 h2 h4 h5 h6 h7 h8 h9 h10
    let p := UnaryForPrograms.popped blockPorts d
    have hp0 : p.stacks 0 = unary count := by
      simp [p, UnaryForPrograms.popped, blockPorts, h0, unary, List.replicate_succ]
    obtain ⟨e, he, hse⟩ := blockStep_eval count color dimension p hp0
      (by simp [p, UnaryForPrograms.popped, blockPorts, h1])
      (by simp [p, UnaryForPrograms.popped, blockPorts, h2])
      (by simp [p, UnaryForPrograms.popped, blockPorts, h4])
      (by simp [p, UnaryForPrograms.popped, blockPorts, h5])
      (by simp [p, UnaryForPrograms.popped, blockPorts, h6])
      (by simp [p, UnaryForPrograms.popped, blockPorts, h7])
      (by simp [p, UnaryForPrograms.popped, blockPorts, h8])
      (by simp [p, UnaryForPrograms.popped, blockPorts, h9])
      (by simp [p, UnaryForPrograms.popped, blockPorts, h10])
    obtain ⟨costs, f, hf, hsf⟩ := ih e
      (by simp [hse, hp0])
      (by simp [hse, p, UnaryForPrograms.popped, blockPorts, h1])
      (by simp [hse, p, UnaryForPrograms.popped, blockPorts, h2])
      (by simp [hse, p, UnaryForPrograms.popped, blockPorts, h4])
      (by simp [hse, p, UnaryForPrograms.popped, blockPorts, h5])
      (by simp [hse, p, UnaryForPrograms.popped, blockPorts, h6])
      (by simp [hse, p, UnaryForPrograms.popped, blockPorts, h7])
      (by simp [hse, p, UnaryForPrograms.popped, blockPorts, h8])
      (by simp [hse, p, UnaryForPrograms.popped, blockPorts, h9])
      (by simp [hse, p, UnaryForPrograms.popped, blockPorts, h10])
    refine ⟨blockStepCost count color dimension :: costs, f,
      .step (by simp [blockPorts, h0, unary]) he (by simp [hse, blockPorts, p]) hf, ?_⟩
    funext i
    fin_cases i <;> simp [hsf, hse, p, UnaryForPrograms.popped, blockPorts,
      blockPrefix_succ, List.append_assoc]

theorem blocks_eval (count color dimension : ℕ) (d : Data)
    (h0 : d.stacks 0 = unary count) (h1 : d.stacks 1 = unary color)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = [])
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = [])
    (h10 : d.stacks 10 = unary dimension) :
    ∃ e, Eval blocks (blockCost color dimension count) d e ∧
      e.stacks = Function.update (Function.update d.stacks 0 []) 3
        (blockPrefix count color dimension ++ d.stacks 3) := by
  obtain ⟨costs, e, he, hs⟩ := blocks_visits count color dimension d
    h0 h1 h2 h4 h5 h6 h7 h8 h9 h10
  exact ⟨e, he.eval, hs⟩

theorem blockCost_le (count color dimension : ℕ) :
    blockCost color dimension count ≤
      count * (7 * dimension + 8 +
        200 * (count + color + dimension + 1)^2) + 2 := by
  induction count with
  | zero => simp [blockCost]
  | succ count ih =>
    have hs := GlobalBasisColumns.segmentCost_polynomial count color 0 dimension
    simp only [Nat.add_zero] at hs
    simp only [blockCost, blockStepCost]
    have hm : (count + color + dimension + 1)^2 ≤
        (count + 1 + color + dimension + 1)^2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith

theorem blockCost_polynomial (count color dimension : ℕ) :
    blockCost color dimension count + 1 ≤ 220 * (count + color + dimension + 1)^3 := by
  have h := blockCost_le count color dimension
  let L := count + color + dimension + 1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hc : count ≤ L := by dsimp [L]; omega
  have hd : dimension ≤ L := by dsimp [L]; omega
  have hcd : count * dimension ≤ L * L := Nat.mul_le_mul hc hd
  have hcl : count * L^2 ≤ L^3 := by nlinarith [Nat.mul_le_mul_right (L^2) hc]
  have hL2 : L ≤ L^2 := by nlinarith
  have hL3 : L^2 ≤ L^3 := by nlinarith [Nat.mul_le_mul_right L hL2]
  change blockCost color dimension count + 1 ≤ 220 * L^3
  change blockCost color dimension count ≤ count * (7 * dimension + 8 + 200 * L^2) + 2 at h
  nlinarith

def program := compiled blocks 0 3

theorem program_runsIn (count color dimension : ℕ) (d : Data)
    (h0 : d.stacks 0 = unary count) (h1 : d.stacks 1 = unary color)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = [])
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = [])
    (h10 : d.stacks 10 = unary dimension) :
    ∃ e : Data, RunsIn program (220 * (count + color + dimension + 1)^3)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update (Function.update d.stacks 0 []) 3
        (blockPrefix count color dimension ++ d.stacks 3) := by
  obtain ⟨e, he, hs⟩ := blocks_eval count color dimension d
    h0 h1 h2 h4 h5 h6 h7 h8 h9 h10
  exact ⟨e, ⟨blockCost color dimension count + 1,
    blockCost_polynomial count color dimension, compiled_halt_trace he 0 3⟩, hs⟩

def emitLeftover : Code := liftCommand GlobalBasisColumns.emitLeftover 2 3 id low

theorem emitLeftover_eval (d : Data)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ e, Eval emitLeftover (31 * (d.stacks 2).length + 42) d e ∧
      e.stacks = Function.update d.stacks 3
        (record (false :: Encoding.frame (d.stacks 2)) ++ d.stacks 3) := by
  obtain ⟨b, hb, hbs⟩ := GlobalBasisColumns.emitLeftover_eval
    (projectState id low d) h6 h7 h8 h9
  refine ⟨embedState id low d b, ?_, ?_⟩
  · simpa [emitLeftover, projectState, low, Nat.add_assoc] using
      eval_liftCommand_from_state _ 2 3 id low d Function.injective_id low_injective hb
  · change Function.extend low b.stacks d.stacks = _
    rw [hbs, ProgramLinking.extend_update low_injective]
    have hp := congrArg StructuredProgram.State.stacks
      (embedState_project id low d Function.injective_id low_injective)
    change Function.extend low (projectState id low d).stacks d.stacks = d.stacks at hp
    rw [hp]
    rfl

def leftoverStep : Code := .seq (MatrixProgramSupport.copy 5 2 8)
  (.seq emitLeftover (.call (StackRoutines.clearProgram 2 0 1)))

theorem leftoverStep_eval (rank : ℕ) (d : Data)
    (h2 : d.stacks 2 = []) (h5 : d.stacks 5 = unary rank)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ e, Eval leftoverStep (40 * rank + 50) d e ∧
      e.stacks = Function.update d.stacks 3
        (record (Descriptor.encode (.leftover rank)) ++ d.stacks 3) := by
  obtain ⟨a, ha, hsa⟩ := MatrixProgramSupport.copy_eval 5 2 8
    (by decide) (by decide) (by decide) d h8
  obtain ⟨b, hb, hsb⟩ := emitLeftover_eval a
    (by simp [hsa, StackRoutines.copyStacks, h6])
    (by simp [hsa, StackRoutines.copyStacks, h7])
    (by simp [hsa, StackRoutines.copyStacks, h8])
    (by simp [hsa, StackRoutines.copyStacks, h9])
  let e : Data := ⟨readRegs b.regs 0 1 none, StackRoutines.clearStacks 2 b.stacks⟩
  have hc := TupleProgram.clear_eval (2 : Fin 11) (0 : Fin 8) 1 b
  have ha2 : a.stacks 2 = unary rank := by simp [hsa, StackRoutines.copyStacks, h2, h5]
  have hb2 : b.stacks 2 = unary rank := by simp [hsb, ha2]
  refine ⟨e, ?_, ?_⟩
  · have h := ha.seq (hb.seq hc)
    rw [h5, ha2, hb2] at h
    convert h using 1
    all_goals first | rfl | (simp [ unary]; omega)
  · funext i
    fin_cases i <;> simp [e, StackRoutines.clearStacks, hsb, hsa,
      StackRoutines.copyStacks, h2, h5, Descriptor.encode]

def leftoverPorts : UnaryForPrograms.Ports 8 11 := ⟨5, 0, 1⟩
def leftovers : Code := UnaryForPrograms.forCmd leftoverPorts leftoverStep

def leftoverPrefix (count : ℕ) : List Bool :=
  (List.range count).flatMap (fun rank => record (Descriptor.encode (.leftover rank)))

@[simp] theorem leftoverPrefix_zero : leftoverPrefix 0 = [] := rfl

theorem leftoverPrefix_succ (count : ℕ) :
    leftoverPrefix (count + 1) = leftoverPrefix count ++
      record (Descriptor.encode (.leftover count)) := by
  simp [leftoverPrefix, List.range_succ]

def leftoverCost : ℕ → ℕ
  | 0 => 2
  | n + 1 => (40 * n + 50) + leftoverCost n + 2

theorem leftovers_visits (count : ℕ) :
    ∀ d : Data, d.stacks 2 = [] → d.stacks 5 = unary count →
      d.stacks 6 = [] → d.stacks 7 = [] → d.stacks 8 = [] → d.stacks 9 = [] →
      ∃ costs e, UnaryForPrograms.Visits leftoverPorts leftoverStep costs
        (leftoverCost count) d e ∧
        e.stacks = Function.update (Function.update d.stacks 5 []) 3
          (leftoverPrefix count ++ d.stacks 3) := by
  induction count with
  | zero =>
    intro d h2 h5 h6 h7 h8 h9
    refine ⟨[], UnaryForPrograms.popped leftoverPorts d, .done d h5, ?_⟩
    funext i
    fin_cases i <;> simp [UnaryForPrograms.popped, leftoverPorts, h5, unary]
  | succ count ih =>
    intro d h2 h5 h6 h7 h8 h9
    let p := UnaryForPrograms.popped leftoverPorts d
    have hp5 : p.stacks 5 = unary count := by
      simp [p, UnaryForPrograms.popped, leftoverPorts, h5, unary, List.replicate_succ]
    obtain ⟨e, he, hse⟩ := leftoverStep_eval count p
      (by simp [p, UnaryForPrograms.popped, leftoverPorts, h2]) hp5
      (by simp [p, UnaryForPrograms.popped, leftoverPorts, h6])
      (by simp [p, UnaryForPrograms.popped, leftoverPorts, h7])
      (by simp [p, UnaryForPrograms.popped, leftoverPorts, h8])
      (by simp [p, UnaryForPrograms.popped, leftoverPorts, h9])
    obtain ⟨costs, f, hf, hsf⟩ := ih e
      (by simp [hse, p, UnaryForPrograms.popped, leftoverPorts, h2])
      (by simp [hse, hp5])
      (by simp [hse, p, UnaryForPrograms.popped, leftoverPorts, h6])
      (by simp [hse, p, UnaryForPrograms.popped, leftoverPorts, h7])
      (by simp [hse, p, UnaryForPrograms.popped, leftoverPorts, h8])
      (by simp [hse, p, UnaryForPrograms.popped, leftoverPorts, h9])
    refine ⟨(40 * count + 50) :: costs, f,
      .step (by simp [leftoverPorts, h5, unary]) he
        (by simp [hse, leftoverPorts, p]) hf, ?_⟩
    funext i
    fin_cases i <;> simp [hsf, hse, p, UnaryForPrograms.popped, leftoverPorts,
      leftoverPrefix_succ, List.append_assoc]

theorem leftovers_eval (count : ℕ) (d : Data)
    (h2 : d.stacks 2 = []) (h5 : d.stacks 5 = unary count)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ e, Eval leftovers (leftoverCost count) d e ∧
      e.stacks = Function.update (Function.update d.stacks 5 []) 3
        (leftoverPrefix count ++ d.stacks 3) := by
  obtain ⟨costs, e, he, hs⟩ := leftovers_visits count d h2 h5 h6 h7 h8 h9
  exact ⟨e, he.eval, hs⟩

theorem leftoverCost_bound (count : ℕ) : leftoverCost count + 1 ≤ 60 * (count + 1)^2 := by
  induction count with
  | zero => simp [leftoverCost]
  | succ count ih => simp only [leftoverCost]; nlinarith

end SubexponentialSAT.Subexp.GlobalBasisColumnBlocks

end OAI.Algorithms
