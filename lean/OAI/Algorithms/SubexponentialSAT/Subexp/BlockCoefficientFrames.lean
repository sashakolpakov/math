import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchLoop

namespace OAI.Algorithms

/-!
# Actual zero-test and classification calls with frame preservation

The helpers use the fixed programs in BlockSearchLoop. Their postconditions
record preservation of all surrounding stacks and of every register outside
the explicit scratch/output set.
-/

namespace SubexponentialSAT.Subexp.BlockCoefficientFrames

open BitProgram StackRoutines StructuredCalls

abbrev Data := StructuredProgram.State 24 42

private theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

private theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : StructuredProgram.State R S) (source : StructuredProgram.State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target := by
  apply state_ext
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_register reg stack frame source hreg]
      exact (hr i).symm
    · rw [embedState_register_frame reg stack frame source j hj]
      exact (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_stack reg stack frame source hstack]
      exact (hs i).symm
    · rw [embedState_stack_frame reg stack frame source j hj]
      exact (hfs j hj).symm

theorem smallRegisters_injective : Function.Injective BlockSearchLoop.smallRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h)

def zeroState (a : Data) (src : Fin 42) (answer : Bool) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 false) 2 answer,
    Function.update a.stacks src []⟩

theorem zeroAt_eval (a : Data) (src : Fin 42) (words : List (List Bool))
    (hin : a.stacks src = BlockZeroProgram.frames words) :
    Eval (BlockSearchLoop.zeroAt src) ((words.map BlockZeroProgram.frameCost).sum + 4)
      a (zeroState a src (BlockZeroProgram.isZero words)) := by
  let x : StructuredProgram.State 3 1 :=
    ⟨![a.regs 0, a.regs 1, a.regs 2], fun _ => BlockZeroProgram.frames words⟩
  let y : StructuredProgram.State 3 1 :=
    ⟨![false, false, BlockZeroProgram.isZero words], fun _ => []⟩
  have hsrc : Function.Injective (fun _ : Fin 1 => src) := fun i j _ => Subsingleton.elim i j
  have hx : embedState BlockSearchLoop.smallRegisters (fun _ => src) a x = a := by
    apply embedState_eq _ _ smallRegisters_injective hsrc
    · intro i; fin_cases i <;> simp [x, BlockSearchLoop.smallRegisters]
    · intro i; exact hin
    · intros; rfl
    · intros; rfl
  have hy : embedState BlockSearchLoop.smallRegisters (fun _ => src) a y =
      zeroState a src (BlockZeroProgram.isZero words) := by
    apply embedState_eq _ _ smallRegisters_injective hsrc
    · intro i; fin_cases i <;> simp [y, zeroState, BlockSearchLoop.smallRegisters]
    · intro i; simp [y, zeroState]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [BlockSearchLoop.smallRegisters] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [BlockSearchLoop.smallRegisters] using h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, by simpa [BlockSearchLoop.smallRegisters] using h.symm⟩
      simp [zeroState, h0, h1, h2]
    · intro j hj
      have hsrcj : j ≠ src := fun h => hj ⟨0, h.symm⟩
      simp [zeroState, hsrcj]
  have ht : Trace BlockZeroProgram.program ((words.map BlockZeroProgram.frameCost).sum + 4)
      (x.withPC (some BlockZeroProgram.program.entry)) (y.withPC none) :=
    BlockZeroProgram.program_trace words (a.regs 0) (a.regs 1) (a.regs 2)
  have he := eval_call_lifted BlockZeroProgram.program BlockSearchLoop.smallRegisters
    (fun _ => src) a smallRegisters_injective hsrc ht
  simpa only [hx, hy, BlockSearchLoop.zeroAt] using he

def copyState (a : Data) (src dst : Fin 42) : Data :=
  ⟨readRegs a.regs 21 22 none, copyStacks src dst a.stacks⟩

theorem copy_eval (a : Data) (src dst : Fin 42)
    (hsd : src ≠ dst) (hs9 : src ≠ 9) (h9d : (9 : Fin 42) ≠ dst)
    (h9 : a.stacks 9 = []) :
    Eval (BlockSearchLoop.copy src dst) (7 * (a.stacks src).length + 5) a (copyState a src dst) := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace src dst (9 : Fin 42) (21 : Fin 24) 22 hsd hs9 h9d
      (by decide) a.regs a.stacks h9) 7 rfl rfl
  simpa [copyState, BlockSearchLoop.copy, StructuredProgram.State.withPC,
    copyResult, copyProgram, Nat.add_assoc] using h

theorem zeroFrom_eval (a : Data) (src : Fin 42) (flag : Fin 24) (words : List (List Bool))
    (hs9 : src ≠ 9) (hs22 : src ≠ 22) (h9 : a.stacks 9 = []) (h22 : a.stacks 22 = [])
    (hin : a.stacks src = BlockZeroProgram.frames words) :
    ∃ n b, n ≤ 10 * (BlockZeroProgram.frames words).length + 10 ∧
      Eval (BlockSearchLoop.zeroFrom src flag) n a b ∧ b.stacks = a.stacks ∧
      b.regs flag = BlockZeroProgram.isZero words ∧
      (∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 21 → j ≠ 22 → j ≠ flag → b.regs j = a.regs j) := by
  let a1 := copyState a src 22
  let a2 := zeroState a1 22 (BlockZeroProgram.isZero words)
  let b := (StructuredProgram.Atom.copy flag (2 : Fin 24)).eval a2
  have hc := copy_eval a src 22 hs22 hs9 (by decide) h9
  have hz := zeroAt_eval a1 22 words (by simp [a1, copyState, copyStacks, hin, h22])
  have he : Eval (BlockSearchLoop.zeroFrom src flag)
      ((7 * (a.stacks src).length + 5) +
        (((words.map BlockZeroProgram.frameCost).sum + 4) + (1 + 0))) a b :=
    hc.seq (hz.seq ((Eval.base (.atom _ _)).seq (Eval.base (.skip _))))
  refine ⟨_, b, ?_, he, ?_, ?_, ?_⟩
  · have h := BlockZeroProgram.cost_le words
    rw [hin]
    omega
  · funext j
    by_cases hj : j = 22
    · subst j
      simp [b, a2, a1, zeroState, copyState, copyStacks, h22,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
    · simp [b, a2, a1, zeroState, copyState, copyStacks, hj,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
  · simp [b, a2, zeroState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  · intro j h0 h1 h2 h21 h22' hf
    simp [b, a2, a1, zeroState, copyState, readRegs, h0, h1, h2, h21, h22', hf,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]

def skipState (a : Data) (words : List (List Bool)) (rest : List Bool) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 false) 2
      (a.regs 2 || !words.isEmpty),
    Function.update (Function.update a.stacks 22 []) 23 rest⟩

theorem skipPrefix_eval (a : Data) (words : List (List Bool)) (rest : List Bool)
    (hc : (a.stacks 22).length = words.length)
    (hin : a.stacks 23 = BlockZeroProgram.frames words ++ rest) :
    Eval BlockSearchLoop.skipPrefix (BlockZeroProgram.skipCost words) a (skipState a words rest) := by
  let x : StructuredProgram.State 3 2 :=
    ⟨![a.regs 0, a.regs 1, a.regs 2], ![a.stacks 22, BlockZeroProgram.frames words ++ rest]⟩
  let y : StructuredProgram.State 3 2 :=
    ⟨![false, false, a.regs 2 || !words.isEmpty], ![[], rest]⟩
  have hstack : Function.Injective (![22, 23] : Fin 2 → Fin 42) := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  have hx : embedState BlockSearchLoop.smallRegisters ![22, 23] a x = a := by
    apply embedState_eq _ _ smallRegisters_injective hstack
    · intro i; fin_cases i <;> simp [x, BlockSearchLoop.smallRegisters]
    · intro i; fin_cases i <;> simp [x, hin]
    · intros; rfl
    · intros; rfl
  have hy : embedState BlockSearchLoop.smallRegisters ![22, 23] a y = skipState a words rest := by
    apply embedState_eq _ _ smallRegisters_injective hstack
    · intro i; fin_cases i <;> simp [y, skipState, BlockSearchLoop.smallRegisters]
    · intro i; fin_cases i <;> simp [y, skipState]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [BlockSearchLoop.smallRegisters] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [BlockSearchLoop.smallRegisters] using h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, by simpa [BlockSearchLoop.smallRegisters] using h.symm⟩
      simp [skipState, h0, h1, h2]
    · intro j hj
      have h22 : j ≠ 22 := fun h => hj ⟨0, by simpa using h.symm⟩
      have h23 : j ≠ 23 := fun h => hj ⟨1, by simpa using h.symm⟩
      simp [skipState, h22, h23]
  have ht : Trace BlockZeroProgram.skipProgram (BlockZeroProgram.skipCost words)
      (x.withPC (some BlockZeroProgram.skipProgram.entry)) (y.withPC none) :=
    BlockZeroProgram.skipProgram_trace words rest (a.stacks 22) hc (a.regs 0) (a.regs 1) (a.regs 2)
  have he := eval_call_lifted BlockZeroProgram.skipProgram BlockSearchLoop.smallRegisters
    ![22, 23] a smallRegisters_injective hstack ht
  simpa only [hx, hy, BlockSearchLoop.skipPrefix] using he

theorem tailZero_eval (a : Data) (pre post : List (List Bool))
    (hc : (a.stacks 8).length = pre.length)
    (hin : a.stacks 40 = BlockZeroProgram.frames (pre ++ post))
    (h9 : a.stacks 9 = []) (h22 : a.stacks 22 = []) (h23 : a.stacks 23 = []) :
    ∃ n b, n ≤ 7 * (a.stacks 8).length +
        11 * (BlockZeroProgram.frames (pre ++ post)).length + 18 ∧
      Eval BlockSearchLoop.tailZero n a b ∧ b.stacks = a.stacks ∧
      b.regs 19 = BlockZeroProgram.isZero post ∧
      (∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 19 → j ≠ 21 → j ≠ 22 → b.regs j = a.regs j) := by
  let a1 := copyState a 8 22
  let a2 := copyState a1 40 23
  let a3 := skipState a2 pre (BlockZeroProgram.frames post)
  let a4 := zeroState a3 23 (BlockZeroProgram.isZero post)
  let b := (StructuredProgram.Atom.copy (19 : Fin 24) 2).eval a4
  have hframes : BlockZeroProgram.frames (pre ++ post) =
      BlockZeroProgram.frames pre ++ BlockZeroProgram.frames post := by
    simp [BlockZeroProgram.frames]
  have t0 := copy_eval a 8 22 (by decide) (by decide) (by decide) h9
  have t1 := copy_eval a1 40 23 (by decide) (by decide) (by decide)
    (by simp [a1, copyState, copyStacks, h9])
  have t2 := skipPrefix_eval a2 pre (BlockZeroProgram.frames post)
    (by simp [a2, a1, copyState, copyStacks, h22, hc])
    (by simp [a2, a1, copyState, copyStacks, h23, hin, hframes])
  have t3 := zeroAt_eval a3 23 post (by simp [a3, skipState])
  have he : Eval BlockSearchLoop.tailZero
      ((7 * (a.stacks 8).length + 5) +
        ((7 * (a1.stacks 40).length + 5) +
          (BlockZeroProgram.skipCost pre + (((post.map BlockZeroProgram.frameCost).sum + 4) + (1 + 0)))))
      a b := t0.seq (t1.seq (t2.seq (t3.seq ((Eval.base (.atom _ _)).seq (Eval.base (.skip _))))))
  refine ⟨_, b, ?_, he, ?_, ?_, ?_⟩
  · have hp := BlockZeroProgram.skipCost_le pre
    have hq := BlockZeroProgram.cost_le post
    have h40 : a1.stacks 40 = a.stacks 40 := by simp [a1, copyState, copyStacks]
    rw [h40, hin, hframes, List.length_append]
    omega
  · funext j
    by_cases h22j : j = 22
    · subst j
      simp [b, a4, a3, a2, a1, zeroState, skipState, copyState, copyStacks, h22,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
    by_cases h23j : j = 23
    · subst j
      simp [b, a4, a3, a2, a1, zeroState, skipState, copyState, copyStacks, h23,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
    · simp [b, a4, a3, a2, a1, zeroState, skipState, copyState, copyStacks, h22j, h23j,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
  · simp [b, a4, zeroState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  · intro j h0 h1 h2 h19 h21 h22j
    simp [b, a4, a3, a2, a1, zeroState, skipState, copyState, readRegs,
      h0, h1, h2, h19, h21, h22j, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      execInstr]

theorem classifyRegisters_injective : Function.Injective BlockSearchLoop.classifyRegisters := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [BlockSearchLoop.classifyRegisters]

def classified (a : Data) : Data :=
  ⟨Function.update a.regs 16 (BlockZeroProgram.classifyResult
    (a.regs 17) (a.regs 18) (a.regs 19) (a.regs 20)), a.stacks⟩

theorem classify_eval (a : Data) :
    ∃ n ≤ 6, Eval BlockSearchLoop.classify n a (classified a) := by
  let x : StructuredProgram.State 5 1 :=
    ⟨![a.regs 17, a.regs 18, a.regs 19, a.regs 20, a.regs 16], fun _ => a.stacks 22⟩
  let y : StructuredProgram.State 5 1 :=
    ⟨![a.regs 17, a.regs 18, a.regs 19, a.regs 20,
      BlockZeroProgram.classifyResult (a.regs 17) (a.regs 18) (a.regs 19) (a.regs 20)],
      fun _ => a.stacks 22⟩
  have hstack : Function.Injective (fun _ : Fin 1 => (22 : Fin 42)) :=
    fun i j _ => Subsingleton.elim i j
  have hx : embedState BlockSearchLoop.classifyRegisters (fun _ => (22 : Fin 42)) a x = a := by
    apply embedState_eq _ _ classifyRegisters_injective hstack
    · intro i; fin_cases i <;> simp [x, BlockSearchLoop.classifyRegisters]
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hy : embedState BlockSearchLoop.classifyRegisters (fun _ => (22 : Fin 42)) a y = classified a := by
    apply embedState_eq _ _ classifyRegisters_injective hstack
    · intro i; fin_cases i <;> simp [y, classified, BlockSearchLoop.classifyRegisters]
    · intros; rfl
    · intro j hj
      have h16 : j ≠ 16 := fun h => hj ⟨4, by simpa [BlockSearchLoop.classifyRegisters] using h.symm⟩
      simp [classified, h16]
    · intros; rfl
  obtain ⟨n, hn, ht⟩ := BlockZeroProgram.classifyProgram_runsIn
    (a.regs 17) (a.regs 18) (a.regs 19) (a.regs 20) (a.regs 16) (a.stacks 22)
  have ht' : Trace BlockZeroProgram.classifyProgram n
      (x.withPC (some BlockZeroProgram.classifyProgram.entry)) (y.withPC none) := ht
  have he := eval_call_lifted BlockZeroProgram.classifyProgram BlockSearchLoop.classifyRegisters
    (fun _ => (22 : Fin 42)) a classifyRegisters_injective hstack ht'
  exact ⟨n, hn, by simpa only [hx, hy, BlockSearchLoop.classify] using he⟩

@[simp] theorem classified_stacks (a : Data) : (classified a).stacks = a.stacks := rfl

@[simp] theorem classified_flag (a : Data) : (classified a).regs 16 =
    BlockZeroProgram.classifyResult (a.regs 17) (a.regs 18) (a.regs 19) (a.regs 20) := by
  simp [classified]

theorem classified_register_frame (a : Data) (j : Fin 24) (hj : j ≠ 16) :
    (classified a).regs j = a.regs j := by simp [classified, hj]

end SubexponentialSAT.Subexp.BlockCoefficientFrames

end OAI.Algorithms
