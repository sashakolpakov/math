import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.SubexpMomentProgram

namespace OAI.Algorithms

/-! Actual finite-control framing for extraction jobs.  Source code is captured
once in a preserved word; no job recomputes or interprets that source here. -/

namespace SubexponentialSAT.SubexpJobFrames

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 3 24
abbrev Code := StructuredCalls.Cmd 3 24

def copy (src dst : Fin 24) : Code := .call (StackRoutines.copyProgram src dst 11 0 1)
def copied (src dst : Fin 24) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (src dst : Fin 24) (d : Data)
    (hsd : src ≠ dst) (hs : src ≠ 11) (hd : (11 : Fin 24) ≠ dst)
    (ht : d.stacks 11 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst 11 0 1 hsd hs hd (by decide)
    d.regs d.stacks ht

def move (src dst : Fin 24) : Code := .call (StackRoutines.transferProgram src dst 0 1)
def moved (src dst : Fin 24) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem move_eval (src dst : Fin 24) (d : Data) (hsd : src ≠ dst) :
    Eval (move src dst) (3 * (d.stacks src).length + 3) d (moved src dst d) := by
  apply Eval.call
  exact ListRegisterProgram.transfer_run src dst 0 1 hsd (by decide) d.regs d.stacks

def pop (src : Fin 24) : Code := .base (.atom (.pop src 0 1))
def popped (src : Fin 24) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks src).head?, Function.update d.stacks src (d.stacks src).tail⟩

theorem pop_eval (src : Fin 24) (d : Data) : Eval (pop src) 1 d (popped src d) :=
  .base (.atom _ _)

def writerPorts (dst : Fin 24) : Fin 4 → Fin 24 := ![0, 2, dst, 10]

theorem writerPorts_injective (dst : Fin 24)
    (h₀ : dst ≠ 0) (h₂ : dst ≠ 2) (h₁₀ : dst ≠ 10) :
    Function.Injective (writerPorts dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [writerPorts]

def writer (dst : Fin 24) : Code := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram id (writerPorts dst))

def writerRegs (regs : Fin 3 → Bool) : Fin 3 → Bool := ![true, false, regs 2]

def written (dst : Fin 24) (d : Data) : Data :=
  ⟨writerRegs d.regs, Function.update (Function.update d.stacks 10 []) dst
    (true :: (Encoding.frame (d.stacks 10).reverse ++ d.stacks dst))⟩

private theorem regs_eta (regs : Fin 3 → Bool) : ![regs 0, regs 1, regs 2] = regs := by
  funext i; fin_cases i <;> rfl

theorem writer_eval (dst : Fin 24) (d : Data)
    (h₀ : dst ≠ 0) (h₂ : dst ≠ 2) (h₁₀ : dst ≠ 10) :
    Eval (writer dst) (5 * (d.stacks 10).length + 7) d (written dst d) := by
  let bits := (d.stacks 10).reverse
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 0) (d.stacks 2) (d.stacks dst) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 0) (d.stacks 2) (true :: (Encoding.frame bits ++ d.stacks dst)) []
  have ha : embedState id (writerPorts dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id
      (writerPorts_injective dst h₀ h₂ h₁₀)
    · intro i; fin_cases i <;> rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> simp [a, bits, writerPorts, SubexpNormalizeProgram.filterState]
    · intros; rfl
  have hb : embedState id (writerPorts dst) d b = written dst d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id
      (writerPorts_injective dst h₀ h₂ h₁₀)
    · intro i; fin_cases i <;> rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;>
        simp [b, bits, writerPorts, written, SubexpNormalizeProgram.filterState,
          Ne.symm h₀, Ne.symm h₂, Ne.symm h₁₀]
    · intro i hi
      have hn₁₀ : i ≠ 10 := fun h => hi ⟨3, h.symm⟩
      have hn : i ≠ dst := fun h => hi ⟨2, h.symm⟩
      simp [written, hn₁₀, hn]
  have ht : Trace SubexpNormalizeProgram.emitRecordProgram (5 * bits.length + 7)
      (a.withPC (some SubexpNormalizeProgram.emitRecordProgram.entry)) (b.withPC none) :=
    SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 0) (d.stacks 2)
      (d.stacks dst) (d.regs 0) (d.regs 1) (d.regs 2)
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram id (writerPorts dst) d
    Function.injective_id (writerPorts_injective dst h₀ h₂ h₁₀) ht
  simpa only [writer, ha, hb, bits, List.length_reverse] using h

def sequence : List Code → Code
  | [] => .base .skip
  | cmd :: rest => .seq cmd (sequence rest)

/-- Source capture is on stack 1. Stack 15 receives its forward frame once;
the source and all master words remain unchanged. -/
def prepareSource : Code := sequence [copy 1 17, move 17 10, writer 15, pop 15]

def sourceResult (d : Data) : Data :=
  popped 15 (written 15 (moved 17 10 (copied 1 17 d)))

def sourceCost (d : Data) : ℕ :=
  (7 * (d.stacks 1).length + 5) +
    ((3 * ((copied 1 17 d).stacks 17).length + 3) +
      ((5 * ((moved 17 10 (copied 1 17 d)).stacks 10).length + 7) + (1 + 0)))

theorem prepareSource_eval (d : Data) (ht : d.stacks 11 = []) :
    Eval prepareSource (sourceCost d) d (sourceResult d) := by
  have h₁ := copy_eval 1 17 d (by decide) (by decide) (by decide) ht
  have h₂ := move_eval 17 10 (copied 1 17 d) (by decide)
  have h₃ := writer_eval 15 (moved 17 10 (copied 1 17 d))
    (by decide) (by decide) (by decide)
  have h₄ := pop_eval 15 (written 15 (moved 17 10 (copied 1 17 d)))
  exact h₁.seq (h₂.seq (h₃.seq (h₄.seq (.base (.skip _)))))

/-- The input key is reversed on stack 10. Stack 15 holds the cached forward
source frame, and stack 5 holds the unary output index. Jobs are prepended on
stack 14 in the exact three-frame format consumed by the extraction phase. -/
def emitPrepared : Code := sequence [copy 15 12, writer 12, pop 12,
  copy 5 10, writer 12, pop 12, move 12 10, writer 14]

def frameResult (d : Data) : Data :=
  written 14 (moved 12 10 (popped 12 (written 12 (copied 5 10
    (popped 12 (written 12 (copied 15 12 d)))))))

def frameCost (d : Data) : ℕ :=
  let b := copied 15 12 d
  let c := written 12 b
  let e := popped 12 c
  let f := copied 5 10 e
  let g := written 12 f
  let h := popped 12 g
  let i := moved 12 10 h
  (7 * (d.stacks 15).length + 5) +
    ((5 * (b.stacks 10).length + 7) +
      (1 + ((7 * (e.stacks 5).length + 5) +
        ((5 * (f.stacks 10).length + 7) +
          (1 + ((3 * (h.stacks 12).length + 3) +
            ((5 * (i.stacks 10).length + 7) + 0)))))))

theorem emitPrepared_eval (d : Data) (ht : d.stacks 11 = []) :
    Eval emitPrepared (frameCost d) d (frameResult d) := by
  let b := copied 15 12 d
  let c := written 12 b
  let e := popped 12 c
  let f := copied 5 10 e
  let g := written 12 f
  let h := popped 12 g
  let i := moved 12 10 h
  have h₁ := copy_eval 15 12 d (by decide) (by decide) (by decide) ht
  have h₂ := writer_eval 12 b (by decide) (by decide) (by decide)
  have h₃ := pop_eval 12 c
  have h₄ := copy_eval 5 10 e (by decide) (by decide) (by decide) (by
    simp [e, c, b, popped, written, copied, StackRoutines.copyStacks, ht])
  have h₅ := writer_eval 12 f (by decide) (by decide) (by decide)
  have h₆ := pop_eval 12 g
  have h₇ := move_eval 12 10 h (by decide)
  have h₈ := writer_eval 14 i (by decide) (by decide) (by decide)
  exact h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq
    (h₆.seq (h₇.seq (h₈.seq (.base (.skip _)))))))))

def job (key source : List Bool) (z : ℕ) : SubexpMomentProgram.Job :=
  ⟨List.replicate z true, key, source⟩

theorem sourceResult_frame (d : Data)
    (h₁₀ : d.stacks 10 = []) (h₁₅ : d.stacks 15 = []) (h₁₇ : d.stacks 17 = []) :
    (sourceResult d).stacks 15 = Encoding.frame (d.stacks 1) := by
  simp [sourceResult, popped, written, moved, copied, StackRoutines.copyStacks,
    StackRoutines.transferStacks, h₁₀, h₁₅, h₁₇]

theorem sourceCost_eq (d : Data) (h₁₀ : d.stacks 10 = []) (h₁₇ : d.stacks 17 = []) :
    sourceCost d = 15 * (d.stacks 1).length + 16 := by
  simp [sourceCost, copied, moved, StackRoutines.copyStacks, StackRoutines.transferStacks,
    h₁₀, h₁₇]
  omega

theorem sourceResult_clean (d : Data) :
    (sourceResult d).stacks 10 = [] ∧ (sourceResult d).stacks 17 = [] := by
  simp [sourceResult, popped, written, moved, StackRoutines.transferStacks]

theorem sourceResult_preserved (d : Data) (i : Fin 24)
    (h₁₀ : i ≠ 10) (h₁₅ : i ≠ 15) (h₁₇ : i ≠ 17) :
    (sourceResult d).stacks i = d.stacks i := by
  simp [sourceResult, popped, written, moved, copied, StackRoutines.copyStacks,
    StackRoutines.transferStacks, h₁₀, h₁₅, h₁₇]

theorem frameResult_output (d : Data) (key source : List Bool) (z : ℕ)
    (hk : d.stacks 10 = key.reverse) (hs : d.stacks 15 = Encoding.frame source)
    (hz : d.stacks 5 = List.replicate z true) (hw : d.stacks 12 = []) :
    (frameResult d).stacks 14 =
      true :: (Encoding.frame (job key source z).encode ++ d.stacks 14) := by
  simp [frameResult, written, moved, popped, copied, StackRoutines.copyStacks,
    StackRoutines.transferStacks, hk, hs, hz, hw, job, SubexpMomentProgram.Job.encode,
    List.append_assoc]

theorem frameCost_eq (d : Data) (key source : List Bool) (z : ℕ)
    (hk : d.stacks 10 = key.reverse) (hs : d.stacks 15 = Encoding.frame source)
    (hz : d.stacks 5 = List.replicate z true) (hw : d.stacks 12 = []) :
    frameCost d = 30 * source.length + 21 * key.length + 28 * z + 67 := by
  simp [frameCost, written, moved, popped, copied, StackRoutines.copyStacks,
    StackRoutines.transferStacks, hk, hs, hz, hw, Encoding.length_frame]
  omega

theorem frameResult_clean (d : Data) :
    (frameResult d).stacks 10 = [] ∧ (frameResult d).stacks 12 = [] := by
  simp [frameResult, written, moved, StackRoutines.transferStacks]

theorem frameResult_preserved (d : Data) (i : Fin 24)
    (h₁₀ : i ≠ 10) (h₁₂ : i ≠ 12) (h₁₄ : i ≠ 14) :
    (frameResult d).stacks i = d.stacks i := by
  simp [frameResult, written, moved, popped, copied, StackRoutines.copyStacks,
    StackRoutines.transferStacks, h₁₀, h₁₂, h₁₄]

end SubexponentialSAT.SubexpJobFrames

end OAI.Algorithms
