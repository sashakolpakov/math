import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram

namespace OAI.Algorithms

/-! The finite loop that scans the four color streams. Its loop count and
color width are runtime stacks. The result is specified by a finite fold of
the already proved physical scan step. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 8 23
abbrev ColorRow := Fin 4 → List Bool

def streams (rows : List ColorRow) (i : Fin 4) : List Bool :=
  (rows.map (fun w => w i)).flatten

@[simp] theorem streams_nil (i : Fin 4) : streams [] i = [] := rfl
@[simp] theorem streams_cons (w : ColorRow) (ws : List ColorRow) (i : Fin 4) :
    streams (w :: ws) i = w i ++ streams ws i := rfl

abbrev popCount : Cmd 8 23 := .base (.atom (.pop 22 4 6))
def popped (a : Data) : Data :=
  ⟨readRegs a.regs 4 6 (a.stacks 22).head?, Function.update a.stacks 22 (a.stacks 22).tail⟩

theorem popCount_eval (a : Data) : Eval popCount 1 a (popped a) := .base (.atom _ _)

abbrev body : Cmd 8 23 := .seq MatrixScanStepProgram.command popCount
abbrev loop : Cmd 8 23 := .while 6 body
abbrev command : Cmd 8 23 := .seq popCount loop

def result : List ColorRow → Data → Data
  | [], a => popped a
  | w :: ws, a => result ws (MatrixScanStepProgram.output (popped a) w (streams ws))

structure Ready (a : Data) (rows : List ColorRow) (width : ℕ) : Prop where
  zero0 : a.stacks 0 = []
  zero1 : a.stacks 1 = []
  zero4 : a.stacks 4 = []
  zero10 : a.stacks 10 = []
  zero11 : a.stacks 11 = []
  zero12 : a.stacks 12 = []
  targets : ∀ i, a.stacks (MatrixColorReadProgram.target i) = []
  sources : ∀ i, a.stacks (MatrixColorReadProgram.source i) = streams rows i
  width_length : (a.stacks 21).length = width
  count_length : (a.stacks 22).length = rows.length
  row_length : ∀ w ∈ rows, ∀ i, (w i).length = width

theorem output_stack_frame (a : Data) (w rests : ColorRow) (j : Fin 23)
    (h2 : j ≠ 2) (h3 : j ≠ 3) (hout : j.val < 13 ∨ 21 ≤ j.val) :
    (MatrixScanStepProgram.output a w rests).stacks j = a.stacks j := by
  fin_cases j <;> simp +decide [MatrixScanStepProgram.output, MatrixScanStepProgram.cleared,
    MatrixScanStepProgram.clearedOne, MatrixScanStepProgram.classified,
    MatrixScanStepProgram.frame, MatrixScanStepProgram.restrict, MatrixScanStepProgram.lowPorts,
    MatrixPositionCountProgram.classified, clearStacks] at *

theorem output_targets (a : Data) (w rests : ColorRow) (i : Fin 4) :
    (MatrixScanStepProgram.output a w rests).stacks (MatrixColorReadProgram.target i) = [] := by
  fin_cases i <;> simp +decide [MatrixScanStepProgram.output, MatrixScanStepProgram.cleared,
    MatrixScanStepProgram.clearedOne, MatrixColorReadProgram.target, clearStacks]

theorem output_sources (a : Data) (w rests : ColorRow) (i : Fin 4) :
    (MatrixScanStepProgram.output a w rests).stacks (MatrixColorReadProgram.source i) = rests i := by
  fin_cases i <;> simp +decide [MatrixScanStepProgram.output, MatrixScanStepProgram.cleared,
    MatrixScanStepProgram.clearedOne, MatrixScanStepProgram.classified,
    MatrixScanStepProgram.frame, MatrixScanStepProgram.restrict, MatrixScanStepProgram.lowPorts, MatrixColorReadProgram.source, clearStacks]

theorem output_ready (a : Data) (w : ColorRow) (ws : List ColorRow) (width : ℕ)
    (h : Ready a (w :: ws) width) :
    Ready (MatrixScanStepProgram.output (popped a) w (streams ws)) ws width := by
  constructor
  · rw [output_stack_frame _ _ _ 0 (by decide) (by decide) (by decide)]
    simpa [popped] using h.zero0
  · rw [output_stack_frame _ _ _ 1 (by decide) (by decide) (by decide)]
    simpa [popped] using h.zero1
  · rw [output_stack_frame _ _ _ 4 (by decide) (by decide) (by decide)]
    simpa [popped] using h.zero4
  · rw [output_stack_frame _ _ _ 10 (by decide) (by decide) (by decide)]
    simpa [popped] using h.zero10
  · rw [output_stack_frame _ _ _ 11 (by decide) (by decide) (by decide)]
    simpa [popped] using h.zero11
  · rw [output_stack_frame _ _ _ 12 (by decide) (by decide) (by decide)]
    simpa [popped] using h.zero12
  · exact output_targets _ _ _
  · exact output_sources _ _ _
  · rw [output_stack_frame _ _ _ 21 (by decide) (by decide) (by decide)]
    simpa [popped] using h.width_length
  · rw [output_stack_frame _ _ _ 22 (by decide) (by decide) (by decide)]
    simp only [popped, Function.update_same, List.length_tail]
    rw [h.count_length]
    simp
  · intro v hv i
    exact h.row_length v (List.mem_cons_of_mem w hv) i

theorem popped_guard (a : Data) :
    (popped a).regs 6 = !(a.stacks 22).isEmpty := by
  cases he : a.stacks 22 <;> simp [popped, readRegs, he]

private theorem target_ne_count (i : Fin 4) : MatrixColorReadProgram.target i ≠ 22 := by
  intro h
  have hv := congrArg (fun j : Fin 23 => j.val) h
  change 13 + i.val = 22 at hv
  omega

private theorem source_ne_count (i : Fin 4) : MatrixColorReadProgram.source i ≠ 22 := by
  intro h
  have hv := congrArg (fun j : Fin 23 => j.val) h
  change 17 + i.val = 22 at hv
  omega

theorem loop_eval (a : Data) (rows : List ColorRow) (width : ℕ) (h : Ready a rows width) :
    ∃ n ≤ rows.length * (208 * width + 149) + 1,
      Eval loop n (popped a) (result rows a) := by
  induction rows generalizing a with
  | nil =>
      have hz : a.stacks 22 = [] := List.length_eq_zero_iff.mp h.count_length
      have hg : (popped a).regs 6 = false := by simp [popped_guard, hz]
      exact ⟨1, by simp, Eval.while_false hg⟩
  | cons w ws ih =>
      have hg : (popped a).regs 6 = true := by
        rw [popped_guard]
        have hp : (a.stacks 22).length > 0 := by rw [h.count_length]; simp
        cases he : a.stacks 22 with
        | nil => simp [he] at hp
        | cons bit tail => rfl
      obtain ⟨ns, hns, hs⟩ := MatrixScanStepProgram.command_eval (popped a) w (streams ws)
        (by simpa [popped] using h.zero0) (by simpa [popped] using h.zero1)
        (by simpa [popped] using h.zero4) (by simpa [popped] using h.zero10)
        (by simpa [popped] using h.zero11) (by simpa [popped] using h.zero12)
        (by intro i; simpa [popped, target_ne_count i] using h.targets i)
        (by intro i; simpa [popped, source_ne_count i] using h.sources i)
        (by intro i; simpa [popped, h.width_length] using h.row_length w (by simp) i)
      let next := MatrixScanStepProgram.output (popped a) w (streams ws)
      have hp := popCount_eval next
      obtain ⟨nt, hnt, ht⟩ := ih next (output_ready a w ws width h)
      refine ⟨(ns + 1) + nt + 1, ?_, Eval.while_true hg (hs.seq hp) ht⟩
      have hw : ((popped a).stacks 21).length = width := by simpa [popped] using h.width_length
      rw [hw] at hns
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

def program := compiled command 17 2

theorem program_runsIn (a : Data) (rows : List ColorRow) (width : ℕ) (h : Ready a rows width) :
    RunsIn program (rows.length * (208 * width + 149) + 3)
      (a.withPC (some program.entry)) ((result rows a).withPC none) := by
  obtain ⟨n, hn, ht⟩ := loop_eval a rows width h
  exact ⟨1 + n + 1, by omega, compiled_halt_trace ((popCount_eval a).seq ht) 17 2⟩

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
