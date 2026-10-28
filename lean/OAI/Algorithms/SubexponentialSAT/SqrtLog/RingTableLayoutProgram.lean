import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayoutProgramSemantics

namespace OAI.Algorithms

/-! A uniform finite program transforming power-major scalar records into the
k-major multiplication table. No dimension changes its finite control. -/
namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev initial (powers degree width : List Bool) : Store where
  powers := powers
  degree := degree
  width := width

abbrev finish : Cmd 2 18 := .seq (clear 14) (transfer 17 3)
abbrev command : Cmd 2 18 := .seq (copy 1 11) (.seq kScan finish)
abbrev program : Program 2 18 (size command + 1) := compiled command 0 3

def budget (d B : ℕ) : ℕ :=
  d*(blockBudget B d (2*d*d+d)+2) + 9*d + 3*d^3*B + 13

theorem initialize_eval (powers degree width : List Bool) (regs : Fin 2 → Bool) :
    ∃ rf, Eval (copy 1 11) (7*degree.length+5)
      (state regs (initial powers degree width))
      (state rf {(initial powers degree width) with kc := degree}) := by
  let d := state regs (initial powers degree width)
  have h := copy_eval d 1 11 (by decide) (by decide) (by decide) (by rfl)
  refine ⟨(afterCopy d 1 11).regs, ?_⟩
  convert h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [d, state, tapes, copyStacks]

theorem finish_eval (s : Store) (regs : Fin 2 → Bool) :
    ∃ rf, Eval finish (2*s.ki.length + 3*s.rev.length + 6)
      (state regs s)
      (state rf {s with ki := [], rev := [], out := s.rev.reverse ++ s.out}) := by
  let d := state regs s
  let a := afterClear d 14
  have h1 := clear_eval d 14
  have h2 := transfer_eval a 17 3 (by decide)
  have hf : afterTransfer a 17 3 =
      state (afterTransfer a 17 3).regs {s with ki := [], rev := [], out := s.rev.reverse ++ s.out} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, d, afterClear, clearStacks, transferStacks, state, tapes]
  refine ⟨(afterTransfer a 17 3).regs, ?_⟩
  rw [← hf]
  convert h1.seq h2 using 1
  simp [a, d, afterClear, clearStacks, state, tapes]
  omega

theorem command_eval (rows : List (List Bool)) (degree width : List Bool) (regs : Fin 2 → Bool)
    (hw : ∀ row ∈ rows, row.length = width.length)
    (hn : degree.length*(2*degree.length-1) ≤ rows.length) :
    ∃ n ≤ budget degree.length width.length, ∃ rf,
      Eval command n (state regs (initial rows.flatten degree width))
        (state rf {(initial rows.flatten degree width) with
          out := layoutBits rows degree.length 0 degree.length}) := by
  obtain ⟨r1, h1⟩ := initialize_eval rows.flatten degree width regs
  let s := {(initial rows.flatten degree width) with kc := degree}
  have hv : ∀ k < s.kc.length, ∀ i < s.degree.length, ∀ j < s.degree.length,
      s.ki.length+k+i*s.degree.length+j*s.degree.length < rows.length := by
    intro k hk i hi j hj
    simpa [s, initial] using (table_index_lt degree.length k i j hk hi hj).trans_le hn
  obtain ⟨n, hn', r2, idx, hidx, h2⟩ := kScan_eval rows s r1
    (2*degree.length*degree.length+degree.length) rfl hw rfl rfl rfl rfl rfl rfl
    (by simp [s ]; omega) hv
  let t := {(initial rows.flatten degree width) with
    ki := idx
    rev := (layoutBits rows degree.length 0 degree.length).reverse}
  have h2' : Eval kScan n (state r1 s) (state r2 t) := by
    simpa [s, t, initial] using h2
  obtain ⟨r3, h3⟩ := finish_eval t r2
  have hlen := full_layout_length rows degree.length width.length hw hn
  have hil : idx.length = degree.length := by simpa [s, initial] using hidx
  refine ⟨(7*degree.length+5)+(n+(2*idx.length+3*(layoutBits rows degree.length 0 degree.length).length+6)),
    ?_, r3, ?_⟩
  · simp only [s ] at hn'
    dsimp [budget]
    rw [hil, hlen]
    nlinarith
  · simpa only [command, s, t, initial, List.length_reverse,
      List.reverse_reverse, List.append_nil] using h1.seq (h2'.seq h3)

/-- A real halted finite-table trace, including the terminal instruction. -/
theorem program_run (rows : List (List Bool)) (degree width : List Bool) (regs : Fin 2 → Bool)
    (hw : ∀ row ∈ rows, row.length = width.length)
    (hn : degree.length*(2*degree.length-1) ≤ rows.length) :
    ∃ rf, RunsIn program (budget degree.length width.length + 1)
      ((state regs (initial rows.flatten degree width)).withPC (some program.entry))
      ((state rf {(initial rows.flatten degree width) with
        out := layoutBits rows degree.length 0 degree.length}).withPC none) := by
  obtain ⟨n, hn', rf, he⟩ := command_eval rows degree width regs hw hn
  exact ⟨rf, n+1, by omega, compiled_halt_trace he 0 3⟩

/-- A coarse polynomial bound independent of the stored scalar values. -/
theorem budget_polynomial (d B : ℕ) : budget d B + 1 ≤ 1000*(d+1)^5*(B+1) := by
  simp only [budget, blockBudget, rowBudget, emitBudget]
  ring_nf
  omega

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
