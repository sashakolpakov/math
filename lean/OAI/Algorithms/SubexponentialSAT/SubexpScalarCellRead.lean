import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposeProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding
import OAI.Algorithms.SubexponentialSAT.ArrayUpdateLifted

namespace OAI.Algorithms

/-!
# Preserving scalar-cell access with runtime addresses

The fixed program forms the unary address `row * N + col`, then calls the
measured persistent array reader. The table already contains complete scalar
frames, so selecting a cell requires no decoding or re-encoding.

Ports: table 0, output 1, unary dimension 2, unary row 3, unary column 4,
unary frame width 5, and initially empty scratch 6--11. Only output 1 changes.
-/

namespace SubexponentialSAT.SubexpScalarCellRead

open BitProgram StructuredCalls StackRoutines
open Subexp.BasisTransposePlanProgram (unary)

abbrev Data := State 5 12
abbrev Code := Cmd 5 12

/-- Local address generation uses the checked unary-copy multiplication loop. -/
abbrev indexCommand : Cmd 3 7 :=
  .seq (Subexp.BasisTransposePlanProgram.copy 2 5)
    (.seq Subexp.BasisTransposePlanProgram.multiply
      (Subexp.BasisTransposePlanProgram.copy 3 4))

def indexCost (N row col : ℕ) : ℕ :=
  (7 * row + 5) + (row * (7 * N + 7) + 2) + (7 * col + 5)

theorem indexCommand_eval (N row col : ℕ) (d : State 3 7)
    (hN : d.stacks 0 = unary N) (hr : d.stacks 2 = unary row)
    (hc : d.stacks 3 = unary col) (h4 : d.stacks 4 = [])
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) :
    ∃ n e, Eval indexCommand n d e ∧ n ≤ indexCost N row col ∧
      e.stacks = Function.update d.stacks 4 (unary (row * N + col)) := by
  let a := Subexp.BasisTransposePlanProgram.copied 2 5 d
  have haN : a.stacks 0 = unary N := by
    simp [a, hN]
  have har : a.stacks 5 = unary row := by
    simp [a, hr, h5]
  have ha6 : a.stacks 6 = [] := by
    simp [a, h6]
  obtain ⟨n, b, hb, hn, hbs⟩ :=
    Subexp.BasisTransposePlanProgram.multiply_eval N row a haN har ha6
  have hb4 : b.stacks 4 = unary (row * N) := by
    simp [hbs, a, h4]
  have hb3 : b.stacks 3 = unary col := by
    simp [hbs, a, hc]
  have hb6 : b.stacks 6 = [] := by
    simp [hbs, a, h6]
  let e := Subexp.BasisTransposePlanProgram.copied 3 4 b
  have he4 : e.stacks 4 = unary (row * N + col) := by
    simp [e, hb3, hb4,
      unary, Nat.add_comm]
  refine ⟨(7 * (d.stacks 2).length + 5) + (n + (7 * (b.stacks 3).length + 5)),
    e, ?_, ?_, ?_⟩
  · exact (Subexp.BasisTransposePlanProgram.copy_eval 2 5 d
      (by decide) (by decide) (by decide) h6).seq
      (hb.seq (Subexp.BasisTransposePlanProgram.copy_eval 3 4 b
        (by decide) (by decide) (by decide) hb6))
  · simp only [hr, hb3, unary, List.length_replicate]
    unfold indexCost
    omega
  · funext i
    by_cases hi : i = 4
    · subst i
      simpa only [Function.update_self] using he4
    · fin_cases i <;>
        simp_all [e, a]

def indexRegisters : Fin 3 → Fin 5 := Fin.castAdd 2
def indexPorts : Fin 7 → Fin 12 := ![2, 11, 3, 4, 6, 7, 8]

theorem indexRegisters_injective : Function.Injective indexRegisters :=
  Fin.castAdd_injective 3 2

theorem indexPorts_injective : Function.Injective indexPorts := by decide

def generateIndex : Code := liftCommand indexCommand 0 4 indexRegisters indexPorts

/-- Runtime scratch requirements; all six stacks are restored by the program. -/
def Clean (d : Data) : Prop := ∀ i : Fin 12, 6 ≤ i.val → d.stacks i = []

theorem generateIndex_eval (N row col : ℕ) (d : Data)
    (hN : d.stacks 2 = unary N) (hr : d.stacks 3 = unary row)
    (hc : d.stacks 4 = unary col) (clean : Clean d) :
    ∃ n e, Eval generateIndex n d e ∧ n ≤ indexCost N row col + 1 ∧
      e.stacks = Function.update d.stacks 6 (unary (row * N + col)) := by
  obtain ⟨n, b, hb, hn, hbs⟩ := indexCommand_eval N row col
    (projectState indexRegisters indexPorts d) hN hr hc
    (clean 6 (by decide)) (clean 7 (by decide)) (clean 8 (by decide))
  refine ⟨n + 1, embedState indexRegisters indexPorts d b,
    eval_liftCommand_from_state indexCommand 0 4 indexRegisters indexPorts d
      indexRegisters_injective indexPorts_injective hb, by omega, ?_⟩
  change Function.extend indexPorts b.stacks d.stacks = _
  rw [hbs, ProgramLinking.extend_update indexPorts_injective]
  have hbase := congrArg StructuredProgram.State.stacks
    (embedState_project indexRegisters indexPorts d
      indexRegisters_injective indexPorts_injective)
  change Function.extend indexPorts
    (projectState indexRegisters indexPorts d).stacks d.stacks = d.stacks at hbase
  rw [hbase]
  rfl

def readPorts : Fin 8 ↪ Fin 12 := ⟨![0, 1, 6, 5, 7, 8, 9, 10], by decide⟩

def readCell : Code := .call (ArrayUpdateLifted.readProgramAt readPorts 0 1)
def command : Code := .seq generateIndex readCell
def program := compiled command 0 1

/-- Includes the address subprogram's return and the complete persistent read. -/
def cost (N row col W : ℕ) : ℕ :=
  indexCost N row col + 1 + (row * N + col) * (14 * W + 10) + 15 * W + 16

/-- Selection from any fixed-width record table. The complete output frame
is prefixed to the caller's output; every other stack has its original value. -/
theorem command_eval (N row col : ℕ) (rows : List (List Bool))
    (width : List Bool) (d : Data)
    (hsource : d.stacks 0 = rows.flatten)
    (hN : d.stacks 2 = unary N) (hr : d.stacks 3 = unary row)
    (hc : d.stacks 4 = unary col) (hw : d.stacks 5 = width)
    (clean : Clean d) (hi : row * N + col < rows.length)
    (hrows : ∀ record ∈ rows, record.length = width.length) :
    ∃ n e, Eval command n d e ∧ n ≤ cost N row col width.length ∧
      e.stacks = Function.update d.stacks 1
        (rows.getD (row * N + col) [] ++ d.stacks 1) := by
  obtain ⟨n, a, ha, hn, has⟩ := generateIndex_eval N row col d hN hr hc clean
  let i := row * N + col
  have hitake : (rows.take i).length = i :=
    List.length_take_of_le (show i ≤ rows.length from Nat.le_of_lt hi)
  have ht : ∀ record ∈ rows.take i, record.length = width.length := by
    intro record hrecord
    exact hrows record (List.mem_of_mem_take hrecord)
  have hlen : (rows.getD i []).length = width.length := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hrows _ (List.getElem_mem hi)
  have hread := ArrayUpdateLifted.readProgramAt_eval readPorts 0 1 (by decide)
    (rows.take i) (rows.getD i []) (rows.drop (i + 1)).flatten width (unary i)
    a.regs a.stacks
    (by simpa [has, readPorts, hsource] using Subexp.GatherProgram.row_decomposition rows i hi)
    (by simpa [has, readPorts] using hw)
    (by simp [has, readPorts, i])
    (by simpa only [unary, List.length_replicate] using hitake.symm)
    ht hlen
    (by simpa [has, readPorts] using clean 7 (by decide))
    (by simpa [has, readPorts] using clean 8 (by decide))
    (by simpa [has, readPorts] using clean 9 (by decide))
    (by simpa [has, readPorts] using clean 10 (by decide))
  let e : Data := ⟨readRegs a.regs 0 1 none,
    ArrayUpdateLifted.readStacksAt readPorts (rows.getD i []) a.stacks⟩
  refine ⟨n + ((rows.take i).length * (14 * width.length + 10) + 15 * width.length + 16),
    e, ha.seq hread, ?_, ?_⟩
  · rw [hitake]
    unfold cost
    dsimp only [i] at *
    omega
  · funext j
    by_cases hj1 : j = 1
    · subst j
      simp [e, ArrayUpdateLifted.readStacksAt, readPorts, has, i]
    · by_cases hj6 : j = 6
      · subst j
        simp [e, ArrayUpdateLifted.readStacksAt, readPorts, has, clean 6 (by decide), i]
      · simp [e, ArrayUpdateLifted.readStacksAt, readPorts, has, hj1, hj6, i]

theorem cost_le_cubic (N row col W : ℕ) :
    cost N row col W ≤ 120 * (N + row + col + W + 1)^3 := by
  let L := N + row + col + W + 1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hN : N ≤ L := by dsimp [L]; omega
  have hr : row ≤ L := by dsimp [L]; omega
  have hc : col ≤ L := by dsimp [L]; omega
  have hw : W ≤ L := by dsimp [L]; omega
  have hL2 : L ≤ L * L := by nlinarith
  have hL3 : L * L ≤ L * L * L := Nat.mul_le_mul_right L hL2
  have hrN : row * N ≤ L * L * L := (Nat.mul_le_mul hr hN).trans hL3
  have hcW : col * W ≤ L * L * L := (Nat.mul_le_mul hc hw).trans hL3
  have hrNW : row * N * W ≤ L * L * L :=
    Nat.mul_le_mul (Nat.mul_le_mul hr hN) hw
  have hrc : row ≤ L * L * L := hr.trans (hL2.trans hL3)
  have hcc : col ≤ L * L * L := hc.trans (hL2.trans hL3)
  have hwc : W ≤ L * L * L := hw.trans (hL2.trans hL3)
  have h1c : 1 ≤ L * L * L := hL.trans (hL2.trans hL3)
  change cost N row col W ≤ 120 * L^3
  unfold cost indexCost
  nlinarith only [hrN, hcW, hrNW, hrc, hcc, hwc, h1c]

theorem program_run (N row col : ℕ) (rows : List (List Bool))
    (width : List Bool) (d : Data)
    (hsource : d.stacks 0 = rows.flatten)
    (hN : d.stacks 2 = unary N) (hr : d.stacks 3 = unary row)
    (hc : d.stacks 4 = unary col) (hw : d.stacks 5 = width)
    (clean : Clean d) (hi : row * N + col < rows.length)
    (hrows : ∀ record ∈ rows, record.length = width.length) :
    ∃ e : Data, RunsIn program (cost N row col width.length + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 1
        (rows.getD (row * N + col) [] ++ d.stacks 1) := by
  obtain ⟨n, e, he, hn, hes⟩ := command_eval N row col rows width d
    hsource hN hr hc hw clean hi hrows
  exact ⟨e, ⟨n + 1, by omega, compiled_halt_trace he 0 1⟩, hes⟩

/-- Measured input bytes, including the retained table and four unary inputs. -/
def inputSize (d : Data) : ℕ :=
  (d.stacks 0).length + (d.stacks 2).length + (d.stacks 3).length +
    (d.stacks 4).length + (d.stacks 5).length

theorem program_run_serialized (N row col : ℕ) (rows : List (List Bool))
    (width : List Bool) (d : Data)
    (hsource : d.stacks 0 = rows.flatten)
    (hN : d.stacks 2 = unary N) (hr : d.stacks 3 = unary row)
    (hc : d.stacks 4 = unary col) (hw : d.stacks 5 = width)
    (clean : Clean d) (hi : row * N + col < rows.length)
    (hrows : ∀ record ∈ rows, record.length = width.length) :
    ∃ e : Data, RunsIn program (120 * (inputSize d + 1)^3 + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 1
        (rows.getD (row * N + col) [] ++ d.stacks 1) := by
  obtain ⟨e, he, hes⟩ := program_run N row col rows width d
    hsource hN hr hc hw clean hi hrows
  have hs : N + row + col + width.length + 1 ≤ inputSize d + 1 := by
    simp only [inputSize, hN, hr, hc, hw, unary, List.length_replicate]
    omega
  have hb : cost N row col width.length + 1 ≤ 120 * (inputSize d + 1)^3 + 1 :=
    Nat.add_le_add_right ((cost_le_cubic N row col width.length).trans
      (Nat.mul_le_mul_left 120 (Nat.pow_le_pow_left hs 3))) 1
  exact ⟨e, he.mono hb, hes⟩

/-- The address uses coordinate-major row order, with no reversal of frame bits. -/
theorem table_cell {A : Type*} (code : StackEncoding.BlockCode A) {N : ℕ}
    (T : Fin N → Fin N → A) (row col : Fin N) :
    (Subexp.BasisTransposeProgram.rows code T).getD (row.val * N + col.val) [] =
      Encoding.frame (code.block (T row col)) := by
  let i : Fin (N * N) := finProdFinEquiv (row, col)
  have hiv : i.val = row.val * N + col.val := by
    simp [i, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [← hiv, List.getD_eq_getElem _ _ (by
    simpa only [Subexp.BasisTransposeProgram.rows_length] using i.isLt)]
  simp only [Subexp.BasisTransposeProgram.rows, List.getElem_ofFn]
  change Encoding.frame (code.block (Subexp.BlockSearchEncoding.flattenTable T i)) = _
  rw [show i = finProdFinEquiv (row, col) from rfl,
    Subexp.BlockSearchEncoding.flattenTable_product]

/-- In the matrix scalar encoding, the selected bytes are exactly the existing
forward scalar frame. No value-dependent instruction or decoding assumption is used. -/
theorem scalar_command_eval (p N : ℕ) [Fact p.Prime]
    (T : Fin N → Fin N → ZMod p) (row col : Fin N) (d : Data)
    (hsource : d.stacks 0 =
      (Subexp.BasisTransposeProgram.rows (Subexp.MatrixWordEncoding.code p) T).flatten)
    (hN : d.stacks 2 = unary N) (hr : d.stacks 3 = unary row.val)
    (hc : d.stacks 4 = unary col.val)
    (hw : d.stacks 5 = unary (2 * Subexp.MatrixWordEncoding.width p + 1))
    (ho : d.stacks 1 = []) (clean : Clean d) :
    ∃ n e, Eval command n d e ∧
      n ≤ cost N row.val col.val (2 * Subexp.MatrixWordEncoding.width p + 1) ∧
      e.stacks = Function.update d.stacks 1
        (Encoding.frame (Subexp.MatrixWordEncoding.word p (T row col))) := by
  have hi : row.val * N + col.val <
      (Subexp.BasisTransposeProgram.rows (Subexp.MatrixWordEncoding.code p) T).length := by
    simpa [Subexp.BasisTransposeProgram.rows_length, finProdFinEquiv,
      Nat.mul_comm, Nat.add_comm] using (finProdFinEquiv (row, col)).isLt
  have hwidth : ∀ record ∈
      Subexp.BasisTransposeProgram.rows (Subexp.MatrixWordEncoding.code p) T,
      record.length = (unary (2 * Subexp.MatrixWordEncoding.width p + 1)).length := by
    simpa [unary, Subexp.BasisTransposeProgram.framedCode, Subexp.MatrixWordEncoding.code]
      using Subexp.BasisTransposeProgram.rows_width (Subexp.MatrixWordEncoding.code p) T
  obtain ⟨n, e, he, hn, hes⟩ := command_eval N row.val col.val
    (Subexp.BasisTransposeProgram.rows (Subexp.MatrixWordEncoding.code p) T)
    (unary (2 * Subexp.MatrixWordEncoding.width p + 1)) d
    hsource hN hr hc hw clean hi hwidth
  refine ⟨n, e, he, ?_, ?_⟩
  · simpa only [unary, List.length_replicate] using hn
  · simpa only [table_cell, Subexp.MatrixWordEncoding.code, ho, List.append_nil] using hes

theorem scalar_program_run (p N : ℕ) [Fact p.Prime]
    (T : Fin N → Fin N → ZMod p) (row col : Fin N) (d : Data)
    (hsource : d.stacks 0 =
      (Subexp.BasisTransposeProgram.rows (Subexp.MatrixWordEncoding.code p) T).flatten)
    (hN : d.stacks 2 = unary N) (hr : d.stacks 3 = unary row.val)
    (hc : d.stacks 4 = unary col.val)
    (hw : d.stacks 5 = unary (2 * Subexp.MatrixWordEncoding.width p + 1))
    (ho : d.stacks 1 = []) (clean : Clean d) :
    ∃ e : Data,
      RunsIn program (cost N row.val col.val (2 * Subexp.MatrixWordEncoding.width p + 1) + 1)
        (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 1
        (Encoding.frame (Subexp.MatrixWordEncoding.word p (T row col))) := by
  obtain ⟨n, e, he, hn, hes⟩ := scalar_command_eval p N T row col d
    hsource hN hr hc hw ho clean
  exact ⟨e, ⟨n + 1, by omega, compiled_halt_trace he 0 1⟩, hes⟩

end SubexponentialSAT.SubexpScalarCellRead

end OAI.Algorithms
