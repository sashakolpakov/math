import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchEncoding
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockBasisProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientContext
import OAI.Algorithms.SubexponentialSAT.Subexp.GatherProgram

namespace OAI.Algorithms

/-!
# Gathering a searched basis table into vector-major order

The local search stores ambient coordinates as rows and basis vectors as
columns. Its scalar frames have fixed width, so the checked gather program
can transpose those frames without decoding or changing a field element.
The result is exactly the kernel/complement table consumed by block copying.

This adapter's runtime inputs are the searched table, its unary frame width,
and the explicit transpose read plan. It proves the physical reordering and
the plan's polynomial size; producing the read-plan bytes is a separate stage.
-/

namespace SubexponentialSAT.Subexp.BasisTransposeProgram

open StackEncoding BlockSearchEncoding

def framedCode {A : Type*} (code : BlockCode A) : BlockCode A where
  width := 2 * code.width + 1
  width_pos := by omega
  block a := Encoding.frame (code.block a)
  length_block a := by simp [code.length_block]
  injective_block := by
    intro a b h
    apply code.injective_block
    exact (Encoding.frame_append_injective (bits := code.block a) (bits' := code.block b)
      (rest := []) (rest' := []) (by simpa using h)).1

def transposeIndex {N : ℕ} (i : Fin (N * N)) : Fin (N * N) :=
  finProdFinEquiv ((finProdFinEquiv.symm i).2, (finProdFinEquiv.symm i).1)

def readPlan (N : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (N * N) => (transposeIndex i).val

@[simp] theorem readPlan_length (N : ℕ) : (readPlan N).length = N * N := by
  simp [readPlan]

theorem readPlan_valid (N : ℕ) : ∀ i ∈ readPlan N, i < N * N := by
  intro i hi
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
  exact (transposeIndex j).isLt

theorem readPlan_eq_nested (N : ℕ) :
    readPlan N = (List.ofFn fun col : Fin N =>
      List.ofFn fun row : Fin N => row.val * N + col.val).flatten := by
  rw [readPlan, List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext col
  apply congrArg List.ofFn
  funext row
  have hv : (finProdFinEquiv (col, row)).val = col.val * N + row.val := by
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  have hb : col.val * N + row.val < N * N := by
    rw [← hv]
    exact (finProdFinEquiv (col, row)).isLt
  change (transposeIndex (⟨col.val * N + row.val, hb⟩ : Fin (N * N))).val = _
  rw [show (⟨col.val * N + row.val, hb⟩ : Fin (N * N)) = finProdFinEquiv (col, row) from
    Fin.ext hv.symm]
  simp only [transposeIndex, Equiv.symm_apply_apply]
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem readPlan_eq_ranges (N : ℕ) :
    readPlan N = (List.range N).flatMap fun col =>
      (List.range N).map fun row => row * N + col := by
  rw [readPlan_eq_nested]
  simp only [List.flatMap_def, List.ofFn_eq_map, ← List.map_coe_finRange N,
    List.map_map, Function.comp_def]

def rows {A : Type*} (code : BlockCode A) {N : ℕ} (T : Fin N → Fin N → A) :
    List (List Bool) :=
  List.ofFn fun i => (framedCode code).block (flattenTable T i)

@[simp] theorem rows_length {A : Type*} (code : BlockCode A) {N : ℕ}
    (T : Fin N → Fin N → A) : (rows code T).length = N * N := by
  simp [rows]

theorem rows_width {A : Type*} (code : BlockCode A) {N : ℕ}
    (T : Fin N → Fin N → A) :
    ∀ row ∈ rows code T, row.length = (framedCode code).width := by
  intro row hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact (framedCode code).length_block _

theorem rows_flatten {A : Type*} (code : BlockCode A) {N : ℕ}
    (T : Fin N → Fin N → A) :
    (rows code T).flatten = encodeDataStack (framedCode code) (tableEntries T) := by
  simp only [rows, encodeDataStack_eq_flatMap, tableEntries, List.flatMap_def, List.map_ofFn]
  rfl

theorem gathered_eq_transpose {A : Type*} (code : BlockCode A) {N : ℕ}
    (T : Fin N → Fin N → A) :
    GatherProgram.gathered (rows code T) (readPlan N) =
      encodeDataStack (framedCode code) (tableEntries fun col row => T row col) := by
  simp only [GatherProgram.gathered, readPlan, encodeDataStack_eq_flatMap,
    tableEntries, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  change (rows code T).getD (transposeIndex i).val [] =
    (framedCode code).block (flattenTable (fun col row => T row col) i)
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [rows, List.getElem_ofFn]
  change (framedCode code).block (flattenTable T (transposeIndex i)) = _
  rw [transposeIndex, flattenTable_product]
  rfl

theorem pairEntries_splitPair {A : Type*} {N : ℕ} (d : Fin (N + 1))
    (T : Fin N → Fin N → A) :
    BlockBasisProgram.pairEntries (splitPair d T) =
      tableEntries (fun col row => T row col) := by
  have hn : d.val + (N - d.val) = N := by have := d.isLt; omega
  rw [tableEntries_eq_flatten_rows]
  unfold tableRows
  rw [List.ofFn_congr hn.symm, List.ofFn_add, List.flatten_append]
  rfl

theorem gathered_eq_pairBits {A : Type*} (code : BlockCode A) {N : ℕ}
    (d : Fin (N + 1)) (T : Fin N → Fin N → A) :
    GatherProgram.gathered (rows code T) (readPlan N) =
      BlockBasisProgram.pairBits (framedCode code) (splitPair d T) := by
  rw [BlockBasisProgram.pairBits, pairEntries_splitPair]
  exact gathered_eq_transpose code T

abbrev program := GatherProgram.program

def widthBits {A : Type*} (code : BlockCode A) : List Bool :=
  List.replicate (framedCode code).width true

def inputState {A : Type*} (code : BlockCode A) {N : ℕ} (T : Fin N → Fin N → A) :=
  GatherProgram.inputState (rows code T) (widthBits code) (readPlan N)

def outputState {A : Type*} (code : BlockCode A) {N : ℕ} (T : Fin N → Fin N → A) :=
  GatherProgram.outputState (rows code T) (widthBits code) (readPlan N)

theorem output_pairBits {A : Type*} (code : BlockCode A) {N : ℕ}
    (d : Fin (N + 1)) (T : Fin N → Fin N → A) :
    (outputState code T).stacks 1 =
      BlockBasisProgram.pairBits (framedCode code) (splitPair d T) := by
  rw [outputState, GatherProgram.outputState_output]
  exact gathered_eq_pairBits code d T

def bound (N W : ℕ) : ℕ :=
  7 + (N * N) * ((N * N) * (14 * (2 * W + 1) + 16) + 21 * (2 * W + 1) + 27)

theorem program_run {A : Type*} (code : BlockCode A) {N : ℕ}
    (T : Fin N → Fin N → A) :
    BitProgram.RunsIn program (bound N code.width)
      ((inputState code T).withPC (some program.entry))
      ((outputState code T).withPC none) := by
  have hw : ∀ row ∈ rows code T, row.length = (widthBits code).length := by
    simpa only [widthBits, List.length_replicate] using rows_width code T
  have hp : ∀ i ∈ readPlan N, i < (rows code T).length := by
    simpa only [rows_length] using readPlan_valid N
  obtain ⟨n, hn, ht⟩ := GatherProgram.program_run _ _ _ hw hp
  refine ⟨n, hn.trans ?_, ht⟩
  have h := GatherProgram.traceCost_le (rows code T) (widthBits code).length (readPlan N) hw hp
  simpa only [bound, rows_length, readPlan_length, widthBits, List.length_replicate, framedCode] using h

theorem primitive_run {A : Type*} (code : BlockCode A) {N : ℕ}
    (T : Fin N → Fin N → A) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * bound N code.width)
      (BitProgram.primitiveCfg program ((inputState code T).withPC (some program.entry)))
      (BitProgram.primitiveCfg program ((outputState code T).withPC none)) :=
  BitProgram.primitive_execution program (program_run code T)

theorem readPlan_encoded_length (N : ℕ) :
    (ProgramEncoding.encodeRecords (GatherProgram.indexRecords (readPlan N))).length ≤
      2 * (N * N) * (N * N) + 2 * (N * N) + 1 := by
  rw [GatherProgram.encoded_plan_length, readPlan_length]
  have hs := GatherProgram.plan_sum_le (readPlan N) (N * N) (readPlan_valid N)
  rw [readPlan_length] at hs
  nlinarith

theorem words_eq_flatMap (ws : List (List Bool)) :
    MatrixProgramSupport.words ws = ws.flatMap Encoding.frame := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [MatrixProgramSupport.words, ih]

/-- The actual table bytes retained by the encoded basis search are exactly
the physical source array of this gather call. -/
theorem input_tableBits (p : ℕ) [Fact p.Prime] {N : ℕ}
    (T : Fin N → Fin N → ZMod p) :
    (inputState (MatrixWordEncoding.code p) T).stacks 0 =
      BlockCoefficientProgram.tableBits p T := by
  rw [inputState, GatherProgram.inputState_array, rows_flatten,
    encodeDataStack_eq_flatMap, tableEntries_eq_flatten_rows]
  simp [BlockCoefficientProgram.tableBits, BlockCoefficientProgram.matrixBits,
    BlockCoefficientProgram.matrixRows, BlockCoefficientProgram.vectorWords,
    tableRows, framedCode, MatrixWordEncoding.code, words_eq_flatMap,
    List.flatMap_def, List.map_flatten, List.map_ofFn, Function.comp_def]

end SubexponentialSAT.Subexp.BasisTransposeProgram

end OAI.Algorithms
