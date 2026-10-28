import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScalarBankProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientContext
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPredicate
import OAI.Algorithms.SubexponentialSAT.SubexpTupleRefinement

namespace OAI.Algorithms

/-!
# Actual enumeration of a matrix image

The fixed program generates coefficient records and applies the actual
matrix-vector service to each record.  Its input matrix is prepared data.
Construction of that matrix from a global block decomposition is a separate
stage.  Output records contain forward flat canonical prime-field words;
the record order is the reverse of the tuple generator's actual order.
-/

namespace SubexponentialSAT.Subexp.MatrixImageEnumeration

open BitProgram StructuredCalls SubexpScanPrimitives
open MatrixWordEncoding BlockCoefficientProgram SubexpTupleRefinement
open scoped BigOperators

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

abbrev Data := State 13 32

def alphabet (p : ℕ) : List (ZMod p) := (QuarticSearch.elements p).reverse

def tokens (p : ℕ) [Fact p.Prime] : List (List Bool) :=
  (alphabet p).map (BlockSearchPredicate.scalarCode p).block

/-- A bounded decoder used only to state which coefficients the physical
records contain. The executed program passes those records to the matrix
service directly. -/
def decode (p : ℕ) : (n : ℕ) → List Bool → Fin n → ZMod p
  | 0, _ => Fin.elim0
  | n + 1, bits =>
    let fields := (Encoding.readFrame bits).getD ([], [])
    Fin.cons (BinaryArithmetic.toNat fields.1 : ZMod p) (decode p n fields.2)

theorem decode_words (p : ℕ) [Fact p.Prime] {n : ℕ} (v : Fin n → ZMod p) :
    decode p n (MatrixProgramSupport.words (vectorWords p v)) = v := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [vectorWords, List.ofFn_succ, MatrixProgramSupport.words, decode,
      Encoding.readFrame_frame_append, Option.getD_some, word_field_value]
    rw [show MatrixProgramSupport.words (List.ofFn fun i => word p (v i.succ)) =
      MatrixProgramSupport.words (vectorWords p (fun i => v i.succ)) from rfl]
    rw [ih]
    exact Fin.cons_self_tail v

theorem decode_encode (p : ℕ) [Fact p.Prime] {n : ℕ} (v : Fin n → ZMod p) :
    decode p n (encodeTuple (BlockSearchPredicate.scalarCode p) v) = v := by
  rw [BlockSearchPredicate.encoded_vector_eq_words]
  exact decode_words p v

def coefficientRows (p n : ℕ) [Fact p.Prime] : List (List Bool) :=
  TupleProgram.powerRows (tokens p) n [[]]

def coefficients (p n : ℕ) [Fact p.Prime] : List (Fin n → ZMod p) :=
  (coefficientRows p n).map (decode p n)

theorem coefficientRows_valid (p n : ℕ) [Fact p.Prime] (bits : List Bool)
    (h : bits ∈ coefficientRows p n) :
    MatrixProgramSupport.words (vectorWords p (decode p n bits)) = bits := by
  obtain ⟨v, _, rfl⟩ := (mem_powerRows_encoded
    (BlockSearchPredicate.scalarCode p) (alphabet p) n bits).mp h
  rw [decode_encode]
  exact (BlockSearchPredicate.encoded_vector_eq_words p v).symm

theorem coefficients_perm (p n : ℕ) [Fact p.Prime] :
    (coefficients p n).Perm (QuarticSearch.vectors (alphabet p) n) := by
  have h := (powerRows_encoded_perm (BlockSearchPredicate.scalarCode p)
    (alphabet p) n).map (decode p n)
  simpa only [coefficients, coefficientRows, tokens, List.map_map, Function.comp_def,
    decode_encode, List.map_id']
    using h

theorem coefficients_nodup (p n : ℕ) [Fact p.Prime] : (coefficients p n).Nodup :=
  (coefficients_perm p n).nodup_iff.mpr
    (SubexpVectorEnumeration.vectors_nodup _
      (List.nodup_reverse.mpr (SubexpVectorEnumeration.elements_nodup p)) n)

theorem mem_coefficients (p n : ℕ) [Fact p.Prime] (v : Fin n → ZMod p) :
    v ∈ coefficients p n := by
  apply (coefficients_perm p n).mem_iff.mpr
  exact QuarticSearch.mem_vectors _ (fun a => by
    simpa [alphabet] using QuarticSearch.mem_elements p a) n v

theorem coefficients_length (p n : ℕ) [Fact p.Prime] :
    (coefficients p n).length = p ^ n := by
  simp [coefficients, coefficientRows, tokens, alphabet, TupleProgram.generated_count]

def bank (p : ℕ) [Fact p.Prime] {m n : ℕ} (M : Fin m → Fin n → ZMod p)
    (v : Fin n → ZMod p) : List Bool :=
  (vectorWords p (BlockSearch.matrixMap M v)).flatten

def bankRecords (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) : List (List Bool) :=
  ((coefficients p n).map (bank p M)).reverse

theorem bank_length (p : ℕ) [Fact p.Prime] {m n : ℕ} (M : Fin m → Fin n → ZMod p)
    (v : Fin n → ZMod p) : (bank p M v).length = m * width p := by
  simp [bank, vectorWords, List.length_flatten, List.map_ofFn, Function.comp_def]

def stored (p : ℕ) [Fact p.Prime] {m n : ℕ} (M : Fin m → Fin n → ZMod p)
    (regs : Fin 13 → Bool) (source payload output : List Bool) : Data :=
  ⟨regs, fun j => if j = 5 then modulus p else if j = 14 then zero p
    else if j = 16 then matrixBits p M else if j = 17 then List.replicate m true
    else if j = 18 then ProgramEncoding.encodeRecords (tokens p)
    else if j = 19 then List.replicate n true else if j = 20 then source
    else if j = 21 then payload else if j = 22 then output else []⟩

def ports : RecordPrograms.Ports 13 32 :=
  ⟨10, 11, 12, 20, 21, by decide, by decide, by decide, by decide⟩

abbrev copy (src dst : Fin 32) : Cmd 13 32 :=
  .call (StackRoutines.copyProgram src dst 23 0 1)
abbrev transfer (src dst : Fin 32) : Cmd 13 32 :=
  .call (StackRoutines.transferProgram src dst 0 1)
abbrev clear (src : Fin 32) : Cmd 13 32 :=
  .call (StackRoutines.clearProgram src 0 1)

def matrixRegs : Fin 8 → Fin 13 := Fin.castAdd 5
def matrixStacks : Fin 16 → Fin 32 := Fin.castAdd 16

theorem matrixRegs_injective : Function.Injective matrixRegs := Fin.castAdd_injective _ _
theorem matrixStacks_injective : Function.Injective matrixStacks := Fin.castAdd_injective _ _

def matrixView (d : Data) : State 8 16 :=
  ⟨d.regs ∘ matrixRegs, d.stacks ∘ matrixStacks⟩

def withMatrix (d : Data) (small : State 8 16) : Data :=
  ⟨Fin.addCases (m := 8) (n := 5) small.regs (fun i => d.regs (Fin.natAdd 8 i)),
    Fin.addCases (m := 16) (n := 16) small.stacks (fun i => d.stacks (Fin.natAdd 16 i))⟩

theorem embed_matrix (d : Data) (small : State 8 16) :
    embedState matrixRegs matrixStacks d small = withMatrix d small := by
  apply embedState_eq _ _ matrixRegs_injective matrixStacks_injective
  · intro i; simp [withMatrix, matrixRegs]
  · intro i; simp [withMatrix, matrixStacks]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 8) (n := 5) (fun i => ?_) (fun i => ?_) j
    · intro hi; exact (hi ⟨i, rfl⟩).elim
    · intro _
      simp [withMatrix]
      congr 1
      apply Fin.ext
      simp
  · intro j hj
    revert hj
    refine Fin.addCases (m := 16) (n := 16) (fun i => ?_) (fun i => ?_) j
    · intro hi; exact (hi ⟨i, rfl⟩).elim
    · intro _; simp [withMatrix]

theorem withMatrix_view (d : Data) : withMatrix d (matrixView d) = d := by
  apply state_ext
  · funext j
    refine Fin.addCases (m := 8) (n := 5) (fun i => ?_) (fun i => ?_) j
    · simp [withMatrix, matrixView, Function.comp_def, matrixRegs]
    · simp [withMatrix, matrixView, Function.comp_def, matrixRegs]
      congr 1
      apply Fin.ext
      simp
  · funext j
    refine Fin.addCases (m := 16) (n := 16) (fun i => ?_) (fun i => ?_) j <;>
      simp [withMatrix, matrixView, Function.comp_def, matrixStacks]

abbrev matrix : Cmd 13 32 := .call
  (ProgramLinking.liftProgram MatrixVectorProgram.matrixProgram matrixRegs matrixStacks)

theorem matrix_eval (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (v : Fin n → ZMod p) (d : Data)
    (hin : matrixView d = MatrixScalarProgram.state (d.regs ∘ matrixRegs)
      [] [] (modulus p) [] [] (matrixBits p M)
      (MatrixProgramSupport.words (vectorWords p v)) [] (zero p) (List.replicate m true)) :
    ∃ t ≤ MatrixVectorProgram.matrixBudget m n (width p), ∃ regs,
      Eval matrix t d (withMatrix d (MatrixScalarProgram.state regs [] [] (modulus p)
        (MatrixProgramSupport.words (vectorWords p (BlockSearch.matrixMap M v)))
        [] [] (MatrixProgramSupport.words (vectorWords p v)) [] (zero p) [])) := by
  obtain ⟨t, ht, regs, results, he, hr⟩ := MatrixVectorProgram.matrix_trace
    (vectorWords p v) (matrixRows p M) (width p) (modulus p) (zero p)
    (vectorWords_width p v) (by simpa only [vectorWords_length] using matrixRows_shape p M)
    (zero_length p) (zero_value p) (by simp) (modulus_positive p)
    (by simpa only [modulus_value] using modulus_capacity p) (d.regs ∘ matrixRegs) []
  simp only [modulus_value] at hr
  have hout := MatrixProgramSemantics.matrix_result_words p M v results hr
  change results = vectorWords p (BlockSearch.matrixMap M v) at hout
  rw [hout] at he
  have hi : MatrixScalarProgram.state (d.regs ∘ matrixRegs) [] [] (modulus p) [] []
      (MatrixVectorProgram.matrixWords (matrixRows p M) ++ [])
      (MatrixProgramSupport.words (vectorWords p v)) [] (zero p)
      (List.replicate (matrixRows p M).length true) = matrixView d := by
    rw [hin]
    simp only [MatrixVectorProgram.matrixWords_eq_words_flatten, List.append_nil,
      matrixRows_length, matrixBits]
  rw [hi] at he
  have hc := eval_call_lifted MatrixVectorProgram.matrixProgram matrixRegs matrixStacks d
    matrixRegs_injective matrixStacks_injective he
  rw [embed_matrix, withMatrix_view, embed_matrix] at hc
  exact ⟨t, by simpa only [matrixRows_length, vectorWords_length] using ht, regs, hc⟩

def bankRegs : Fin 3 → Fin 13 := Fin.castAdd 10
def bankStacks : Fin 4 → Fin 32 := ![8, 0, 10, 15]
theorem bankRegs_injective : Function.Injective bankRegs := Fin.castAdd_injective _ _
theorem bankStacks_injective : Function.Injective bankStacks := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [bankStacks]

abbrev flatten : Cmd 13 32 := .call
  (ProgramLinking.liftProgram ScalarBankProgram.program bankRegs bankStacks)

def flattened (d : Data) (bits : List Bool) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false,
    Function.update (Function.update (Function.update (Function.update d.stacks
      8 []) 0 []) 10 bits) 15 []⟩

theorem flatten_eval (d : Data) (rows : List (List Bool))
    (hs : d.stacks 8 = MatrixProgramSupport.words rows)
    (ha : d.stacks 0 = []) (ho : d.stacks 10 = [])
    (hc : d.stacks 15 = List.replicate rows.length true) :
    Eval flatten (9 * (rows.map List.length).sum + 6 * rows.length + 7)
      d (flattened d rows.flatten) := by
  let a := ScalarBankProgram.data (d.regs 0) (d.regs 1) (d.regs 2)
    (MatrixProgramSupport.words rows ++ []) [] [] (List.replicate rows.length true)
  let b := ScalarBankProgram.data false false false [] [] (rows.flatten ++ []) []
  have hin : embedState bankRegs bankStacks d a = d := by
    apply embedState_eq _ _ bankRegs_injective bankStacks_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> simp [a, bankStacks, ScalarBankProgram.data, hs, ha, ho, hc]
    · intros; rfl
    · intros; rfl
  have hout : embedState bankRegs bankStacks d b = flattened d rows.flatten := by
    apply embedState_eq _ _ bankRegs_injective bankStacks_injective
    · intro i; fin_cases i <;> simp [b, bankRegs, ScalarBankProgram.data, flattened]
    · intro i; fin_cases i <;> simp [b, bankStacks, ScalarBankProgram.data, flattened]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [bankRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [bankRegs] using h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, by simpa [bankRegs] using h.symm⟩
      simp [flattened, h0, h1, h2]
    · intro j hj
      have h8 : j ≠ 8 := fun h => hj ⟨0, by simpa [bankStacks] using h.symm⟩
      have h0 : j ≠ 0 := fun h => hj ⟨1, by simpa [bankStacks] using h.symm⟩
      have h10 : j ≠ 10 := fun h => hj ⟨2, by simpa [bankStacks] using h.symm⟩
      have h15 : j ≠ 15 := fun h => hj ⟨3, by simpa [bankStacks] using h.symm⟩
      simp [flattened, h8, h0, h10, h15]
  have he := eval_call_lifted ScalarBankProgram.program bankRegs bankStacks d
    bankRegs_injective bankStacks_injective
    (ScalarBankProgram.program_trace (d.regs 0) (d.regs 1) (d.regs 2) rows [] [])
  change Eval flatten (9 * (rows.map List.length).sum + 6 * rows.length + 7)
    (embedState bankRegs bankStacks d a) (embedState bankRegs bankStacks d b) at he
  rw [hin, hout] at he
  exact he

def emitPorts : RecordPrograms.Ports 13 32 :=
  ⟨0, 1, 2, 24, 22, by decide, by decide, by decide, by decide⟩
abbrev emit : Cmd 13 32 := .seq (transfer 10 24)
  (.seq (TupleProgram.pushConst 22 0 false)
    (.seq (TupleProgram.escape emitPorts) (TupleProgram.pushConst 22 0 true)))

def emitted (d : Data) : Data :=
  ⟨Function.update (readRegs d.regs 0 1 none) 0 true,
    Function.update (Function.update d.stacks 10 []) 22
      (TupleProgram.prependRecord (d.stacks 10) (d.stacks 22))⟩

theorem emit_eval (d : Data) (ht : d.stacks 24 = []) :
    Eval emit (8 * (d.stacks 10).length + 10) d (emitted d) := by
  let a := afterTransfer d 10 24 0 1
  let b := TupleProgram.pushedState 22 0 false a
  let c := TupleProgram.escapedState emitPorts b
  let e := TupleProgram.pushedState 22 0 true c
  have h1 := SubexpScanPrimitives.transfer_eval d 10 24 0 1 (by decide) (by decide)
  have h2 := TupleProgram.pushConst_eval 22 (0 : Fin 13) false a
  have h3 := TupleProgram.escape_eval_state emitPorts b
  have h4 := TupleProgram.pushConst_eval 22 (0 : Fin 13) true c
  have hb : b.stacks 24 = (d.stacks 10).reverse := by
    simp [b, a, afterTransfer, StackRoutines.transferStacks, ht]
  have he : e = emitted d := by
    apply state_ext
    · funext j
      by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> subst_vars <;>
        simp_all [e, c, b, a, emitted, TupleProgram.pushedState, TupleProgram.escapedState,
          emitPorts, afterTransfer, readRegs]
    · funext j
      by_cases h10 : j = 10 <;> by_cases h22 : j = 22 <;> by_cases h24 : j = 24 <;>
        subst_vars <;>
        simp_all [e, c, b, a, emitted, TupleProgram.pushedState, TupleProgram.escapedState,
          emitPorts, afterTransfer, StackRoutines.transferStacks, TupleProgram.prependRecord,
          TupleProgram.frame_eq_escaped, List.append_assoc]
  change Eval (TupleProgram.pushConst 22 0 true) 2 c e at h4
  rw [he] at h4
  have hall := h1.seq (h2.seq (h3.seq h4))
  convert hall using 1
  all_goals simp only [emitPorts, hb, List.length_reverse]
  all_goals omega

end SubexponentialSAT.Subexp.MatrixImageEnumeration

end OAI.Algorithms
