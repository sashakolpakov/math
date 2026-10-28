import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgram

namespace OAI.Algorithms

/-! A fixed row controller for encoded matrix-vector multiplication. -/

namespace SubexponentialSAT.Subexp.MatrixVectorProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram MatrixProgram

abbrev row : Cmd 8 16 :=
  .seq (MatrixProgramSupport.copy 12 10 9)
    (.seq (MatrixProgramSupport.copy 14 8 9)
      (.seq (.call dotProgram)
        (.seq (emitFrame 8 0 9 (by decide)) (transfer 0 13))))

/-- One row is read from the right stream. The saved vector, zero word,
modulus, and outer-loop counter are preserved. Its framed result is emitted
in reverse on port 13 for a final linear-time reversal. -/
theorem row_eval (xs ys : List (List Bool)) (B : ℕ) (modulus zero : List Bool)
    (hlen : xs.length = ys.length)
    (hx : ∀ x ∈ xs, x.length = B) (hy : ∀ y ∈ ys, y.length = B)
    (hz : zero.length = B) (hzv : BinaryArithmetic.toNat zero = 0)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (right output count : List Bool) :
    ∃ n ≤ rowBudget xs.length B, ∃ regs' result,
      Eval row n
        (state regs [] [] modulus [] [] (words ys ++ right) (words xs) output zero count)
        (state regs' [] [] modulus [] [] right (words xs)
          ((Encoding.frame result).reverse ++ output) zero count) ∧
      result.length = B ∧ BinaryArithmetic.toNat result < BinaryArithmetic.toNat modulus ∧
      (BinaryArithmetic.toNat result : ZMod (BinaryArithmetic.toNat modulus)) = dotValue (BinaryArithmetic.toNat modulus) xs ys := by
  obtain ⟨d₁, h₁, hs₁⟩ := MatrixProgramSupport.copy_eval (12 : Fin 16) 10 9
    (by decide) (by decide) (by decide)
    (state regs [] [] modulus [] [] (words ys ++ right) (words xs) output zero count) rfl
  have hd₁ : d₁ = state d₁.regs [] [] modulus [] (words xs)
      (words ys ++ right) (words xs) output zero count := by
    apply data_ext <;> try rfl
    rw [hs₁]
    funext j
    fin_cases j <;> simp [ scalarStacks, StackRoutines.copyStacks]
  rw [hd₁] at h₁
  obtain ⟨d₂, h₂, hs₂⟩ := MatrixProgramSupport.copy_eval (14 : Fin 16) 8 9
    (by decide) (by decide) (by decide)
    (state d₁.regs [] [] modulus [] (words xs) (words ys ++ right) (words xs) output zero count) rfl
  have hd₂ : d₂ = state d₂.regs [] [] modulus zero (words xs)
      (words ys ++ right) (words xs) output zero count := by
    apply data_ext <;> try rfl
    rw [hs₂]
    funext j
    fin_cases j <;> simp [ scalarStacks, StackRoutines.copyStacks]
  rw [hd₂] at h₂
  obtain ⟨n₃, hn₃, r₃, result, h₃, hl₃, hc₃, hv₃⟩ :=
    dot_trace xs ys B modulus hlen hx hy hml hm hcap d₂.regs zero right
      (words xs) output zero count hz (by simpa only [hzv] using hm)
  have he₃ : Eval (.call dotProgram) n₃
      (state d₂.regs [] [] modulus zero (words xs) (words ys ++ right) (words xs) output zero count)
      (state r₃ [] [] modulus result [] right (words xs) output zero count) := .call _ h₃
  obtain ⟨d₄, h₄, hs₄⟩ := emitFrame_eval (8 : Fin 16) 0 9
    (by decide) (by decide) (by decide)
    (state r₃ [] [] modulus result [] right (words xs) output zero count) rfl
  have hd₄ : d₄ = state d₄.regs (Encoding.frame result) [] modulus [] []
      right (words xs) output zero count := by
    apply data_ext <;> try rfl
    rw [hs₄]
    funext j
    fin_cases j <;> simp [ scalarStacks]
  rw [hd₄] at h₄
  obtain ⟨d₅, h₅, hs₅⟩ := transfer_eval (0 : Fin 16) 13 (by decide)
    (state d₄.regs (Encoding.frame result) [] modulus [] [] right (words xs) output zero count)
  have hd₅ : d₅ = state d₅.regs [] [] modulus [] [] right (words xs)
      ((Encoding.frame result).reverse ++ output) zero count := by
    apply data_ext <;> try rfl
    rw [hs₅]
    funext j
    fin_cases j <;> simp [ scalarStacks, StackRoutines.transferStacks]
  rw [hd₅] at h₅
  have he := Eval.seq h₁ (Eval.seq h₂ (Eval.seq he₃ (Eval.seq h₄ h₅)))
  refine ⟨(7 * (xs.length * (2 * B + 1)) + 5) + (7 * B + 5 +
      (n₃ + (8 * B + 8 + (3 * (2 * B + 1) + 3)))), ?_, d₅.regs, result, ?_, hl₃, hc₃, ?_⟩
  · unfold rowBudget
    omega
  · simpa [row, state, scalarStacks, words_length xs B hx, hz, hl₃,
      Encoding.length_frame] using he
  · simpa only [hzv, Nat.cast_zero, add_zero] using hv₃

def matrixWords : List (List (List Bool)) → List Bool
  | [] => []
  | ys :: rows => words ys ++ matrixWords rows

theorem matrixWords_eq_words_flatten (rows : List (List (List Bool))) :
    matrixWords rows = words rows.flatten := by
  induction rows with
  | nil => rfl
  | cons ys rows ih => simp [matrixWords, List.flatten_cons, words_append, ih]

abbrev popRow : Cmd 8 16 := .base (.atom (.pop 15 0 1))
abbrev matrixBody : Cmd 8 16 := .seq row popRow
abbrev matrixLoop : Cmd 8 16 := .while 1 matrixBody
abbrev matrixCommand : Cmd 8 16 := .seq popRow (.seq matrixLoop (transfer 13 8))
def matrixProgram := compiled matrixCommand 11 8

theorem matrixProgram_labels : size matrixCommand + 1 = 359 := by decide

abbrev readyMatrix (regs : Fin 8 → Bool) (modulus : List Bool) (xs : List (List Bool))
    (right output zero : List Bool) (m : ℕ) : MatrixScalarProgram.Data :=
  state (readRegs regs 0 1 (List.replicate m true).head?) [] [] modulus [] [] right
    (words xs) output zero (List.replicate m true).tail

theorem popRow_eval (regs : Fin 8 → Bool) (modulus : List Bool) (xs : List (List Bool))
    (right output zero : List Bool) (m : ℕ) :
    Eval popRow 1
      (state regs [] [] modulus [] [] right (words xs) output zero (List.replicate m true))
      (readyMatrix regs modulus xs right output zero m) := by
  have hfinish : (StructuredProgram.Atom.pop (15 : Fin 16) (0 : Fin 8) 1).eval
      (state regs [] [] modulus [] [] right (words xs) output zero (List.replicate m true)) =
      readyMatrix regs modulus xs right output zero m := by
    apply MatrixProgramSupport.data_ext
    · simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, scalarStacks]
    · funext j
      fin_cases j <;>
        simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr, scalarStacks]
  rw [← hfinish]
  exact .base (.atom _ _)

theorem readyMatrix_zero (regs : Fin 8 → Bool) (modulus : List Bool) (xs : List (List Bool))
    (right output zero : List Bool) :
    (readyMatrix regs modulus xs right output zero 0).regs 1 = false := by
  simp [ readRegs]

theorem readyMatrix_succ (regs : Fin 8 → Bool) (modulus : List Bool) (xs : List (List Bool))
    (right output zero : List Bool) (m : ℕ) :
    (readyMatrix regs modulus xs right output zero (m + 1)).regs 1 = true := by
  simp [ readRegs, List.replicate_succ]

def RowResult (p B : ℕ) (xs ys : List (List Bool)) (z : List Bool) : Prop :=
  z.length = B ∧ BinaryArithmetic.toNat z < p ∧ (BinaryArithmetic.toNat z : ZMod p) = dotValue p xs ys

theorem result_widths {p B : ℕ} {xs : List (List Bool)}
    {rows : List (List (List Bool))} {zs : List (List Bool)}
    (h : List.Forall₂ (RowResult p B xs) rows zs) : ∀ z ∈ zs, z.length = B := by
  induction h with
  | nil => simp
  | cons hh ht ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hh.1
    · exact ih z hz

theorem result_canonical {p B : ℕ} {xs : List (List Bool)}
    {rows : List (List (List Bool))} {zs : List (List Bool)}
    (h : List.Forall₂ (RowResult p B xs) rows zs) : ∀ z ∈ zs, BinaryArithmetic.toNat z < p := by
  induction h with
  | nil => simp
  | cons hh ht ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hh.2.1
    · exact ih z hz

theorem matrixLoop_eval (xs : List (List Bool)) (rows : List (List (List Bool)))
    (B : ℕ) (modulus zero : List Bool)
    (hx : ∀ x ∈ xs, x.length = B)
    (hrows : ∀ ys ∈ rows, xs.length = ys.length ∧ ∀ y ∈ ys, y.length = B)
    (hz : zero.length = B) (hzv : BinaryArithmetic.toNat zero = 0)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (right output : List Bool) :
    ∃ n ≤ rows.length * (rowBudget xs.length B + 2) + 1, ∃ regs' results,
      Eval matrixLoop n
        (readyMatrix regs modulus xs (matrixWords rows ++ right) output zero rows.length)
        (state regs' [] [] modulus [] [] right (words xs)
          ((words results).reverse ++ output) zero []) ∧
      List.Forall₂ (RowResult (BinaryArithmetic.toNat modulus) B xs) rows results := by
  induction rows generalizing regs output with
  | nil =>
    refine ⟨1, by simp, (readyMatrix regs modulus xs right output zero 0).regs,
      [], ?_, .nil⟩
    simpa [matrixLoop, matrixWords, words, readyMatrix, state] using
      (Eval.while_false (test := (1 : Fin 8)) (body := matrixBody)
        (readyMatrix_zero regs modulus xs right output zero))
  | cons ys rows ih =>
    have hy := hrows ys (by simp)
    let rr := (readyMatrix regs modulus xs
      (matrixWords (ys :: rows) ++ right) output zero (ys :: rows).length).regs
    obtain ⟨nr, hnr, r₁, result, her, hlr, hcr, hvr⟩ := row_eval xs ys B modulus zero
      hy.1 hx hy.2 hz hzv hml hm hcap rr (matrixWords rows ++ right) output
      (List.replicate rows.length true)
    have hrow : Eval row nr
        (readyMatrix regs modulus xs (matrixWords (ys :: rows) ++ right) output zero
          (ys :: rows).length)
        (state r₁ [] [] modulus [] [] (matrixWords rows ++ right) (words xs)
          ((Encoding.frame result).reverse ++ output) zero (List.replicate rows.length true)) := by
      simpa only [rr, readyMatrix, matrixWords, List.length_cons, List.replicate_succ,
        List.tail_cons, List.append_assoc] using her
    have hp := popRow_eval r₁ modulus xs (matrixWords rows ++ right)
      ((Encoding.frame result).reverse ++ output) zero rows.length
    obtain ⟨nt, hnt, rf, results, het, hrel⟩ :=
      ih (fun row hr => hrows row (List.mem_cons_of_mem _ hr)) r₁
        ((Encoding.frame result).reverse ++ output)
    have he := Eval.while_true
      (readyMatrix_succ regs modulus xs (matrixWords (ys :: rows) ++ right)
        output zero rows.length) (Eval.seq hrow hp) het
    refine ⟨(nr + 1) + nt + 1, ?_, rf, result :: results, ?_, .cons ⟨hlr, hcr, hvr⟩ hrel⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · simpa only [matrixLoop, matrixBody, words, List.length_cons, Nat.add_comm,
        List.reverse_append, List.append_assoc] using he

/-- A whole matrix-vector product with actual framing, scalar arithmetic,
row iteration, and output reversal. The unary row count is runtime input;
empty rows and zero-column matrices are handled without an EOF assumption. -/
theorem matrix_trace (xs : List (List Bool)) (rows : List (List (List Bool)))
    (B : ℕ) (modulus zero : List Bool)
    (hx : ∀ x ∈ xs, x.length = B)
    (hrows : ∀ ys ∈ rows, xs.length = ys.length ∧ ∀ y ∈ ys, y.length = B)
    (hz : zero.length = B) (hzv : BinaryArithmetic.toNat zero = 0)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (right : List Bool) :
    ∃ n ≤ matrixBudget rows.length xs.length B, ∃ regs' results,
      Trace matrixProgram n
        ((state regs [] [] modulus [] [] (matrixWords rows ++ right) (words xs)
          [] zero (List.replicate rows.length true)).withPC (some matrixProgram.entry))
        ((state regs' [] [] modulus (words results) [] right (words xs) [] zero []).withPC none) ∧
      List.Forall₂ (RowResult (BinaryArithmetic.toNat modulus) B xs) rows results := by
  obtain ⟨n, hn, rf, results, he, hrel⟩ := matrixLoop_eval xs rows B modulus zero
    hx hrows hz hzv hml hm hcap regs right []
  have hp := popRow_eval regs modulus xs (matrixWords rows ++ right) [] zero rows.length
  have he' : Eval matrixLoop n
      (readyMatrix regs modulus xs (matrixWords rows ++ right) [] zero rows.length)
      (state rf [] [] modulus [] [] right (words xs) (words results).reverse zero []) := by
    simpa only [List.append_nil] using he
  obtain ⟨d, ht, hst⟩ := transfer_eval (13 : Fin 16) 8 (by decide)
    (state rf [] [] modulus [] [] right (words xs) (words results).reverse zero [])
  have hd : d = state d.regs [] [] modulus (words results) [] right (words xs) [] zero [] := by
    apply data_ext <;> try rfl
    rw [hst]
    funext j
    fin_cases j <;> simp [ scalarStacks, StackRoutines.transferStacks]
  rw [hd] at ht
  have hwidth : (words results).length = rows.length * (2 * B + 1) := by
    rw [words_length results B (result_widths hrel), ← hrel.length_eq]
  have hrun := compiled_halt_trace (Eval.seq hp (Eval.seq he' ht)) 11 8
  refine ⟨1 + (n + (3 * (rows.length * (2 * B + 1)) + 3)) + 1, ?_, d.regs, results, ?_, hrel⟩
  · unfold matrixBudget
    nlinarith only [hn]
  · simpa [matrixProgram, matrixCommand, state, scalarStacks, List.length_reverse, hwidth] using hrun

theorem matrix_primitive (xs : List (List Bool)) (rows : List (List (List Bool)))
    (B : ℕ) (modulus zero : List Bool)
    (hx : ∀ x ∈ xs, x.length = B)
    (hrows : ∀ ys ∈ rows, xs.length = ys.length ∧ ∀ y ∈ ys, y.length = B)
    (hz : zero.length = B) (hzv : BinaryArithmetic.toNat zero = 0)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (right : List Bool) :
    ∃ regs' results,
      Computation.RunsIn (BitProgram.primitive matrixProgram).step
        (BitProgram.primitiveOverhead matrixProgram * matrixBudget rows.length xs.length B)
        (BitProgram.primitiveCfg matrixProgram
          ((state regs [] [] modulus [] [] (matrixWords rows ++ right) (words xs)
            [] zero (List.replicate rows.length true)).withPC (some matrixProgram.entry)))
        (BitProgram.primitiveCfg matrixProgram
          ((state regs' [] [] modulus (words results) [] right (words xs) [] zero []).withPC none)) ∧
      List.Forall₂ (RowResult (BinaryArithmetic.toNat modulus) B xs) rows results := by
  obtain ⟨n, hn, rf, results, ht, hrel⟩ := matrix_trace xs rows B modulus zero hx hrows
    hz hzv hml hm hcap regs right
  exact ⟨rf, results, BitProgram.primitive_execution matrixProgram ⟨n, hn, ht⟩, hrel⟩

end SubexponentialSAT.Subexp.MatrixVectorProgram

end OAI.Algorithms
