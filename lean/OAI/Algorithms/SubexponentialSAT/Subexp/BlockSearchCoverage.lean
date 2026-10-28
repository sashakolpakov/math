import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPredicate
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchOuter
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchCost

namespace OAI.Algorithms

/-! Coverage and algebraic soundness of the actual generated search lists. -/

namespace SubexponentialSAT.Subexp.BlockSearchCoverage

open BitProgram StructuredCalls BlockSearch BlockSearchEncoding BlockSearchPredicate
open SubexpTupleRefinement BlockSearchLoop BlockSearchOuter

variable {K : Type*} [Field K] [DecidableEq K]

def tables (code : StackEncoding.BlockCode K) (alphabet : List K) (N : ℕ) :=
  TupleProgram.powerRows (alphabet.map code.block) (N * N) [[]]

def coefficients (code : StackEncoding.BlockCode K) (alphabet : List K) (N : ℕ) :=
  TupleProgram.powerRows (alphabet.map code.block) N [[]]

def dimensions (N : ℕ) := DimensionProgram.dimensionRows 0 N

def ValidTable (code : StackEncoding.BlockCode K) (N : ℕ) (bits : List Bool) : Prop :=
  ∃ C : Fin N → Fin N → K, bits = encodeTuple code (flattenTable C)

def ValidCoefficient (code : StackEncoding.BlockCode K) (N : ℕ) (bits : List Bool) : Prop :=
  ∃ x : Fin N → K, bits = encodeTuple code x

def ValidSplit (N : ℕ) (bits : List Bool) : Prop :=
  ∃ d : Fin (N + 1), bits = splitCode d

omit [Field K] [DecidableEq K] in
theorem valid_table (code : StackEncoding.BlockCode K) (alphabet : List K) (N : ℕ)
    (bits : List Bool) (h : bits ∈ tables code alphabet N) : ValidTable code N bits := by
  obtain ⟨x, hx, he⟩ := (mem_powerRows_encoded code alphabet (N * N) bits).mp h
  exact ⟨unflattenTable x, by simpa using he.symm⟩

omit [Field K] [DecidableEq K] in
theorem valid_coefficient (code : StackEncoding.BlockCode K) (alphabet : List K) (N : ℕ)
    (bits : List Bool) (h : bits ∈ coefficients code alphabet N) : ValidCoefficient code N bits := by
  obtain ⟨x, hx, he⟩ := (mem_powerRows_encoded code alphabet N bits).mp h
  exact ⟨x, he.symm⟩

theorem dimension_payload (k n : ℕ) (bits : List Bool)
    (h : bits ∈ DimensionProgram.dimensionRows k n) :
    ∃ d, k ≤ d ∧ d ≤ k + n ∧ bits = List.replicate d true := by
  induction n generalizing k bits with
  | zero =>
      have he : bits = List.replicate k true := by simpa [DimensionProgram.dimensionRows] using h
      exact ⟨k, le_rfl, by omega, he⟩
  | succ n ih =>
      simp only [DimensionProgram.dimensionRows, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · obtain ⟨d, hl, hu, he⟩ := ih (k + 1) bits h
        exact ⟨d, by omega, by omega, he⟩
      · exact ⟨k, le_rfl, by omega, h⟩

theorem valid_split (N : ℕ) (bits : List Bool) (h : bits ∈ dimensions N) :
    ValidSplit N bits := by
  obtain ⟨d, hl, hu, he⟩ := dimension_payload 0 N bits h
  exact ⟨⟨d, by omega⟩, he⟩

theorem valid_split_reverse (N : ℕ) (bits : List Bool) (h : ValidSplit N bits) :
    bits.reverse = bits := by
  obtain ⟨d, rfl⟩ := h
  simp [splitCode]

theorem valid_split_length (N : ℕ) (bits : List Bool) (h : ValidSplit N bits) :
    bits.length ≤ N := by
  obtain ⟨d, rfl⟩ := h
  simp only [splitCode, List.length_replicate]
  have := d.isLt
  omega

omit [Field K] [DecidableEq K] in
theorem valid_table_length (code : StackEncoding.BlockCode K) (N : ℕ)
    (bits : List Bool) (h : ValidTable code N bits) : bits.length = N * N * code.width := by
  obtain ⟨C, rfl⟩ := h
  simp [encodeTuple, StackEncoding.length_encodeDataStack]

omit [Field K] [DecidableEq K] in
theorem valid_coefficient_length (code : StackEncoding.BlockCode K) (N : ℕ)
    (bits : List Bool) (h : ValidCoefficient code N bits) : bits.length = N * code.width := by
  obtain ⟨x, rfl⟩ := h
  simp [encodeTuple, StackEncoding.length_encodeDataStack]

omit [Field K] [DecidableEq K] in
theorem coefficients_eq (code : StackEncoding.BlockCode K) (alphabet : List K) {N : ℕ}
    (d : Fin (N + 1)) (C : Fin N → Fin N → K) :
    BlockSearchProgram.coefficientRecords code alphabet (splitPair d C) =
      coefficients code alphabet N := by
  simp only [BlockSearchProgram.coefficientRecords, splitPair_dimensions_add, coefficients]

theorem generated_success (code : StackEncoding.BlockCode K) (alphabet : List K)
    (hfull : ∀ x, x ∈ alphabet) {m N : ℕ} (M : Fin m → Fin N → K) :
    (tables code alphabet N).any
      (tableTest (coefficients code alphabet N) (dimensions N) (encodedTest code alphabet M)) = true := by
  obtain ⟨d, C, ht, hd, hp⟩ := exists_encoded_success code alphabet hfull M
  apply List.any_eq_true.mpr
  refine ⟨encodeTuple code (flattenTable C), ht, ?_⟩
  apply List.any_eq_true.mpr
  exact ⟨splitCode d, hd, by simpa only [coefficients_eq] using hp⟩

theorem selected_good (code : StackEncoding.BlockCode K) (alphabet : List K)
    (hfull : ∀ x, x ∈ alphabet) {m N : ℕ} (M : Fin m → Fin N → K)
    (table split : List Bool) (ht : table ∈ tables code alphabet N)
    (hd : split ∈ dimensions N)
    (hgood : (coefficients code alphabet N).all (encodedTest code alphabet M table split) = true) :
    ∃ (C : Fin N → Fin N → K) (d : Fin (N + 1)), GoodPair M (splitPair d C) ∧
      table = encodeTuple code (flattenTable C) ∧ split = splitCode d := by
  obtain ⟨C, rfl⟩ := valid_table code alphabet N table ht
  obtain ⟨d, rfl⟩ := valid_split N split hd
  refine ⟨C, d, ?_, rfl, rfl⟩
  apply (all_encoded_iff_goodPair code alphabet hfull M d C).mp
  simpa only [coefficients_eq] using hgood

omit [Field K] [DecidableEq K] in
theorem list_lengths (code : StackEncoding.BlockCode K) (alphabet : List K) (N : ℕ) :
    (tables code alphabet N).length = alphabet.length ^ (N * N) ∧
    (coefficients code alphabet N).length = alphabet.length ^ N ∧
    (dimensions N).length = N + 1 := by
  simp [tables, coefficients, dimensions, TupleProgram.powerRows_length,
    DimensionProgram.dimensionRows_length]

/-- The checked nested loop returns an actual basis/complement encoding once
its concrete arithmetic callback meets the execution contract. -/
theorem program_runsIn (matrixPair : Cmd 24 42) (ctx : Context)
    (code : StackEncoding.BlockCode K) (alphabet : List K) (hfull : ∀ x, x ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) (bound : ℕ)
    (contract : ∀ (C : Fin N → Fin N → K) (d : Fin (N + 1)),
      CoefficientContract matrixPair ctx (encodeTuple code (flattenTable C)) (splitCode d)
        (encodedTest code alphabet M (encodeTuple code (flattenTable C)) (splitCode d))
        (fun _ => bound) (ValidCoefficient code N))
    (base : StructuredProgram.State 24 42)
    (hb : TableEntry ctx (coefficients code alphabet N) (dimensions N) N (N * N * code.width) base)
    (h0 : base.stacks 0 = ProgramEncoding.encodeRecords (tables code alphabet N))
    (h2 : base.stacks 2 = []) :
    ∃ (next : StructuredProgram.State 24 42) (C : Fin N → Fin N → K) (d : Fin (N + 1)),
      GoodPair M (splitPair d C) ∧ next.stacks 41 = encodeTuple code (flattenTable C) ∧
      next.stacks 8 = splitCode d ∧
      RunsIn (program matrixPair)
        (alphabet.length ^ (N * N) * ((N + 1) *
          (alphabet.length ^ N * (24 * (N * code.width) + bound + 27) + 35 * N + 62) +
          15 * (N * N * code.width) + 41) + 9)
        (base.withPC (some (program matrixPair).entry)) (next.withPC none) := by
  have hc : ∀ table, ValidTable code N table → ∀ split, ValidSplit N split →
      CoefficientContract matrixPair ctx table split (encodedTest code alphabet M table split)
        (fun _ => bound) (ValidCoefficient code N) := by
    rintro table ⟨C, rfl⟩ split ⟨d, rfl⟩
    exact contract C d
  obtain ⟨n, next, hn, hselected, hempty, hfound, heval⟩ :=
    BlockSearchOuter.command_eval matrixPair ctx (coefficients code alphabet N) (dimensions N)
      (tables code alphabet N) N (N * N * code.width) (encodedTest code alphabet M)
      (fun _ _ _ => bound) (ValidTable code N) (ValidSplit N) (ValidCoefficient code N)
      (fun bits h => (valid_table_length code N bits h).le)
      (valid_split_reverse N) (valid_split_length N)
      (valid_coefficient code alphabet N) (valid_split N) (valid_table code alphabet N)
      hc (generated_success code alphabet hfull M) base hb h0 h2
  obtain ⟨table, ht, split, hd, hgood, hout, hsplit⟩ := hselected
  obtain ⟨C, d, hpair, heC, hed⟩ := selected_good code alphabet hfull M table split ht hd hgood
  refine ⟨next, C, d, hpair, hout.trans heC, hsplit.trans hed, n + 1, ?_,
    StructuredCalls.compiled_halt_trace heval 0 41⟩
  have hcap := BlockSearchCost.searchCost_le N (N * N * code.width) (N * code.width) bound
    (fun _ _ _ => bound) (coefficients code alphabet N) (dimensions N) (tables code alphabet N)
    (fun bits h => (valid_table_length code N bits (valid_table code alphabet N bits h)).le)
    (fun bits h => valid_split_length N bits (valid_split N bits h))
    (fun bits h => (valid_coefficient_length code N bits (valid_coefficient code alphabet N bits h)).le)
    (fun _ _ _ _ _ _ => le_rfl)
  rcases list_lengths code alphabet N with ⟨htlen, hclen, hdlen⟩
  rw [htlen, hclen, hdlen] at hcap
  omega

end SubexponentialSAT.Subexp.BlockSearchCoverage

end OAI.Algorithms
