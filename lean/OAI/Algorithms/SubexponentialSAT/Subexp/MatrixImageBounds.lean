import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixImageEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreBounds

namespace OAI.Algorithms

/-! Output-sensitive bounds for the actual matrix-image enumerator. -/

namespace SubexponentialSAT.Subexp.MatrixImageEnumeration

open BitProgram MatrixWordEncoding BlockCoefficientProgram

theorem matrixBits_length (p : ℕ) {m n : ℕ} (M : Fin m → Fin n → ZMod p) :
    (matrixBits p M).length = m * n * (2 * width p + 1) := by
  have hw : ∀ word ∈ (matrixRows p M).flatten, word.length = width p := by
    intro word hword
    obtain ⟨row, hrow, hw⟩ := List.mem_flatten.mp hword
    exact (matrixRows_shape p M row hrow).2 word hw
  rw [matrixBits, MatrixProgramSupport.words_length _ (width p) hw]
  have hl : (matrixRows p M).flatten.length = m * n := by
    simp [matrixRows, vectorWords, List.length_flatten, List.map_ofFn, Function.comp_def]
  rw [hl]

theorem coefficientRows_length (p n : ℕ) [Fact p.Prime] :
    (coefficientRows p n).length = p ^ n := by
  simpa only [coefficients, List.length_map] using coefficients_length p n

theorem coefficientRows_payload_length (p n : ℕ) [Fact p.Prime]
    (bits : List Bool) (hbits : bits ∈ coefficientRows p n) :
    bits.length = n * (2 * width p + 1) := by
  rw [← coefficientRows_valid p n bits hbits]
  rw [MatrixProgramSupport.words_length _ (width p) (vectorWords_width p _), vectorWords_length]

def callbackPolynomial (m n B : ℕ) : ℕ :=
  (3 * (n * (2 * B + 1)) + 3) + (7 * (m * n * (2 * B + 1)) + 5) + (7 * m + 5) +
  MatrixVectorProgram.matrixBudget m n B + (7 * m + 5) +
  (9 * (m * B) + 6 * m + 7) + (2 * (n * (2 * B + 1)) + 3) +
  (8 * (m * B) + 10) + 3

theorem callbackBudget_eq (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (bits : List Bool)
    (hbits : bits ∈ coefficientRows p n) :
    callbackBudget p M bits = callbackPolynomial m n (width p) := by
  simp only [callbackBudget, callbackPolynomial, matrixBits_length,
    coefficientRows_payload_length p n bits hbits]

def workPolynomial (m n B : ℕ) : ℕ :=
  7 * n + 25 + 800 * (n + 1) * ((n + 1) * (2 * B + 1) + 1) +
    6 * (n * (2 * B + 1)) + callbackPolynomial m n B + 7

theorem sourceBudget_le_polynomial (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) :
    sourceBudget p M ≤ workPolynomial m n (width p) * p ^ n := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have ht : (tokens p).length = p := by simp [tokens, alphabet]
  have htokens : ∀ bits ∈ tokens p, bits.length ≤ 2 * width p + 1 := by
    intro bits hbits
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hbits
    simp [BlockSearchPredicate.scalarCode, BlockSearchProgram.framedCode,
      MatrixWordEncoding.code]
  have hgen := PairScoreBounds.generated_powerCost_le (tokens p) n (2 * width p + 1)
    (by simpa only [ht] using hp) htokens
  rw [ht] at hgen
  have hcallbacks := RecordPrograms.budget_le_linear (callbackBudget p M)
    (coefficientRows p n) 0 (callbackPolynomial m n (width p)) (by
      intro bits hbits
      simp only [Nat.zero_mul, Nat.zero_add, callbackBudget_eq p M bits hbits, le_refl])
  have hvolume : ((coefficientRows p n).map List.length).sum =
      p ^ n * (n * (2 * width p + 1)) := by
    have he : (coefficientRows p n).map List.length =
        (coefficientRows p n).map (fun _ => n * (2 * width p + 1)) := by
      apply List.map_congr_left
      exact coefficientRows_payload_length p n
    rw [he]
    simp [coefficientRows_length]
  rw [hvolume, coefficientRows_length] at hcallbacks
  have hinit : 7 * n + 25 ≤ (7 * n + 25) * p ^ n := by
    exact Nat.le_mul_of_pos_right _ (pow_pos (Fact.out : p.Prime).pos _)
  unfold sourceBudget workPolynomial
  nlinarith only [hgen, hcallbacks, hinit]

theorem workPolynomial_le (m n B : ℕ) :
    workPolynomial m n B ≤ 50000 * (m + 1) * (n + 1) ^ 2 * (B + 1) ^ 2 := by
  unfold workPolynomial callbackPolynomial MatrixVectorProgram.matrixBudget
    MatrixVectorProgram.rowBudget MatrixProgram.termBudget
  ring_nf
  omega

theorem sourceBudget_le (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) :
    sourceBudget p M ≤ 50000 * (m + 1) * (n + 1) ^ 2 * (width p + 1) ^ 2 * p ^ n :=
  (sourceBudget_le_polynomial p M).trans (Nat.mul_le_mul_right _ (workPolynomial_le _ _ _))

/-- Complete primitive-machine cost, including tuple generation, all matrix
calls, parsing, record framing, copies, and cleanup. -/
theorem primitive_run_bounded (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (regs : Fin 13 → Bool) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program *
        (50000 * (m + 1) * (n + 1) ^ 2 * (width p + 1) ^ 2 * p ^ n))
      (primitiveCfg program ((stored p M regs [] [] []).withPC (some program.entry)))
      (primitiveCfg program
        ((stored p M rf [] [] (ProgramEncoding.encodeRecords (bankRecords p M))).withPC none)) := by
  obtain ⟨rf, t, ht, he⟩ := program_run p M regs
  exact ⟨rf, primitive_execution program ⟨t, ht.trans (sourceBudget_le p M), he⟩⟩

end SubexponentialSAT.Subexp.MatrixImageEnumeration

end OAI.Algorithms
