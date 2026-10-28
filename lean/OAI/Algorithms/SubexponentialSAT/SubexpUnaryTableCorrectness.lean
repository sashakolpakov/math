import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryFactorTable

namespace OAI.Algorithms

/-! The actual table's row order and its connection to packed unary factors. -/

namespace SubexponentialSAT.SubexpUnaryTableCorrectness

open SubexpUnaryFactorTable SubexpUnaryRowProgram

theorem width_le_word_length (modulus : List Bool) (width : ℕ)
    (hcapacity : 2 ^ width ≤ CounterPrograms.value modulus) : width ≤ modulus.length := by
  have hp : CounterPrograms.value modulus < 2 ^ modulus.length := by
    rw [CounterPrograms.value_eq_toNat]
    exact SubexpFactorProgram.toNat_lt_pow_length modulus
  by_contra h
  have hle : modulus.length ≤ width := by omega
  have hpow := Nat.pow_le_pow_right (n := 2) (by decide) hle
  omega

/-- Row position zero holds rank `p - 1`; the final position holds rank zero. -/
theorem table_getElem (width p i : ℕ) (hi : i < p) :
    (table width p)[i]'(by simpa using hi) = answer width (p - 1 - i) := by
  simp [table, SubexpUnaryRowEnumeration.rows, List.getElem_reverse]

theorem answer_matches_factor {V J : Type*} [DecidableEq V] [DecidableEq J]
    {b : J → ℕ} {p : ℕ} [NeZero p]
    (positions : V ≃ (j : J) × Fin (b j)) (capacity : ∀ j, 2 ^ b j ≤ p)
    (F : SAT.CNF V) (x : J → ZMod p) (j : J) :
    answer (b j) (x j).val =
      Factor.evalFactor (FactorReduction.primeLabelCNF positions capacity F) (.inl j) x := by
  apply Bool.eq_iff_iff.mpr
  simpa only [answer, decide_eq_true_eq] using
    (FactorReduction.primeLabelCNF_unary_iff positions capacity F x j).symm

/-- This theorem follows the machine's descending order without silently
permuting the raw table bytes. -/
theorem table_getElem_matches_factor {V J : Type*} [DecidableEq V] [DecidableEq J]
    {b : J → ℕ} {p : ℕ} [NeZero p]
    (positions : V ≃ (j : J) × Fin (b j)) (capacity : ∀ j, 2 ^ b j ≤ p)
    (F : SAT.CNF V) (x : J → ZMod p) (j : J) (i : ℕ) (hi : i < p)
    (hx : (x j).val = p - 1 - i) :
    (table (b j) p)[i]'(by simpa using hi) =
      Factor.evalFactor (FactorReduction.primeLabelCNF positions capacity F) (.inl j) x := by
  rw [table_getElem (b j) p i hi, ← hx]
  exact answer_matches_factor positions capacity F x j

end SubexponentialSAT.SubexpUnaryTableCorrectness

end OAI.Algorithms
