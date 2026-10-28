import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerInputBounds
import OAI.Algorithms.SubexponentialSAT.DyadicMaskedSearchBounds

namespace OAI.Algorithms

/-!
# Actual encoded callback inputs for the dyadic schedule

Every length hypothesis concerns the stored bits. The canonical-word
specializations derive those hypotheses from the actual `Nat.bits` and
unary literal encoders; no decoded value bounds an arbitrary padded word.
-/

namespace SubexponentialSAT.DyadicCallbackInputs

open CandidatePrepareProgram ExecSunflowerCallbackBounds
open DyadicMaskedSearchBounds

theorem formulaCode_length_le (F : Formula) (n m k : ℕ)
    (hcount : F.length ≤ m) (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hliteral : ∀ C ∈ F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1) :
    (formulaCode F).length ≤ 1 + (2 * (1 + (4 * n + 4) * k) + 2) * m := by
  have hclause : ∀ C ∈ F, (clauseCode C).length ≤ 1 + (4 * n + 4) * k := by
    intro C hC
    have h := Encoding.length_encodeList_upper id C (2 * n + 1) (hliteral C hC)
    calc
      (clauseCode C).length ≤ 1 + (2 * (2 * n + 1) + 2) * C.length := h
      _ ≤ 1 + (2 * (2 * n + 1) + 2) * k :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ (hwidth C hC)) 1
      _ = _ := by ring
  exact (Encoding.length_encodeList_upper clauseCode F _ hclause).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hcount) 1)

theorem aggregate_le_localSize_cube (F : Formula) (n m r k w : ℕ)
    (limit width size : List Bool)
    (hcount : F.length ≤ m) (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hliteral : ∀ C ∈ F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1)
    (hw : w ≤ m + 1) (hlimit : limit.length ≤ m + 1)
    (hwidthBits : width.length ≤ k + 1) (hsize : size.length ≤ r + 1) :
    aggregate F k r w limit width size ≤ 24 * localSize n m r k ^ 3 := by
  let L := localSize n m r k
  have hL : 1 ≤ L := by dsimp [L, localSize]; omega
  have hn : n + 1 ≤ L := by dsimp [L, localSize]; omega
  have hm : m ≤ L := by dsimp [L, localSize]; omega
  have hk : k ≤ L := by dsimp [L, localSize]; omega
  have hr : r ≤ L := by dsimp [L, localSize]; omega
  have hm1 : m + 1 ≤ L := by dsimp [L, localSize]; omega
  have hk1 : k + 1 ≤ L := by dsimp [L, localSize]; omega
  have hr1 : r + 1 ≤ L := by dsimp [L, localSize]; omega
  have hprod : (n + 1) * k * m ≤ L ^ 3 := by
    simpa only [pow_succ, pow_zero, Nat.one_mul] using
      Nat.mul_le_mul (Nat.mul_le_mul hn hk) hm
  have hL3 : L ≤ L ^ 3 := by
    simpa using Nat.pow_le_pow_right hL (show 1 ≤ 3 by decide)
  have hformula := formulaCode_length_le F n m k hcount hwidth hliteral
  have hformula' : (formulaCode F).length ≤ 1 + 4 * m + 8 * ((n + 1) * k * m) := by
    convert hformula using 1 ; ring
  change (formulaCode F).length + k + r + w + limit.length + width.length + size.length + 1 ≤
    24 * L ^ 3
  have hwb := hw.trans hm1
  have hlb := hlimit.trans hm1
  have hdb := hwidthBits.trans hk1
  have hsb := hsize.trans hr1
  omega

theorem aggregate_canonical_le (F : Formula) (n m r k j : ℕ)
    (hcount : F.length ≤ m) (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hliteral : ∀ C ∈ F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1) (hj : j ≤ k) :
    aggregate F k r (DyadicWidth.width m) m.bits j.bits r.bits ≤
      24 * localSize n m r k ^ 3 := by
  apply aggregate_le_localSize_cube F n m r k (DyadicWidth.width m) m.bits j.bits r.bits
    hcount hwidth hliteral (DyadicWidth.width_le_succ m)
  · exact (SparsificationBudgetProgram.bits_length_le m).trans (Nat.le_succ m)
  · exact (SparsificationBudgetProgram.bits_length_le j).trans (hj.trans (Nat.le_succ k))
  · exact (SparsificationBudgetProgram.bits_length_le r).trans (Nat.le_succ r)

/-- The executed threshold bank may retain arithmetic padding. Its actual
length is bounded explicitly instead of identifying its bytes with `r.bits`. -/
theorem aggregate_threshold_le (F : Formula) (n m r k w A : ℕ)
    (limit width size : List Bool)
    (hcount : F.length ≤ m) (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hliteral : ∀ C ∈ F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1)
    (hw : w ≤ m + 1) (hlimit : limit.length ≤ m + 1)
    (hwidthBits : width.length ≤ k + 1)
    (hsize : size.length ≤ A * localSize n m r k) :
    aggregate F k r w limit width size ≤ (A + 24) * localSize n m r k ^ 3 := by
  have hempty := aggregate_le_localSize_cube F n m r k w limit width []
    hcount hwidth hliteral hw hlimit hwidthBits (by simp)
  have hL : 1 ≤ localSize n m r k := by unfold localSize; omega
  have hL3 : localSize n m r k ≤ localSize n m r k ^ 3 := by
    simpa using Nat.pow_le_pow_right hL (show 1 ≤ 3 by decide)
  have hs := hsize.trans (Nat.mul_le_mul_left A hL3)
  have heq : aggregate F k r w limit width size =
      aggregate F k r w limit width [] + size.length := by simp [aggregate]; omega
  rw [heq]
  calc
    _ ≤ 24 * localSize n m r k ^ 3 + A * localSize n m r k ^ 3 := Nat.add_le_add hempty hs
    _ = _ := by ring

/-- The literal representation used by the executable finite-CNF layer. -/
def encodedLiterals {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) : Formula :=
  F.map (List.map (fun l => Encoding.encodeNat (Encoding.literalCode l)))

theorem encodedLiterals_length {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    (encodedLiterals F).length = F.length := by simp [encodedLiterals]

theorem encodedLiterals_width {n k : ℕ} (F : List (List (SAT.Literal (Fin n))))
    (hwidth : ∀ C ∈ F, C.length ≤ k) :
    ∀ C ∈ encodedLiterals F, C.length ≤ k := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
  simpa using hwidth D hD

theorem encodedLiterals_bits {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    ∀ C ∈ encodedLiterals F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1 := by
  intro C hC bits hb
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hb
  rw [Encoding.length_encodeNat]
  exact Nat.add_le_add_right (Nat.le_of_lt (Encoding.literalCode_lt l)) 1

theorem encodedLiterals_aggregate_le {n : ℕ}
    (F : List (List (SAT.Literal (Fin n)))) (m r k j : ℕ)
    (hcount : F.length ≤ m) (hwidth : ∀ C ∈ F, C.length ≤ k) (hj : j ≤ k) :
    aggregate (encodedLiterals F) k r (DyadicWidth.width m) m.bits j.bits r.bits ≤
      24 * localSize n m r k ^ 3 := by
  exact aggregate_canonical_le (encodedLiterals F) n m r k j
    (by simpa [encodedLiterals] using hcount) (encodedLiterals_width F hwidth)
    (encodedLiterals_bits F) hj

end SubexponentialSAT.DyadicCallbackInputs

end OAI.Algorithms
