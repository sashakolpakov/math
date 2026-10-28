import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrapPreparation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCost

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open SubexpEnumerationPayload

/-- An expanded bound uses only the audited generator estimate and fixed constants. -/
theorem cost_le (d : ℕ) : cost d ≤
    800 * (d + 1) * 3 ^ d * ((d + 1) * scalarWidth 3 + 1) +
    800 * ((d + 1) + (d + 1) + 1) * 3 ^ ((d + 1) + (d + 1)) *
      (((d + 1) + (d + 1) + 1) * scalarWidth 3 + 1) +
    28 * d + 4 * alphabetWord.length + 89 := by
  have h1 := IrreducibleSearchEnumeration.cost_le d
  have h2 := IrreducibleSearchEnumeration.cost_le ((d + 1) + (d + 1))
  dsimp only [cost]
  omega

def preparationConstant : ℕ := 200000

private theorem scalarWidth_three : scalarWidth 3 = 2 := by
  have h : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  simp only [scalarWidth, h]

private theorem alphabetWord_length_le : alphabetWord.length ≤ 19 := by
  have h := ProgramEncoding.encodeRecords_length_le IrreducibleSearchEnumeration.alphabet 2 (by
    intro row hrow
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hrow
    have hx' : ((scalarCode 3).block x).length = scalarWidth 3 :=
      (scalarCode 3).length_block x
    exact le_of_eq (hx'.trans scalarWidth_three))
  simpa only [alphabetWord, IrreducibleSearchEnumeration.alphabet_length] using h

private theorem coefficient_bound :
    800 * (scalarWidth 3 + 1) + 21600 * (3 * scalarWidth 3 + 1) +
      28 + 4 * alphabetWord.length + 89 ≤ preparationConstant := by
  have h := alphabetWord_length_le
  norm_num [scalarWidth_three, preparationConstant]
  omega

private theorem first_term_bound (d N W : ℕ) (hN : 1 ≤ N) (hdN : d + 1 ≤ N) :
    800 * (d + 1) * N * ((d + 1) * W + 1) ≤ (800 * (W + 1)) * N^4 := by
  have hN34 : N^3 ≤ N^4 := pow_le_pow_right₀ hN (by decide)
  calc
    _ ≤ 800 * N * N * (N * W + N) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right N (Nat.mul_le_mul_left 800 hdN))
        (Nat.add_le_add (Nat.mul_le_mul_right W hdN) hN)
    _ = (800 * (W + 1)) * N^3 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hN34

private theorem second_term_bound (d N W : ℕ) (hN : 1 ≤ N) (hdN : d + 1 ≤ N) :
    800 * ((d + 1) + (d + 1) + 1) * (9 * N^2) *
      (((d + 1) + (d + 1) + 1) * W + 1) ≤ (21600 * (3 * W + 1)) * N^4 := by
  have hfN : (d + 1) + (d + 1) + 1 ≤ 3 * N := by omega
  calc
    _ ≤ 800 * (3 * N) * (9 * N^2) * ((3 * N) * W + N) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 800 hfN))
        (Nat.add_le_add (Nat.mul_le_mul_right W hfN) hN)
    _ = _ := by ring

private theorem rest_bound (d N K : ℕ) (hN : 1 ≤ N) (hdN : d + 1 ≤ N) :
    28 * d + 4 * K + 89 ≤ (28 + 4 * K + 89) * N^4 := by
  have hN4 : N ≤ N^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hN (show 1 ≤ 4 by decide)
  have hd4 : d ≤ N^4 := (Nat.le_succ d).trans (hdN.trans hN4)
  have h14 : 1 ≤ N^4 := hN.trans hN4
  calc
    _ = 28 * d + (4 * K + 89) * 1 := by omega
    _ ≤ 28 * N^4 + (4 * K + 89) * N^4 :=
      Nat.add_le_add (Nat.mul_le_mul_left 28 hd4) (Nat.mul_le_mul_left _ h14)
    _ = _ := by simp only [add_mul, Nat.add_assoc]

private theorem terms_bound (d N W K : ℕ) (hN : 1 ≤ N) (hdN : d + 1 ≤ N) :
    800 * (d + 1) * N * ((d + 1) * W + 1) +
      800 * ((d + 1) + (d + 1) + 1) * (9 * N^2) *
        (((d + 1) + (d + 1) + 1) * W + 1) + 28 * d + 4 * K + 89 ≤
      (800 * (W + 1) + 21600 * (3 * W + 1) + 28 + 4 * K + 89) * N^4 := by
  have h := Nat.add_le_add (Nat.add_le_add (first_term_bound d N W hN hdN)
    (second_term_bound d N W hN hdN)) (rest_bound d N K hN hdN)
  simpa only [add_mul, Nat.add_assoc] using h

private theorem factor_power (d : ℕ) :
    3 ^ ((d + 1) + (d + 1)) = 9 * (3 ^ d)^2 := by
  rw [show (d + 1) + (d + 1) = d * 2 + 2 by omega, pow_add, pow_mul]
  norm_num [Nat.mul_comm]

theorem cost_cardinality (d : ℕ) : cost d ≤ preparationConstant * (3 ^ d)^4 := by
  have h := cost_le d
  rw [factor_power] at h
  have hb := h.trans (terms_bound d (3 ^ d) (scalarWidth 3) alphabetWord.length
    (Nat.one_le_pow _ _ (by decide)) (IrreducibleSearch.succ_le_three_pow d))
  exact hb.trans (Nat.mul_le_mul_right _ coefficient_bound)

/-- The implemented degree uses a quadratic field-size bound in `Q + 1`. -/
theorem cost_sizeDegreeBound {d Q : ℕ} (h : 3 ^ d ≤ 16 * (Q + 1)^2) :
    cost d ≤ (preparationConstant * 16^4) * (Q + 1)^8 := by
  calc
    cost d ≤ preparationConstant * (3 ^ d)^4 := cost_cardinality d
    _ ≤ preparationConstant * (16 * (Q + 1)^2)^4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 4)
    _ = _ := by
      rw [mul_pow, ← pow_mul]
      simp only [Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
