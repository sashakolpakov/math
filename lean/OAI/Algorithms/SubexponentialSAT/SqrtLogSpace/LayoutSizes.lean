import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramMagnitudeOffset
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRankSignature
import Mathlib.Data.Nat.Size

/-! Retained full integer rows have polynomial binary length. Bounds on these
mathematical records are separate from native every-prefix storage proofs. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutSizes

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open LayoutPullback LayoutExactBuckets LayoutCoefficientAlgorithm

theorem natAbs_scalarSum_le (A R Q d h : ℕ) (hAQ : A ≤ Q)
    (hQ : 1 ≤ Q) (hh : h ≤ Q) :
    (scalarSum A R d h).natAbs ≤ (8 * Q) ^ (2 * R) := by
  have hc (j : ℕ) : (coefficientAt A R j).natAbs ≤ (4 * Q) ^ R := by
    rw [coefficientAt_eq]
    exact LayoutCoefficientBounds.natAbs_extend_parityCoefficients_le A R Q j hAQ hQ
  apply le_trans _ (LayoutProgram.scalarMass_le R d h Q hQ hh
    (fun j => (coefficientAt A R j).natAbs) (fun j _ => hc j))
  unfold scalarSum LayoutProgram.scalarMass
  rw [Int.natAbs_mul]
  simp only [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]
  convert Int.natAbs_sum_le (Finset.range (R - d))
    (fun k => coefficientAt A R (d + k) * 2 ^ (R - 1 - (d + k)) *
      (h.choose k : ℤ)) using 1
  simp [Int.natAbs_mul, Int.natAbs_pow]

theorem natAbs_scalarEntry_le {r Q Δ : ℕ} (i : Fin Δ) (t : Fin Q)
    (A R : ℕ) (hAQ : A ≤ Q) (u y : UniversalType r Q Δ) :
    (scalarEntry i t A R u y).natAbs ≤ (8 * Q) ^ (2 * R) := by
  unfold scalarEntry
  split_ifs
  · apply natAbs_scalarSum_le A R Q _ _ hAQ (by have := t.isLt; omega)
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin Q)
  · simp

theorem natAbs_localEntry_le {r Q D : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (A R : ℕ) (hAQ : A ≤ Q) (t : Fin Q) (j v : Fin D) :
    (LayoutProgram.localEntry P A R t j v).natAbs ≤
      LayoutProgram.constraintMassBound Q R := by
  have hQ : 1 ≤ Q := by have := t.isLt; omega
  have hone : 1 ≤ LayoutProgram.constraintMassBound Q R := by
    unfold LayoutProgram.constraintMassBound
    exact (one_le_pow₀ (show 1 ≤ 8 * Q by omega)).trans (Nat.le_add_right _ _)
  unfold LayoutProgram.localEntry
  split
  · split_ifs <;> simp_all
  · split
    · simp
    · split
      · calc
          _ ≤ _ := Int.natAbs_sub_le _ _
          _ ≤ 2 ^ (R - 1) + (8 * Q) ^ (2 * R) := by
            apply Nat.add_le_add
            · split <;> norm_num [Int.natAbs_pow]
            · exact natAbs_scalarEntry_le _ _ _ _ hAQ _ _
          _ = _ := by simp [LayoutProgram.constraintMassBound, Nat.add_comm]
      · simp

/-- The height grows with the actual owner fiber, preserving the bounded
incidence parameter needed for the attained-signature time estimate. -/
theorem natAbs_literalMatrix_le_fiber {r Q D n : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (A R : ℕ) (hAQ : A ≤ Q) (t : Fin Q) (j : Fin D) (v : Fin n) :
    (LayoutProducedMatrix.literalMatrix P owner A R t j v).natAbs ≤
      (Finset.univ.filter (fun i => owner i = v)).card *
        LayoutProgram.constraintMassBound Q R := by
  unfold LayoutProducedMatrix.literalMatrix LayoutPullback.row
  calc
    _ ≤ ∑ i : Fin D, (if owner i = v then LayoutProgram.localEntry P A R t j i
        else 0).natAbs := Int.natAbs_sum_le _ _
    _ = ∑ i ∈ Finset.univ.filter (fun i => owner i = v),
        (LayoutProgram.localEntry P A R t j i).natAbs := by
      simp only [Finset.sum_filter, apply_ite Int.natAbs, Int.natAbs_zero]
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => owner i = v),
        LayoutProgram.constraintMassBound Q R := by
      apply Finset.sum_le_sum
      intro i _
      exact natAbs_localEntry_le P A R hAQ t j i
    _ = _ := by simp

/-- A coarse incidence-size bound is convenient for retained binary words. -/
theorem natAbs_literalMatrix_le {r Q D n : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (A R : ℕ) (hAQ : A ≤ Q) (t : Fin Q) (j : Fin D) (v : Fin n) :
    (LayoutProducedMatrix.literalMatrix P owner A R t j v).natAbs ≤
      D * LayoutProgram.constraintMassBound Q R := by
  apply (natAbs_literalMatrix_le_fiber P owner A R hAQ t j v).trans
  apply Nat.mul_le_mul_right
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin D)

theorem constraintMassBound_le_pow (Q R : ℕ) (hQ : 1 ≤ Q) :
    LayoutProgram.constraintMassBound Q R ≤ 2 ^ (1 + 2 * R * (Q + 3)) := by
  have hbase : 8 * Q ≤ 2 ^ (Q + 3) := by
    calc
      _ ≤ 8 * 2 ^ Q := Nat.mul_le_mul_left 8 (Nat.le_of_lt Nat.lt_two_pow_self)
      _ = _ := by rw [pow_add]; norm_num; ring
  calc
    _ ≤ 2 * (8 * Q) ^ (2 * R) := LayoutProgram.constraintMassBound_le Q R hQ
    _ ≤ 2 * (2 ^ (Q + 3)) ^ (2 * R) := Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_left hbase _)
    _ = _ := by rw [← pow_mul, pow_add]; simp [Nat.mul_comm]

/-- Applies to the two physically retained unsigned components only after
their actual total has been bounded, so cancellation cannot hide storage. -/
theorem component_bits_length_le (D Q R positive negative : ℕ) (hQ : 1 ≤ Q)
    (hMass : positive + negative ≤ D * LayoutProgram.constraintMassBound Q R) :
    positive.bits.length + negative.bits.length ≤ 2 * (D + 2 * R * (Q + 3) + 2) := by
  have hbound : D * LayoutProgram.constraintMassBound Q R <
      2 ^ (D + 2 * R * (Q + 3) + 2) := by
    calc
      _ ≤ 2 ^ D * 2 ^ (1 + 2 * R * (Q + 3)) := Nat.mul_le_mul
        (Nat.le_of_lt Nat.lt_two_pow_self) (constraintMassBound_le_pow Q R hQ)
      _ = 2 ^ (D + 2 * R * (Q + 3) + 1) := by rw [← pow_add]; congr 1; omega
      _ < _ := Nat.pow_lt_pow_right (by omega) (by omega)
  have hp : positive.size ≤ D + 2 * R * (Q + 3) + 2 := Nat.size_le.mpr (by omega)
  have hn : negative.size ≤ D + 2 * R * (Q + 3) + 2 := Nat.size_le.mpr (by omega)
  simp only [Nat.size_eq_bits_len]
  omega

/-- Exponentially large integer values still have polynomial binary words. -/
theorem literalMatrix_bits_length_le {r Q D n : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (A R : ℕ) (hAQ : A ≤ Q) (t : Fin Q) (j : Fin D) (v : Fin n) :
    (LayoutProducedMatrix.literalMatrix P owner A R t j v).natAbs.bits.length ≤
      D + 2 * R * (Q + 3) + 2 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  calc
    _ ≤ D * LayoutProgram.constraintMassBound Q R :=
      natAbs_literalMatrix_le P owner A R hAQ t j v
    _ ≤ 2 ^ D * 2 ^ (1 + 2 * R * (Q + 3)) := Nat.mul_le_mul
      (Nat.le_of_lt Nat.lt_two_pow_self)
      (constraintMassBound_le_pow Q R (by have := t.isLt; omega))
    _ = 2 ^ (D + 2 * R * (Q + 3) + 1) := by rw [← pow_add]; congr 1; omega
    _ < _ := Nat.pow_lt_pow_right (by omega) (by omega)

/-- Storing every head matrix stores each original-variable column once at
each node, even if an original variable has no incidence. -/
theorem raw_entry_count {r n : ℕ} (head : Fin n → Fin r) (D : ℕ) :
    (∑ g : Fin r, D * Fintype.card {v : Fin n // head v = g}) = D * n := by
  have h : (∑ g : Fin r, Fintype.card {v : Fin n // head v = g}) = n := by
    simpa using Fintype.sum_fiberwise head (fun _ => (1 : ℕ))
  rw [← Finset.mul_sum, h]

/-- A signed-magnitude encoding with one sign bit per retained integer has
polynomial total size; this bound includes every raw row, not a basis. -/
theorem raw_matrix_bits_le {r Q D n : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (head : Fin n → Fin r) (A R : ℕ) (hAQ : A ≤ Q) (t : Fin Q) :
    (∑ g : Fin r, ∑ j : Fin D, ∑ v : {v : Fin n // head v = g},
      (1 + (LayoutProducedMatrix.literalMatrix P owner A R t j v.val).natAbs.bits.length)) ≤
      D * n * (D + 2 * R * (Q + 3) + 3) := by
  calc
    _ ≤ ∑ g : Fin r, ∑ _j : Fin D, ∑ _v : {v : Fin n // head v = g},
        (D + 2 * R * (Q + 3) + 3) := by
      apply Finset.sum_le_sum
      intro g _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro v _
      have h := literalMatrix_bits_length_le P owner A R hAQ t j v.val
      omega
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      simp_rw [← Nat.mul_assoc]
      rw [← Finset.sum_mul, raw_entry_count]

/-- The entire integer measurement is retained, with no modular reduction.
Its word length remains polynomial even when its numerical value is large. -/
theorem raw_signature_bits_length_le {r Q D n : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (head : Fin n → Fin r) (A R : ℕ) (hAQ : A ≤ Q) (t : Fin Q) (g : Fin r)
    (x : {v : Fin n // head v = g} → Bool) (j : Fin D) :
    (LayoutSignatureBound.boolSignature
      (fun j (v : {v : Fin n // head v = g}) =>
        LayoutProducedMatrix.literalMatrix P owner A R t j v.val) x j).natAbs.bits.length ≤
      n + D + 2 * R * (Q + 3) + 2 := by
  have hentry : ∀ j (v : {v : Fin n // head v = g}),
      |LayoutProducedMatrix.literalMatrix P owner A R t j v.val| ≤
        (D * LayoutProgram.constraintMassBound Q R : ℕ) := by
    intro j v
    rw [← Int.natCast_natAbs]
    exact_mod_cast natAbs_literalMatrix_le P owner A R hAQ t j v.val
  have hsig := LayoutSignatureBound.abs_boolSignature_le _
    (D * LayoutProgram.constraintMassBound Q R) hentry x j
  rw [← Int.natCast_natAbs] at hsig
  have hsig' : (LayoutSignatureBound.boolSignature
      (fun j (v : {v : Fin n // head v = g}) =>
        LayoutProducedMatrix.literalMatrix P owner A R t j v.val) x j).natAbs ≤
      Fintype.card {v : Fin n // head v = g} *
        (D * LayoutProgram.constraintMassBound Q R) := by exact_mod_cast hsig
  have hcard : Fintype.card {v : Fin n // head v = g} ≤ n := by
    simpa using Fintype.card_subtype_le (fun v : Fin n => head v = g)
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  calc
    _ ≤ n * (D * LayoutProgram.constraintMassBound Q R) := hsig'.trans
      (Nat.mul_le_mul_right _ hcard)
    _ ≤ 2 ^ n * (2 ^ D * 2 ^ (1 + 2 * R * (Q + 3))) := Nat.mul_le_mul
      (Nat.le_of_lt Nat.lt_two_pow_self)
      (Nat.mul_le_mul (Nat.le_of_lt Nat.lt_two_pow_self)
        (constraintMassBound_le_pow Q R (by have := t.isLt; omega)))
    _ = 2 ^ (n + D + 2 * R * (Q + 3) + 1) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ < _ := Nat.pow_lt_pow_right (by omega) (by omega)

/-- The rank bound is instantiated with a proved height for the actual raw
matrix. Neither a small retained basis nor a coefficient-bound oracle is used. -/
theorem literal_attained_signatures_le {r Q D n : ℕ} {O : Type*} [CommRing O]
    {node : Fin Q → O}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t, (P.label i).head t = head t (owner i))
    (A R B : ℕ) (hAQ : A ≤ Q)
    (hB : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r) :
    Nat.card (Set.range (LayoutSignatureBound.boolSignature
      (fun j (v : {v : Fin n // head t v = g}) =>
        LayoutProducedMatrix.literalMatrix P owner A R t j v.val))) ≤
      (2 * Fintype.card {v : Fin n // head t v = g} *
        (B * LayoutProgram.constraintMassBound Q R) + 1) ^
        LayoutRank.rowRank (pulledConstraints
          (LayoutProducedMatrix.headOwner P owner head hhead t g)
          (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
            P.completeBlocks t g)) := by
  have hW : ∀ j (v : {v : Fin n // head t v = g}),
      |LayoutProducedMatrix.literalMatrix P owner A R t j v.val| ≤
        (B * LayoutProgram.constraintMassBound Q R : ℕ) := by
    intro j v
    rw [← Int.natCast_natAbs]
    exact_mod_cast (natAbs_literalMatrix_le_fiber P owner A R hAQ t j v.val).trans
      (Nat.mul_le_mul_right _ (hB v.val))
  have h := LayoutSignatureBound.card_range_boolSignature_le_rank _ _ hW
  rwa [LayoutProducedMatrix.literalHead_rank P owner head hhead A R denom hdenom units t g] at h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutSizes
