import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramGenerated
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramCounts

namespace OAI.Algorithms

/-! Input size, produced table size, and binary size of the exact numerator. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.LocalExpectation SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.SqrtLog.PackingProgram

theorem planInput_length_le (M : ℕ) (plans : List (List ℕ))
    (hlen : ∀ p ∈ plans, p.length ≤ 2) (hindex : ∀ p ∈ plans, ∀ i ∈ p, i < M) :
    (ProgramEncoding.encodeRecords (planAlphabet plans)).length ≤
      1 + (16*M+24)*plans.length := by
  have h := ProgramEncoding.encodeRecords_length_le (planAlphabet plans) (8*M+11)
    (planAlphabet_width M plans hlen hindex)
  have hc : 2*(8*M+11)+2 = 16*M+24 := by omega
  rw [hc] at h
  simpa only [planAlphabet, List.length_map] using h

section Sizes
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceInput_length_le (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (incidences : List I) :
    (ProgramEncoding.encodeRecords
      (planAlphabet (incidencePlans ivar factor indices incidences))).length ≤
      1 + (16*indices.length+24)*incidences.length := by
  have hv := incidencePlans_valid ivar factor indices hi incidences
  simpa only [incidencePlans, List.length_map] using
    planInput_length_le indices.length (incidencePlans ivar factor indices incidences) hv.1 hv.2

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem generatedPairRecords_length_le (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (incidences : List I) :
    (PairScoreProgram.pairRecords
      (generatedRawPairs (incidencePlans ivar factor indices incidences))).length ≤
      1 + (32*(indices.length+1)+14)*incidences.length^2 := by
  have h := PairPreparationBounds.encoded_pairRecords_le
    (generatedRawPairs (incidencePlans ivar factor indices incidences))
    (16*(indices.length+1)+6) (by
      intro pair hp
      have hraw := (generatedIncidencePairs_perm ivar factor indices incidences).mem_iff.mp hp
      exact pairBytes_length_le indices.length pair
        (rawPairs_valid ivar factor indices hi incidences pair hraw))
  have hc : 2*(16*(indices.length+1)+6)+2 = 32*(indices.length+1)+14 := by omega
  rw [hc] at h
  simpa only [generatedRawPairs_length, incidencePlans, List.length_map] using h

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceCount_le (alphabet : List (Word r Q)) (terms : List (ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (remaining : List ℕ) (hr : remaining.Nodup)
    (ω : ℕ → Word r Q) :
    (unweightedCounts ivar factor alphabet terms indices remaining ω).1 ≤
      terms.length * alphabet.length^4 := by
  have h := commonNumerator_bound alphabet terms
    (fun z η => incidenceIndicator ivar factor z (fun i => η (indexCode indices i)))
    (numberedScoreSupport ivar factor indices) 4 1 remaining
    (fun z => (active_length_le _ _ hr).trans (numberedScoreSupport_card_le ivar factor indices z))
    (by
      intro z η
      cases z with
      | inl p => rcases p with ⟨i,j⟩; simp only [incidenceIndicator]; split_ifs <;> omega
      | inr p => simp [incidenceIndicator]) ω
  simpa only [unweightedCounts, one_mul] using h

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceNumerator_le (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (n : ℕ) (fixed : List (Word r Q)) :
    incidenceNumerator ivar factor alphabet pairs indices default n fixed ≤
      pairs.length * alphabet.length^4 := by
  simpa only [incidenceNumerator, List.length_map] using
    incidenceCount_le ivar factor alphabet (pairs.map Sum.inl) indices
      (List.range' fixed.length n) List.nodup_range' (decode default fixed)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceNumerator_bitSize (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (default : Word r Q) (n : ℕ) (fixed : List (Word r Q)) :
    (incidenceNumerator ivar factor alphabet pairs indices default n fixed).size ≤
      pairs.length.size + 4*alphabet.length.size + 1 := by
  apply Nat.size_le.mpr
  have hp : pairs.length * alphabet.length^4 ≤
      2^(pairs.length.size + 4*alphabet.length.size) := by
    calc
      _ ≤ (2^pairs.length.size)*(2^alphabet.length.size)^4 :=
        Nat.mul_le_mul (Nat.lt_size_self _).le (Nat.pow_le_pow_left (Nat.lt_size_self _).le _)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  exact ((incidenceNumerator_le ivar factor alphabet pairs indices default n fixed).trans hp).trans_lt
    (Nat.pow_lt_pow_right (by decide) (by omega))
end Sizes
end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
