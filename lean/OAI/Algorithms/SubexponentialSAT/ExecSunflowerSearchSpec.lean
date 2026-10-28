import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCandidateBounds
import OAI.Algorithms.SubexponentialSAT.CandidatePrepareProgram
import OAI.Algorithms.SubexponentialSAT.ExecSelectedFamilyCompleteness
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration

namespace OAI.Algorithms

/-!
# Correctness of the concrete index-and-mask search space

The witnesses below are used only in the completeness proof.  The program
enumerates fixed-width bit tuples and applies the actual index guard, gather,
mask, and candidate-check instructions.
-/

namespace SubexponentialSAT.ExecSunflowerSearchSpec

abbrev Clause := List (List Bool)
abbrev Formula := List Clause

open ExecCNF
open SubexpSunflowerProgram.Intersection

def accept (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) : Bool :=
  CandidatePrepareProgram.valid limit words &&
    ExecSunflowerCandidateProgram.answer (CandidatePrepareProgram.selected F words)
      (CandidatePrepareProgram.core F mask words) width size

theorem checks_of_sunflower (G : Formula) (H : Clause)
    (hG : (G.map clauseSet).Nodup)
    (hf : Sunflower.IsSunflowerWithCore (formulaSet G) (clauseSet H)) :
    (∀ C ∈ G, subset H C = true) ∧
      G.Pairwise (fun C D => ContainsIntersection C D H) := by
  constructor
  · intro C hC
    exact (subset_true H C).mpr (hf.1 _ (mem_formulaSet.mpr ⟨C, hC, rfl⟩))
  · have hp : G.Pairwise (fun C D => clauseSet C ≠ clauseSet D) := by
      exact List.pairwise_map.mp hG
    apply hp.imp_of_mem
    intro C D hC hD hne x hxC hxD
    have he := hf.2 _ (mem_formulaSet.mpr ⟨C, hC, rfl⟩)
      _ (mem_formulaSet.mpr ⟨D, hD, rfl⟩) hne
    apply mem_clauseSet.mp
    rw [← he]
    exact Finset.mem_inter.mpr ⟨mem_clauseSet.mpr hxC, mem_clauseSet.mpr hxD⟩

theorem answer_of_normalized_sunflower (G : Formula) (H : Clause)
    (width size : List Bool) (hG : (G.map clauseSet).Nodup)
    (hC : ∀ C ∈ G, C.Nodup)
    (hf : Sunflower.IsSunflowerWithCore (formulaSet G) (clauseSet H))
    (hH : (clauseSet H).Nonempty)
    (hs : (formulaSet G).card = BinaryArithmetic.toNat size)
    (hw : ∀ C ∈ formulaSet G, C.card = BinaryArithmetic.toNat width) :
    ExecSunflowerCandidateProgram.answer G H width size = true := by
  obtain ⟨hc, hp⟩ := checks_of_sunflower G H hG hf
  apply (ExecSunflowerCandidateProgram.answer_true_iff G H width size).mpr
  refine ⟨⟨⟨⟨?_, ?_⟩, hc⟩, hp⟩, ?_⟩
  · exact (ExecSunflowerCandidateSpec.selected_card G hG).symm.trans hs
  · intro C hCG
    exact (List.toFinset_card_of_nodup (hC C hCG)).symm.trans
      (hw _ (mem_formulaSet.mpr ⟨C, hCG, rfl⟩))
  · intro he
    subst H
    simp at hH

theorem selected_mem_source (F : Formula) (words : List (List Bool)) :
    CandidatePrepareProgram.selected F words ⊆ F := by
  intro C hC
  have hm : C ∈ ExecSelectedFamilyProgram.selectedClauses F words := by
    simpa only [CandidatePrepareProgram.selected, List.mem_reverse] using hC
  obtain ⟨word, _, he⟩ := List.mem_filterMap.mp hm
  exact List.mem_of_getElem? he

theorem selected_literal_nodup (F : Formula) (words : List (List Bool))
    (hF : ∀ C ∈ F, C.Nodup) :
    ∀ C ∈ CandidatePrepareProgram.selected F words, C.Nodup := by
  intro C hC
  exact hF C (selected_mem_source F words hC)

/-- Acceptance of the concrete guards supplies a distinct mathematical
sunflower drawn from the input's clauses of the requested width. -/
theorem sound (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool))
    (hF : (F.map clauseSet).Nodup) (hC : ∀ C ∈ F, C.Nodup)
    (hlimit : BinaryArithmetic.toNat limit = F.length)
    (ha : accept F mask limit width size words = true) :
    CandidatePrepareProgram.selected F words ⊆ F ∧
      formulaSet (CandidatePrepareProgram.selected F words) ⊆
        (formulaSet F).filter (fun C => C.card = BinaryArithmetic.toNat width) ∧
      (clauseSet (CandidatePrepareProgram.core F mask words)).Nonempty ∧
      Sunflower.IsSunflowerWithCore
        (formulaSet (CandidatePrepareProgram.selected F words))
        (clauseSet (CandidatePrepareProgram.core F mask words)) ∧
      (formulaSet (CandidatePrepareProgram.selected F words)).card =
        BinaryArithmetic.toNat size := by
  obtain ⟨hv, hanswer⟩ := Bool.and_eq_true_iff.mp ha
  obtain ⟨hrange, hinc⟩ := (CandidatePrepareProgram.valid_iff limit words).mp hv
  have hi : (words.map CounterPrograms.value).Pairwise (· < ·) := by
    simpa only [List.pairwise_map, CounterPrograms.value_eq_toNat] using hinc
  have hr : ∀ word ∈ words, CounterPrograms.value word < F.length := by
    intro word hw
    simpa only [CounterPrograms.value_eq_toNat, hlimit] using hrange word hw
  obtain ⟨hsub, hnd, _, hs⟩ :=
    ExecSelectedFamilyCompleteness.selectedClauses_sound F words hF hi hr
  obtain ⟨hne, hflower, hcard, huniform⟩ :=
    ExecSunflowerCandidateProgram.accepted_normalized _ _ width size hanswer hnd
      (selected_literal_nodup F words hC)
  refine ⟨hsub, ?_, hne, hflower, hcard⟩
  intro C hCG
  exact Finset.mem_filter.mpr ⟨hs hCG, huniform C hCG⟩

/-- Every finite nonempty selected family has an accepted tuple with the
fixed index width and a mask of the caller's width bound. -/
theorem complete (F : Formula) (k : ℕ) (limit width size : List Bool)
    (hF : (F.map clauseSet).Nodup) (hC : ∀ C ∈ F, C.Nodup)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hlimit : BinaryArithmetic.toNat limit = F.length)
    (S : Finset (Finset (List Bool))) (H : Finset (List Bool))
    (hS : S ⊆ formulaSet F) (hs : S.card = BinaryArithmetic.toNat size)
    (hpos : 0 < S.card) (hH : H.Nonempty)
    (hf : Sunflower.IsSunflowerWithCore S H)
    (hw : ∀ C ∈ S, C.card = BinaryArithmetic.toNat width) :
    ∃ mask words,
      mask.length = k ∧
      words.map List.length = List.replicate (BinaryArithmetic.toNat size)
        (DyadicWidth.width F.length) ∧
      accept F mask limit width size words = true ∧
      formulaSet (CandidatePrepareProgram.selected F words) = S ∧
      clauseSet (CandidatePrepareProgram.core F mask words) = H := by
  let indices := ExecSelectedFamilyCompleteness.familyIndices F S
  let words := indices.map (ExecCNFTupleEnumeration.fixedBits (DyadicWidth.width F.length))
  have hvalues : words.map CounterPrograms.value = indices := by
    dsimp [words]
    rw [List.map_map]
    calc
      _ = indices.map id := by
        apply List.map_congr_left
        intro i hi
        exact ExecCNFTupleEnumeration.fixedBits_value _ i
          ((ExecSelectedFamilyCompleteness.familyIndices_lt_length F S i hi).trans
            (DyadicWidth.lt_two_pow_width F.length))
      _ = indices := List.map_id _
  obtain ⟨hinc, hrange, hlen, hglen, hset, hgnd⟩ :=
    ExecSelectedFamilyCompleteness.selectedClauses_of_values F S words hF hS hvalues
  let G := CandidatePrepareProgram.selected F words
  have hGset : formulaSet G = S := hset
  have hGnd : (G.map clauseSet).Nodup := hgnd
  have hGne : G ≠ [] := by
    intro he
    have hz : S.card = 0 := by rw [← hGset, he]; rfl
    omega
  have hhead : G.headD [] ∈ G := by
    cases hG : G with
    | nil => exact False.elim (hGne hG)
    | cons C Cs => simp
  have hheadF := selected_mem_source F words hhead
  obtain ⟨mask, hmask, hcore⟩ := CoreMaskProgram.exists_mask_of_subset k (G.headD []) H
    (hwidth _ hheadF) (hf.1 _ (by rw [← hGset]; exact mem_formulaSet.mpr ⟨_, hhead, rfl⟩))
  have hcore' : clauseSet (CandidatePrepareProgram.core F mask words) = H := hcore
  have hvalid : CandidatePrepareProgram.valid limit words = true := by
    apply (CandidatePrepareProgram.valid_iff limit words).mpr
    constructor
    · intro word hword
      rw [hlimit, ← CounterPrograms.value_eq_toNat]
      exact hrange word hword
    · simpa only [List.pairwise_map, CounterPrograms.value_eq_toNat] using hinc
  refine ⟨mask, words, hmask, ?_, ?_, hGset, hcore'⟩
  · change (indices.map (ExecCNFTupleEnumeration.fixedBits
        (DyadicWidth.width F.length))).map List.length = _
    rw [ExecCNFTupleEnumeration.fixedBits_map_shape]
    have hi : indices.length = BinaryArithmetic.toNat size :=
      (ExecSelectedFamilyCompleteness.familyIndices_length F S hF hS).trans hs
    rw [hi]
  · apply Bool.and_eq_true_iff.mpr
    refine ⟨hvalid, ?_⟩
    apply answer_of_normalized_sunflower G _ width size hGnd
      (selected_literal_nodup F words hC)
    · simpa only [hGset, hcore'] using hf
    · simpa only [hcore'] using hH
    · simpa only [hGset] using hs
    · simpa only [hGset] using hw

/-- Exhausting the encoded tuple space without acceptance certifies the
mathematical terminal condition at this width. -/
theorem free_of_no_accept (F : Formula) (k : ℕ) (limit width size : List Bool)
    (hF : (F.map clauseSet).Nodup) (hC : ∀ C ∈ F, C.Nodup)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hlimit : BinaryArithmetic.toNat limit = F.length)
    (hsize : 0 < BinaryArithmetic.toNat size)
    (hno : ∀ mask words, mask.length = k →
      words.map List.length = List.replicate (BinaryArithmetic.toNat size)
        (DyadicWidth.width F.length) → accept F mask limit width size words ≠ true) :
    Sunflower.NonemptyCoreSunflowerFree
      ((formulaSet F).filter (fun C => C.card = BinaryArithmetic.toNat width))
      (BinaryArithmetic.toNat size) := by
  intro S hS hs H hH hf
  obtain ⟨mask, words, hm, hw, ha, _, _⟩ := complete F k limit width size
    hF hC hwidth hlimit S H (fun C hC => (Finset.mem_filter.mp (hS hC)).1)
    hs (hs.symm ▸ hsize) hH hf (fun C hC => (Finset.mem_filter.mp (hS hC)).2)
  exact hno mask words hm hw ha

theorem no_accept_of_free (F : Formula) (limit width size : List Bool)
    (hF : (F.map clauseSet).Nodup) (hC : ∀ C ∈ F, C.Nodup)
    (hlimit : BinaryArithmetic.toNat limit = F.length)
    (hfree : Sunflower.NonemptyCoreSunflowerFree
      ((formulaSet F).filter (fun C => C.card = BinaryArithmetic.toNat width))
      (BinaryArithmetic.toNat size)) :
    ∀ mask words, accept F mask limit width size words ≠ true := by
  intro mask words ha
  obtain ⟨_, hsub, hne, hflower, hcard⟩ := sound F mask limit width size words hF hC hlimit ha
  exact hfree _ hsub hcard _ hne hflower

/-- Exact terminality equivalence for the fixed-shape tuple space traversed
by the odometer, including rejected out-of-range or duplicate-index tuples. -/
theorem free_iff_no_accept (F : Formula) (k : ℕ) (limit width size : List Bool)
    (hF : (F.map clauseSet).Nodup) (hC : ∀ C ∈ F, C.Nodup)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hlimit : BinaryArithmetic.toNat limit = F.length)
    (hsize : 0 < BinaryArithmetic.toNat size) :
    Sunflower.NonemptyCoreSunflowerFree
      ((formulaSet F).filter (fun C => C.card = BinaryArithmetic.toNat width))
      (BinaryArithmetic.toNat size) ↔
    ∀ mask words, mask.length = k →
      words.map List.length = List.replicate (BinaryArithmetic.toNat size)
        (DyadicWidth.width F.length) → accept F mask limit width size words ≠ true := by
  constructor
  · intro h mask words _ _
    exact no_accept_of_free F limit width size hF hC hlimit h mask words
  · exact free_of_no_accept F k limit width size hF hC hwidth hlimit hsize

end SubexponentialSAT.ExecSunflowerSearchSpec

end OAI.Algorithms
