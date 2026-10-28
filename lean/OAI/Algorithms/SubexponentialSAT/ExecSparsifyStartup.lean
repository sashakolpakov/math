import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFCodeTransport
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyEncoding
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness
import OAI.Algorithms.SubexponentialSAT.CandidatePrepareProgram

namespace OAI.Algorithms

/-!
# Startup invariants for the actual normalized formula

These facts concern the ordered list emitted by the checked normalizer.
The three-part conjunction is definitionally the observed sparsifier's
`Ready` predicate. Keeping that predicate expanded here avoids a dependency
on the complete search and worklist implementation.
-/

namespace SubexponentialSAT.ExecSparsifyStartup

open ExecCNF

/-- The same ordered-list startup facts apply directly to numeric literals,
or to any other decidable literal alphabet. -/
theorem normalize_raw_ready {α : Type*} [DecidableEq α]
    (neg : α → α) (F : Formula α) (k : ℕ)
    (hF : ∀ C ∈ F, C.length ≤ k) :
    ((normalize neg F).map clauseSet).Nodup ∧
      (∀ C ∈ normalize neg F, C.Nodup) ∧
      ∀ C ∈ normalize neg F, C.length ≤ k := by
  refine ⟨normalize_map_nodup neg F, normalize_literal_nodup neg F, ?_⟩
  intro C hC
  have hm := absorb_subset _ hC
  have hc := (List.mem_filter.mp hm).1
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hc
  exact (dedupLiterals_length_le D).trans (hF D hD)

/-- The set form of the antichain property does not require typed SAT
literals and therefore also applies to the raw numeric normalization. -/
theorem normalize_raw_antichain {α : Type*} [DecidableEq α]
    (neg : α → α) (F : Formula α) :
    ∀ C ∈ formulaSet (normalize neg F), ∀ D ∈ formulaSet (normalize neg F),
      C ⊆ D → C = D := by
  classical
  intro C hC D hD hCD
  rw [ExecCNF.normalize, formulaSet_absorb] at hC hD
  have hc := (Finset.mem_filter.mp hC).1
  have hd := (Finset.mem_filter.mp hD).2
  by_contra hne
  exact hd ⟨C, hc, Finset.ssubset_iff_subset_ne.mpr ⟨hCD, hne⟩⟩

theorem numeric_ready (F : Formula ℕ) (k : ℕ)
    (hF : ∀ C ∈ F, C.length ≤ k) :
    ((normalize SubexpFrontend.negateCode F).map clauseSet).Nodup ∧
      (∀ C ∈ normalize SubexpFrontend.negateCode F, C.Nodup) ∧
      ∀ C ∈ normalize SubexpFrontend.negateCode F, C.length ≤ k :=
  normalize_raw_ready SubexpFrontend.negateCode F k hF

theorem numeric_antichain (F : Formula ℕ) :
    ∀ C ∈ formulaSet (normalize SubexpFrontend.negateCode F),
      ∀ D ∈ formulaSet (normalize SubexpFrontend.negateCode F), C ⊆ D → C = D :=
  normalize_raw_antichain SubexpFrontend.negateCode F

variable {n : ℕ}

theorem normalizedInput_ready (F : ExecSparsifyWorklist.Formula n) (k : ℕ)
    (hF : ExecSunflowerSearch.RawWidthAtMost k F) :
    ((ExecSparsifyWorklist.normalizedInput F).map clauseSet).Nodup ∧
      (∀ C ∈ ExecSparsifyWorklist.normalizedInput F, C.Nodup) ∧
      ∀ C ∈ ExecSparsifyWorklist.normalizedInput F, C.length ≤ k := by
  rw [ExecCNFCodeTransport.normalizedInput_eq_normalize]
  exact normalize_raw_ready SAT.Literal.negate F k hF

theorem normalizedInput_antichain (F : ExecSparsifyWorklist.Formula n) :
    SunflowerBranch.Antichain (formulaSet (ExecSparsifyWorklist.normalizedInput F)) := by
  rw [ExecSparsifyWorklist.normalizedInput_set]
  exact SunflowerBranch.antichain_normalize _

/-- A width bound on the original finite-set CNF supplies all three ordered
list invariants required by the actual index-and-mask search. -/
theorem normalizedFormula_ready (F : SAT.CNF (Fin n)) (k : ℕ)
    (hF : SAT.WidthAtMost k F) :
    ((SubexpNormalizationCorrectness.normalizedFormula F).map clauseSet).Nodup ∧
      (∀ C ∈ SubexpNormalizationCorrectness.normalizedFormula F, C.Nodup) ∧
      ∀ C ∈ SubexpNormalizationCorrectness.normalizedFormula F, C.length ≤ k :=
  normalizedInput_ready (ExecQuantitativeSparsify.formulaList F) k
    (ExecQuantitativeSparsify.formulaList_width F k hF)

theorem normalizedFormula_antichain (F : SAT.CNF (Fin n)) :
    SunflowerBranch.Antichain
      (formulaSet (SubexpNormalizationCorrectness.normalizedFormula F)) :=
  normalizedInput_antichain (ExecQuantitativeSparsify.formulaList F)

/-- The numeric normalizer's output is the exact encoded typed input of
the observed worklist, with the equality oriented for procedure composition. -/
theorem numeric_normalizedInput_code (F : ExecSparsifyWorklist.Formula n) :
    SubexpNormalizationProgram.formulaCode
        (ExecCNF.normalize SubexpFrontend.negateCode (F.map (List.map Encoding.literalCode))) =
      CandidatePrepareProgram.formulaCode
        (ExecSparsifyEncoding.words (ExecSparsifyWorklist.normalizedInput F)) := by
  rw [← ExecCNFCodeTransport.normalizedInput_literalCode F]
  exact (ExecSparsifyEncoding.words_encoding _).symm

theorem numeric_normalizedFormula_code (F : SAT.CNF (Fin n)) :
    SubexpNormalizationProgram.formulaCode
        (ExecCNF.normalize SubexpFrontend.negateCode
          ((ExecQuantitativeSparsify.formulaList F).map (List.map Encoding.literalCode))) =
      CandidatePrepareProgram.formulaCode
        (ExecSparsifyEncoding.words (SubexpNormalizationCorrectness.normalizedFormula F)) :=
  numeric_normalizedInput_code (ExecQuantitativeSparsify.formulaList F)

/-- These are the exact bytes consumed by the observed node search. The
normalizer has already produced them; no reordering or recoding is needed. -/
theorem normalizedFormula_body (F : SAT.CNF (Fin n)) :
    CandidatePrepareProgram.formulaCode
        (ExecSparsifyEncoding.words (SubexpNormalizationCorrectness.normalizedFormula F)) =
      SubexpNormalizationCorrectness.normalizedBody F :=
  ExecSparsifyEncoding.words_encodeRawFormula _

theorem normalizedFormula_body_length_le (F : SAT.CNF (Fin n)) :
    (CandidatePrepareProgram.formulaCode
      (ExecSparsifyEncoding.words (SubexpNormalizationCorrectness.normalizedFormula F))).length ≤
        (Encoding.encodeCNFBody F).length := by
  rw [normalizedFormula_body]
  exact SubexpNormalizationCorrectness.normalizedBody_length_le F

end SubexponentialSAT.ExecSparsifyStartup

end OAI.Algorithms
