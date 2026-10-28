import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFNodeSearchCorrectness
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyEncoding

namespace OAI.Algorithms

/-!
# Typed witnesses from the actual encoded node search

Typed preimages are used only to state and prove SAT semantics. The fixed
program operates on the encoded words whose exact values appear below.
-/

namespace SubexponentialSAT.ExecSparsifySearchWitness

open BitProgram StructuredCalls ExecCNF ExecSparsifyEncoding
open ExecCNFWidthLoad (low)

abbrev Data := ExecCNFNodeSearch.Data
abbrev natClauseCode := Encoding.encodeList Encoding.encodeNat
abbrev natFormulaCode := Encoding.encodeList natClauseCode

theorem clause_words_encoding {n : ℕ} (K : Clause (SAT.Literal (Fin n))) :
    Encoding.encodeList id (K.map ExecSunflowerCodeTransport.literalWord) =
      natClauseCode (K.map Encoding.literalCode) := by
  change Encoding.encodeList id (K.map ExecSunflowerCodeTransport.literalWord) =
    Encoding.encodeList Encoding.encodeNat (K.map Encoding.literalCode)
  rw [encodeList_map, encodeList_map]
  rfl

/-- This record describes data already returned on the search's stacks.
It is not an input to the machine and adds no search primitive. -/
structure TypedWitness {n k : ℕ} (F : Formula (SAT.Literal (Fin n)))
    (z : ℕ → ℕ) (b : Data k) where
  selected : Formula (SAT.Literal (Fin n))
  core : Clause (SAT.Literal (Fin n))
  choice : Sparsify.Choice (formulaSet F) z k
  selected_subset : selected ⊆ F
  core_sublist : ∃ C ∈ F, core.Sublist C
  core_eq : choice.flower.core = clauseSet core
  selected_eq : SunflowerBranch.clauses choice.flower.core choice.flower.petals = formulaSet selected
  family_word : b.stacks (low k 13) = natFormulaCode (codes selected)
  core_word : b.stacks (low k 8) = natClauseCode (core.map Encoding.literalCode)

def TypedOutcome {n k : ℕ} (F : Formula (SAT.Literal (Fin n)))
    (z : ℕ → ℕ) (b : Data k) : Prop :=
  (b.stacks (low k 21) = [] ∧ ∀ j, 2 ≤ j → j ≤ k → Sparsify.FreeAt (formulaSet F) z j) ∨
    (b.stacks (low k 21) ≠ [] ∧ Nonempty (TypedWitness F z b))

theorem outcome_typed {n k : ℕ} (F : Formula (SAT.Literal (Fin n)))
    (z : ℕ → ℕ) (count : List Bool) (b : Data k)
    (hF : (F.map clauseSet).Nodup) (hC : ∀ C ∈ F, C.Nodup)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j)
    (hcount : CounterPrograms.value count = (words F).length)
    (ho : ExecCNFNodeSearchCorrectness.Outcome (words F) count z b) :
    TypedOutcome F z b := by
  rcases ho with hnone | hsome
  · refine Or.inl ⟨hnone.1, ?_⟩
    intro j hj hjk
    change Sunflower.NonemptyCoreSunflowerFree
      ((formulaSet F).filter (fun C => C.card = j)) (z j)
    apply ExecSunflowerCodeTransport.nonemptyCoreSunflowerFree_reflect
      ExecSunflowerCodeTransport.literalWord ExecSunflowerCodeTransport.literalWord_injective
    rw [ExecSunflowerCodeTransport.width_filter_image _
      ExecSunflowerCodeTransport.literalWord_injective,
      ← ExecSunflowerCodeTransport.formulaSet_map]
    exact hnone.2 j hj hjk
  · obtain ⟨hne, d, hd, hminimum⟩ := hsome
    have hdlo : 2 ≤ ExecCNFWidthDriver.dimension d := by
      unfold ExecCNFWidthDriver.dimension
      omega
    have hdhi := ExecCNFWidthDriver.dimension_le d
    have hcount' : BinaryArithmetic.toNat count = (words F).length := by
      simpa only [CounterPrograms.value_eq_toNat] using hcount
    obtain ⟨G, H, hG, hH, hGF, _, hHsub, hcore, hflower, hcard, hwidth⟩ :=
      ExecSunflowerCallback.saved_sound_with_core_sublist (words F) count
        (ExecCNFWidthDriver.dimension d).bits (b.stacks (low k 15))
        (ExecCNFWidthInvariant.localState b) hd.2.2 hne
        (words_clause_nodup F hF) (words_literal_nodup F hC) hcount'
    have hcard' : (formulaSet G).card = z (ExecCNFWidthDriver.dimension d) :=
      hcard.trans hd.2.1
    have hwidth' : ∀ C ∈ formulaSet G, C.card = ExecCNFWidthDriver.dimension d := by
      simpa only [ArithmeticExpressionSupport.bits_value] using hwidth
    obtain ⟨A, K, hAF, hAmap, hKmap, c, _, hcK, hcA⟩ :=
      choice_with_lists F G H z k (ExecCNFWidthDriver.dimension d) hdlo hdhi
        (hz _ hdlo hdhi) hGF hflower hcore hcard' hwidth' hminimum
    have hKsub : ∃ C ∈ F, K.Sublist C := by
      obtain ⟨D, hDF, hHD⟩ := hHsub
      obtain ⟨C, hCF, hCmap⟩ := List.mem_map.mp hDF
      refine ⟨C, hCF, sublist_reflect ExecSunflowerCodeTransport.literalWord
        ExecSunflowerCodeTransport.literalWord_injective K C ?_⟩
      simpa only [hKmap, hCmap] using hHD
    have hGword : b.stacks (low k 13) = natFormulaCode (codes A) := by
      change b.stacks (low k 13) = CandidatePrepareProgram.formulaCode G at hG
      rw [← hAmap] at hG
      exact hG.trans (words_encoding A)
    have hHword : b.stacks (low k 8) = natClauseCode (K.map Encoding.literalCode) := by
      change b.stacks (low k 8) = CandidatePrepareProgram.clauseCode H at hH
      rw [← hKmap] at hH
      exact hH.trans (clause_words_encoding K)
    exact Or.inr ⟨hne, ⟨⟨A, K, c, hAF, hKsub, hcK, hcA, hGword, hHword⟩⟩⟩

/-- One fixed node-search program returns a typed valid choice, or certifies
terminality. Its count and index-width words are computed internally. -/
theorem program_typed {n k : ℕ} (F : Formula (SAT.Literal (Fin n)))
    (z : ℕ → ℕ) (a : Data k)
    (ha : ExecCNFNodeSearch.Fresh (words F) a)
    (hF : (F.map clauseSet).Nodup) (hC : ∀ C ∈ F, C.Nodup)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j)
    (hbank : ExecCNFNodeSearchCorrectness.BankValues z a) :
    ∃ (t : ℕ) (b : Data k),
      Trace (ExecCNFNodeSearch.program k) t
        (a.withPC (some (ExecCNFNodeSearch.program k).entry)) (b.withPC none) ∧
      b.stacks (low k 16) = natFormulaCode (codes F) ∧
      ExecCNFNodeSearch.Frame k a b ∧ TypedOutcome F z b := by
  have hnorm : ExecCNFWidthCorrectness.Normalized (words F) k :=
    ⟨words_clause_nodup F hF, words_literal_nodup F hC, words_width F k hwidth⟩
  obtain ⟨count, width, hc, _, _, _, ns, nt, b, _, htrace, hsource, _, _, hf, ho⟩ :=
    ExecCNFNodeSearchCorrectness.program_correct k (words F) z a ha hnorm
      (fun j hj hjk => Nat.lt_of_lt_of_le (by decide : 0 < 2) (hz j hj hjk)) hbank
  exact ⟨ns + nt + 2, b, htrace, hsource.trans (words_encoding F), hf,
    outcome_typed F z count b hF hC hz hc ho⟩

end SubexponentialSAT.ExecSparsifySearchWitness

end OAI.Algorithms
