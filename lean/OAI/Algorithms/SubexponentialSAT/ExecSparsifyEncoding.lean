import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCodeTransport

namespace OAI.Algorithms

/-! Exact syntax and normalization bridges for the word-based node search. -/

namespace SubexponentialSAT.ExecSparsifyEncoding

open ExecCNF ExecSunflowerCodeTransport

theorem encodeList_map {α β : Type*} (f : α → β) (enc : β → List Bool) (xs : List α) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (fun x => enc (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, ih]

def words {n : ℕ} (F : Formula (SAT.Literal (Fin n))) : Formula (List Bool) :=
  F.map (List.map literalWord)

def codes {n : ℕ} (F : Formula (SAT.Literal (Fin n))) : Formula ℕ :=
  F.map (List.map Encoding.literalCode)

theorem words_eq_codes {n : ℕ} (F : Formula (SAT.Literal (Fin n))) :
    words F = (codes F).map (List.map Encoding.encodeNat) := by
  simp [words, codes, literalWord, List.map_map, Function.comp_def]

theorem words_encoding {n : ℕ} (F : Formula (SAT.Literal (Fin n))) :
    Encoding.encodeList (Encoding.encodeList id) (words F) =
      Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (codes F) := by
  rw [words_eq_codes, encodeList_map]
  congr 1
  funext C
  exact encodeList_map Encoding.encodeNat id C

theorem words_encodeRawFormula {n : ℕ} (F : Formula (SAT.Literal (Fin n))) :
    Encoding.encodeList (Encoding.encodeList id) (words F) =
      ExecQuantitativeSparsify.encodeRawFormula F :=
  words_encoding F

theorem mapped_clause_nodup {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (F : Formula α)
    (hF : (F.map clauseSet).Nodup) :
    ((F.map (List.map f)).map clauseSet).Nodup := by
  have h := hF.map (Finset.image_injective hf)
  have he : (F.map clauseSet).map (Finset.image f) =
      (F.map (List.map f)).map clauseSet := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro C _
    exact (clauseSet_map f C).symm
  exact he ▸ h

theorem words_clause_nodup {n : ℕ} (F : Formula (SAT.Literal (Fin n)))
    (hF : (F.map clauseSet).Nodup) : ((words F).map clauseSet).Nodup :=
  mapped_clause_nodup literalWord literalWord_injective F hF

theorem words_literal_nodup {n : ℕ} (F : Formula (SAT.Literal (Fin n)))
    (hF : ∀ C ∈ F, C.Nodup) : ∀ C ∈ words F, C.Nodup := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
  exact (hF D hD).map literalWord_injective

theorem words_width {n : ℕ} (F : Formula (SAT.Literal (Fin n))) (k : ℕ)
    (hF : ∀ C ∈ F, C.length ≤ k) : ∀ C ∈ words F, C.length ≤ k := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
  simpa only [List.length_map] using hF D hD

@[simp] theorem words_length {n : ℕ} (F : Formula (SAT.Literal (Fin n))) :
    (words F).length = F.length := by simp [words]

theorem sublist_reflect {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (A B : List α) (h : (A.map f).Sublist (B.map f)) : A.Sublist B := by
  obtain ⟨C, hC, he⟩ := List.sublist_map_iff.mp h
  have hAC : A = C := (List.map_injective_iff.mpr hf) he
  simpa only [hAC] using hC

/-- Retain the exact typed lists as well as the mathematical choice, so the
actual child-program bytes can be identified without reordering clauses. -/
theorem choice_with_lists {n : ℕ} (F : Formula (SAT.Literal (Fin n)))
    (G : Formula (List Bool)) (H : Clause (List Bool)) (z : ℕ → ℕ) (k d : ℕ)
    (hdlo : 2 ≤ d) (hdhi : d ≤ k) (hz : 2 ≤ z d)
    (hG : G ⊆ words F)
    (hflower : Sunflower.IsSunflowerWithCore (formulaSet G) (clauseSet H))
    (hcore : (clauseSet H).Nonempty) (hcard : (formulaSet G).card = z d)
    (hwidth : ∀ C ∈ formulaSet G, C.card = d)
    (hminimum : InsertionInvariant.MinimumWidth z (formulaSet (words F)) d) :
    ∃ A : Formula (SAT.Literal (Fin n)), ∃ K : Clause (SAT.Literal (Fin n)),
      A ⊆ F ∧ words A = G ∧ K.map literalWord = H ∧
      ∃ c : Sparsify.Choice (formulaSet F) z k,
        c.width = d ∧ c.flower.core = clauseSet K ∧
        SunflowerBranch.clauses c.flower.core c.flower.petals = formulaSet A := by
  have htwo : 2 ≤ (formulaSet G).card := by rw [hcard]; exact hz
  obtain ⟨A, K, hA, hmapA, hmapK, s, hsK, hsA, hsub, hsize⟩ :=
    typed_sunflower literalWord literalWord_injective F G H d hG hflower hcore htwo hwidth
  let c : Sparsify.Choice (formulaSet F) z k :=
    ⟨d, hdlo, hdhi, s, hsub, hsize.trans hcard,
      minimumWidth_codes_reflect literalWord literalWord_injective F z d hminimum⟩
  exact ⟨A, K, hA, hmapA, hmapK, c, rfl, hsK, hsA⟩

end SubexponentialSAT.ExecSparsifyEncoding

end OAI.Algorithms
