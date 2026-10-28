import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFCodeTransport

namespace OAI.Algorithms

/-!
# Recovering typed sunflower witnesses from encoded candidates

The executable search manipulates literal words. Selected clauses come from
the input list, and the accepted common core lies in each selected clause.
These facts suffice to recover typed lists for proof purposes. The executable
algorithm never needs a choice of a typed inverse.
-/

namespace SubexponentialSAT.ExecSunflowerCodeTransport

open ExecCNF

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
/-- A selected list has an ordered preimage; multiplicities are retained. -/
theorem lift_list (f : α → β) (F : List α) (G : List β)
    (hG : G ⊆ F.map f) :
    ∃ A : List α, A ⊆ F ∧ A.map f = G := by
  induction G with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons x xs ih =>
      obtain ⟨a, ha, hfa⟩ := List.mem_map.mp
        (hG (show x ∈ x :: xs from List.mem_cons_self))
      obtain ⟨A, hA, hm⟩ := ih (fun y hy => hG (by simp [hy]))
      refine ⟨a :: A, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ha
        · exact hA hy
      · simp only [List.map_cons, hfa, hm]

omit [DecidableEq α] [DecidableEq β] in
/-- The stronger sublist case also preserves the selected positions. -/
theorem lift_sublist (f : α → β) (F : List α) (G : List β)
    (hG : G.Sublist (F.map f)) :
    ∃ A : List α, A.Sublist F ∧ A.map f = G := by
  obtain ⟨A, hA, hm⟩ := List.sublist_map_iff.mp hG
  exact ⟨A, hA, hm.symm⟩

@[simp] theorem clauseSet_map (f : α → β) (C : Clause α) :
    clauseSet (C.map f) = (clauseSet C).image f := by
  ext x
  simp only [mem_clauseSet, List.mem_map, Finset.mem_image]

@[simp] theorem formulaSet_map (f : α → β) (F : Formula α) :
    formulaSet (F.map (List.map f)) = (formulaSet F).image (Finset.image f) := by
  ext C
  constructor
  · intro hC
    obtain ⟨D, hD, he⟩ := mem_formulaSet.mp hC
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hD
    exact Finset.mem_image.mpr ⟨clauseSet A, mem_formulaSet.mpr ⟨A, hA, rfl⟩,
      (clauseSet_map f A).symm.trans he⟩
  · intro hC
    obtain ⟨D, hD, he⟩ := Finset.mem_image.mp hC
    obtain ⟨A, hA, rfl⟩ := mem_formulaSet.mp hD
    exact mem_formulaSet.mpr ⟨A.map f, List.mem_map.mpr ⟨A, hA, rfl⟩,
      (clauseSet_map f A).trans he⟩

theorem formulaSet_mono {F G : Formula α} (h : F ⊆ G) : formulaSet F ⊆ formulaSet G := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := mem_formulaSet.mp hC
  exact mem_formulaSet.mpr ⟨D, h hD, rfl⟩

/-- Injective encoding reflects the exact common-intersection condition. -/
theorem sunflower_reflect (f : α → β) (hf : Function.Injective f)
    (F : Finset (Finset α)) (H : Finset α)
    (h : Sunflower.IsSunflowerWithCore (F.image (Finset.image f)) (H.image f)) :
    Sunflower.IsSunflowerWithCore F H := by
  constructor
  · intro C hC
    apply (Finset.image_subset_image_iff hf).mp
    exact h.1 _ (Finset.mem_image.mpr ⟨C, hC, rfl⟩)
  · intro C hC D hD hne
    apply Finset.image_injective hf
    rw [Finset.image_inter C D hf]
    exact h.2 _ (Finset.mem_image.mpr ⟨C, hC, rfl⟩)
      _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)
      (fun he => hne (Finset.image_injective hf he))

/-- Typed sunflower witnesses remain valid after the actual injective encoding. -/
theorem sunflower_image (f : α → β) (hf : Function.Injective f)
    (F : Finset (Finset α)) (H : Finset α)
    (h : Sunflower.IsSunflowerWithCore F H) :
    Sunflower.IsSunflowerWithCore (F.image (Finset.image f)) (H.image f) := by
  constructor
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    exact Finset.image_subset_image (h.1 D hD)
  · intro C hC D hD hne
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hD
    have hAB : A ≠ B := by
      intro he
      exact hne (congrArg (Finset.image f) he)
    rw [← Finset.image_inter A B hf, h.2 A hA B hB hAB]

theorem sunflower_map_iff (f : α → β) (hf : Function.Injective f)
    (F : Formula α) (H : Clause α) :
    Sunflower.IsSunflowerWithCore (formulaSet (F.map (List.map f)))
        (clauseSet (H.map f)) ↔
      Sunflower.IsSunflowerWithCore (formulaSet F) (clauseSet H) := by
  rw [formulaSet_map, clauseSet_map]
  exact ⟨sunflower_reflect f hf _ _, sunflower_image f hf _ _⟩

theorem mapped_family_card (f : α → β) (hf : Function.Injective f)
    (F : Formula α) : (formulaSet (F.map (List.map f))).card = (formulaSet F).card := by
  rw [formulaSet_map]
  exact Finset.card_image_of_injective _ (Finset.image_injective hf)

/-- No separate inverse-decoder hypothesis is required for an accepted core:
it is contained in a selected encoded clause. -/
theorem lift_candidate (f : α → β) (hf : Function.Injective f)
    (F : Formula α) (G : Formula β) (H : Clause β)
    (hG : G ⊆ F.map (List.map f)) (hne : G ≠ [])
    (hflower : Sunflower.IsSunflowerWithCore (formulaSet G) (clauseSet H)) :
    ∃ A : Formula α, ∃ K : Clause α,
      A ⊆ F ∧ A.map (List.map f) = G ∧ K.map f = H ∧
      Sunflower.IsSunflowerWithCore (formulaSet A) (clauseSet K) := by
  obtain ⟨A, hA, hmapA⟩ := lift_list (List.map f) F G hG
  obtain ⟨C, hC⟩ : ∃ C, C ∈ G := by
    cases G with
    | nil => exact (hne rfl).elim
    | cons C G => exact ⟨C, by simp⟩
  obtain ⟨D, hD, hmapD⟩ := List.mem_map.mp (hG hC)
  have hHD : H ⊆ D.map f := by
    intro x hx
    have hcore := hflower.1 (clauseSet C) (mem_formulaSet.mpr ⟨C, hC, rfl⟩)
    rw [hmapD]
    exact mem_clauseSet.mp (hcore (mem_clauseSet.mpr hx))
  obtain ⟨K, _, hmapK⟩ := lift_list f D H hHD
  refine ⟨A, K, hA, hmapA, hmapK, ?_⟩
  apply sunflower_reflect f hf
  rw [← formulaSet_map, ← clauseSet_map, hmapA, hmapK]
  exact hflower

/-- Width checks on encoded clause sets reflect to the typed selected family. -/
theorem uniform_reflect (f : α → β) (hf : Function.Injective f)
    (A : Formula α) (d : ℕ)
    (hw : ∀ C ∈ formulaSet (A.map (List.map f)), C.card = d) :
    ∀ C ∈ formulaSet A, C.card = d := by
  intro C hC
  have hmem : C.image f ∈ formulaSet (A.map (List.map f)) := by
    rw [formulaSet_map]
    exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
  simpa only [Finset.card_image_of_injective C hf] using hw _ hmem

section Typed

variable {V : Type u} [DecidableEq V]

/-- An accepted encoded family yields the exact branching witness required by
the mathematical sparsifier, with the selected family inside the input. -/
theorem typed_sunflower (f : SAT.Literal V → β) (hf : Function.Injective f)
    (F : Formula (SAT.Literal V)) (G : Formula β) (H : Clause β) (d : ℕ)
    (hG : G ⊆ F.map (List.map f))
    (hflower : Sunflower.IsSunflowerWithCore (formulaSet G) (clauseSet H))
    (hcore : (clauseSet H).Nonempty) (hcard : 2 ≤ (formulaSet G).card)
    (hwidth : ∀ C ∈ formulaSet G, C.card = d) :
    ∃ A : Formula (SAT.Literal V), ∃ K : Clause (SAT.Literal V),
      A ⊆ F ∧ A.map (List.map f) = G ∧ K.map f = H ∧
      ∃ s : SunflowerBranch.Sunflower V d,
        s.core = clauseSet K ∧
        SunflowerBranch.clauses s.core s.petals = formulaSet A ∧
        SunflowerBranch.clauses s.core s.petals ⊆ formulaSet F ∧
        s.petals.card = (formulaSet G).card := by
  have hne : G ≠ [] := by
    intro he
    subst G
    simp at hcard
  obtain ⟨A, K, hA, hmapA, hmapK, hs⟩ := lift_candidate f hf F G H hG hne hflower
  have hK : (clauseSet K).Nonempty := by
    have hm : (clauseSet K).image f = clauseSet H := by rw [← clauseSet_map, hmapK]
    rw [← hm] at hcore
    exact Finset.image_nonempty.mp hcore
  have hcardEq : (formulaSet A).card = (formulaSet G).card := by
    rw [← hmapA, mapped_family_card f hf]
  have hsize : 2 ≤ (formulaSet A).card := hcardEq ▸ hcard
  have hw : ∀ C ∈ formulaSet A, C.card = d := by
    apply uniform_reflect f hf A d
    simpa only [hmapA] using hwidth
  let s := SunflowerBranch.Sunflower.ofClauses (formulaSet A) (clauseSet K) d
    hK hsize hs.1 hs.2 hw
  have hselected : SunflowerBranch.clauses s.core s.petals = formulaSet A :=
    SunflowerBranch.Sunflower.ofClauses_selected _ _ _ _ _ _ _ _
  refine ⟨A, K, hA, hmapA, hmapK, s, rfl, hselected, ?_, ?_⟩
  · rw [hselected]
    exact formulaSet_mono hA
  · exact (SunflowerBranch.petalFamily_card hs.1).trans hcardEq

end Typed

/-- The actual literal payload used by the encoded CNF programs. -/
def literalWord {n : ℕ} (l : SAT.Literal (Fin n)) : List Bool :=
  Encoding.encodeNat (Encoding.literalCode l)

theorem literalWord_injective {n : ℕ} :
    Function.Injective (literalWord (n := n)) :=
  Encoding.encodeNat_injective.comp Encoding.literalCode_injective

/-- Filtering the common core out of the selected clauses recovers the
actual petals, even when their list order is different from the old selector. -/
theorem recovered_petals {V : Type u} [DecidableEq V] {d : ℕ}
    (s : SunflowerBranch.Sunflower V d) :
    (SunflowerBranch.clauses s.core s.petals).image (fun C => C \ s.core) = s.petals := by
  ext p
  constructor
  · intro hp
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hC
    simpa only [Finset.union_sdiff_cancel_left (s.disjoint_core q hq)] using hq
  · intro hp
    exact Finset.mem_image.mpr ⟨s.core ∪ p,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.union_sdiff_cancel_left (s.disjoint_core p hp)⟩

theorem petal_filter_family_eq {V : Type u} [DecidableEq V] {d : ℕ}
    (s : SunflowerBranch.Sunflower V d)
    (A : Formula (SAT.Literal V)) (K : Clause (SAT.Literal V))
    (hcore : clauseSet K = s.core)
    (hselected : formulaSet A = SunflowerBranch.clauses s.core s.petals) :
    formulaSet (A.map (fun C => C.filter (fun x => !decide (x ∈ K)))) = s.petals := by
  rw [ExecCNFCodeTransport.petal_family_set, hcore, hselected]
  exact recovered_petals s

/-- Every typed nonempty-core sunflower would encode to a raw one. -/
theorem nonemptyCoreSunflowerFree_reflect (f : α → β) (hf : Function.Injective f)
    (F : Finset (Finset α)) (z : ℕ)
    (h : Sunflower.NonemptyCoreSunflowerFree (F.image (Finset.image f)) z) :
    Sunflower.NonemptyCoreSunflowerFree F z := by
  intro G hG hcard H hH hflower
  apply h (G.image (Finset.image f)) (Finset.image_subset_image hG)
    ((Finset.card_image_of_injective G (Finset.image_injective hf)).trans hcard)
    (H.image f) (Finset.image_nonempty.mpr hH)
  exact sunflower_image f hf G H hflower

omit [DecidableEq α] in
/-- Injective literal encoding preserves each exact-width family. -/
theorem width_filter_image (f : α → β) (hf : Function.Injective f)
    (F : Finset (Finset α)) (d : ℕ) :
    (F.filter (fun C => C.card = d)).image (Finset.image f) =
      (F.image (Finset.image f)).filter (fun C => C.card = d) := by
  ext C
  constructor
  · intro hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨hDF, hDd⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨D, hDF, rfl⟩,
      (Finset.card_image_of_injective D hf).trans hDd⟩
  · intro hC
    obtain ⟨hCF, hCd⟩ := Finset.mem_filter.mp hC
    obtain ⟨D, hDF, rfl⟩ := Finset.mem_image.mp hCF
    refine Finset.mem_image.mpr ⟨D, Finset.mem_filter.mpr ⟨hDF, ?_⟩, rfl⟩
    exact (Finset.card_image_of_injective D hf).symm.trans hCd

/-- The raw exhaustive-search result supplies the precise charging invariant. -/
theorem minimumWidth_reflect (f : α → β) (hf : Function.Injective f)
    (F : Finset (Finset α)) (z : ℕ → ℕ) (d : ℕ)
    (h : InsertionInvariant.MinimumWidth z (F.image (Finset.image f)) d) :
    InsertionInvariant.MinimumWidth z F d := by
  intro j hj hjd
  apply nonemptyCoreSunflowerFree_reflect f hf
  rw [width_filter_image f hf]
  exact h j hj hjd

theorem minimumWidth_codes_reflect (f : α → β) (hf : Function.Injective f)
    (F : Formula α) (z : ℕ → ℕ) (d : ℕ)
    (h : InsertionInvariant.MinimumWidth z (formulaSet (F.map (List.map f))) d) :
    InsertionInvariant.MinimumWidth z (formulaSet F) d := by
  rw [formulaSet_map] at h
  exact minimumWidth_reflect f hf (formulaSet F) z d h

/-- The encoded search's local outputs produce exactly the certified choice
used by the existing path-charging and decomposition proofs. -/
theorem typed_choice {n : ℕ} (f : SAT.Literal (Fin n) → β)
    (hf : Function.Injective f) (F : Formula (SAT.Literal (Fin n)))
    (G : Formula β) (H : Clause β) (z : ℕ → ℕ) (k d : ℕ)
    (hdlo : 2 ≤ d) (hdhi : d ≤ k) (hz : 2 ≤ z d)
    (hG : G ⊆ F.map (List.map f))
    (hflower : Sunflower.IsSunflowerWithCore (formulaSet G) (clauseSet H))
    (hcore : (clauseSet H).Nonempty) (hcard : (formulaSet G).card = z d)
    (hwidth : ∀ C ∈ formulaSet G, C.card = d)
    (hminimum : InsertionInvariant.MinimumWidth z (formulaSet (F.map (List.map f))) d) :
    ∃ c : Sparsify.Choice (formulaSet F) z k,
      c.width = d ∧ c.flower.core.image f = clauseSet H ∧
      (SunflowerBranch.clauses c.flower.core c.flower.petals).image (Finset.image f) =
        formulaSet G := by
  have htwo : 2 ≤ (formulaSet G).card := by rw [hcard]; exact hz
  obtain ⟨A, K, _, hmapA, hmapK, s, hsK, hsA, hsub, hsize⟩ :=
    typed_sunflower f hf F G H d hG hflower hcore htwo hwidth
  let c : Sparsify.Choice (formulaSet F) z k :=
    ⟨d, hdlo, hdhi, s, hsub, hsize.trans hcard,
      minimumWidth_codes_reflect f hf F z d hminimum⟩
  refine ⟨c, rfl, ?_, ?_⟩
  · change s.core.image f = clauseSet H
    rw [hsK, ← clauseSet_map, hmapK]
  · change (SunflowerBranch.clauses s.core s.petals).image (Finset.image f) = formulaSet G
    rw [hsA, ← formulaSet_map, hmapA]

end SubexponentialSAT.ExecSunflowerCodeTransport

end OAI.Algorithms
