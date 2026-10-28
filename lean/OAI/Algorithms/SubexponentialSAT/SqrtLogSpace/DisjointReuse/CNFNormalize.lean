import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CountModel
import Mathlib.Data.Finset.Powerset

/-!
Raw input normalization for the frozen counting manuscript, lines 1758–1762.
The ambient type remains `Fin n` throughout, including unused variables.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

variable {n : ℕ}

/-- List multiplicities have exactly the usual disjunction/conjunction semantics. -/
theorem eval_formulaSet (a : SAT.Assignment (Fin n)) (F : RawCNF n) :
    SAT.CNF.eval a (ExecCNF.formulaSet F) =
      F.all (fun C => C.any (fun l => l.eval a)) := by
  apply Bool.eq_iff_iff.mpr
  simp [SAT.CNF.eval_eq_true, SAT.Clause.eval_eq_true, ExecCNF.formulaSet,
    ExecCNF.clauseSet, List.all_eq_true, List.any_eq_true]

theorem rawCount_eq_card_satisfying (F : RawCNF n) :
    rawCount F =
      (Finset.univ.filter fun a : Fin n → Bool =>
        F.all (fun C => C.any (fun l => l.eval a)) = true).card := by
  simp only [rawCount, SAT.count, SAT.satisfyingAssignments, eval_formulaSet]

/-- No variable restriction or unit propagation occurs in this normalization. -/
theorem rawCount_normalize (F : RawCNF n) :
    rawCount (ExecCNF.normalize SAT.Literal.negate F) = rawCount F := by
  simp only [rawCount, ExecCNF.normalize_set, SAT.count_normalize]

theorem rawCount_nil : rawCount ([] : RawCNF n) = 2 ^ n := by
  simp [rawCount, SAT.count, SAT.satisfyingAssignments, SAT.Assignment]

theorem rawCount_eq_zero_of_empty_mem (F : RawCNF n) (h : [] ∈ F) :
    rawCount F = 0 := by
  apply (SAT.count_eq_zero_iff _).mpr
  apply SAT.not_satisfiable_of_empty_mem
  exact ExecCNF.mem_formulaSet.mpr ⟨[], h, rfl⟩

theorem formulaSet_card_le_length (F : RawCNF n) :
    (ExecCNF.formulaSet F).card ≤ F.length := by
  simpa only [ExecCNF.formulaSet, List.length_map] using
    (F.map ExecCNF.clauseSet).toFinset_card_le

theorem formulaSet_width_le (F : RawCNF n) {k : ℕ}
    (h : ∀ C ∈ F, C.length ≤ k) : SAT.WidthAtMost k (ExecCNF.formulaSet F) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := ExecCNF.mem_formulaSet.mp hC
  exact D.toFinset_card_le.trans (h D hD)

theorem normalize_width_le (F : RawCNF n) {k : ℕ}
    (h : ∀ C ∈ F, C.length ≤ k) :
    ∀ C ∈ ExecCNF.normalize SAT.Literal.negate F, C.length ≤ k := by
  intro C hC
  have h₁ := ExecCNF.absorb_subset _ hC
  have h₂ := (List.mem_filter.mp h₁).1
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h₂
  exact (ExecCNF.dedupLiterals_length_le D).trans (h D hD)

/-- Raw repetitions remain charged in the encoded input length. -/
theorem encodeRawCNF_length_upper (F : RawCNF n) {k : ℕ}
    (h : ∀ C ∈ F, C.length ≤ k) :
    (encodeRawCNF F).length ≤ n + 2 + (4 + (8 * n + 8) * k) * F.length := by
  have hC (C : List (SAT.Literal (Fin n))) (hC : C ∈ F) :
      (Encoding.encodeList Encoding.encodeNat (C.map Encoding.literalCode)).length ≤
        1 + (4 * n + 4) * k := by
    have hL := Encoding.length_encodeList_upper Encoding.encodeNat
      (C.map Encoding.literalCode) (2 * n + 1) (by
        intro a ha
        obtain ⟨l, _, rfl⟩ := List.mem_map.mp ha
        rw [Encoding.length_encodeNat]
        have := Encoding.literalCode_lt l
        omega)
    have hK := h C hC
    simp only [List.length_map,
      show 2 * (2 * n + 1) + 2 = 4 * n + 4 by omega] at hL
    exact hL.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hK) _)
  have hF := Encoding.length_encodeList_upper (Encoding.encodeList Encoding.encodeNat)
    (F.map (List.map Encoding.literalCode)) (1 + (4 * n + 4) * k) (by
      intro C hC'
      obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC'
      exact hC D hD)
  have hE : 2 * (1 + (4 * n + 4) * k) + 2 = 4 + (8 * n + 8) * k := by ring
  simp only [List.length_map, hE] at hF
  simp only [encodeRawCNF, List.length_append, Encoding.length_encodeNat]
  omega

theorem normalized_formulaBitLength_upper (F : RawCNF n) {k : ℕ}
    (h : ∀ C ∈ F, C.length ≤ k) :
    Encoding.formulaBitLength (SAT.normalize (ExecCNF.formulaSet F)) ≤
      n + 2 + (4 + (8 * n + 8) * k) * F.length := by
  apply (Encoding.formulaBitLength_upper _
    (SAT.widthAtMost_of_subset (SAT.normalize_subset _) (formulaSet_width_le F h))).trans
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _
    ((Finset.card_le_card (SAT.normalize_subset _)).trans (formulaSet_card_le_length F))) _

/-- For fixed width the complete raw binary input has quadratic size in `n + m`. -/
theorem encodeRawCNF_length_polynomial (F : RawCNF n) {k : ℕ} (hn : 1 ≤ n)
    (h : ∀ C ∈ F, C.length ≤ k) :
    (encodeRawCNF F).length ≤ (16 * k + 7) * (n + F.length) ^ 2 := by
  let s := n + F.length
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hn' : n ≤ s := Nat.le_add_right _ _
  have hm : F.length ≤ s := Nat.le_add_left _ _
  have hsq : s ≤ s * s := by
    simpa using Nat.mul_le_mul_left s hs
  have hhead : n + 2 ≤ 3 * (s * s) :=
    (show n + 2 ≤ 3 * s by omega).trans (Nat.mul_le_mul_left 3 hsq)
  have hc : 4 + (8 * n + 8) * k ≤ (16 * k + 4) * s := by
    calc
      4 + (8 * n + 8) * k ≤ 4 * s + (16 * s) * k :=
        Nat.add_le_add (by omega) (Nat.mul_le_mul_right k (by omega))
      _ = (16 * k + 4) * s := by ring
  have hbody := Nat.mul_le_mul hc hm
  apply (encodeRawCNF_length_upper F h).trans
  calc
    n + 2 + (4 + (8 * n + 8) * k) * F.length
        ≤ 3 * (s * s) + ((16 * k + 4) * s) * s := Nat.add_le_add hhead hbody
    _ = (16 * k + 7) * (n + F.length) ^ 2 := by dsimp [s]; ring

/-- Normalization bounds the output language for fixed declared `n`, even with
arbitrarily many raw repetitions and without a width promise. -/
theorem encodeRawCNF_normalize_length_bound (F : RawCNF n) :
    (encodeRawCNF (ExecCNF.normalize SAT.Literal.negate F)).length ≤
      n + 2 + (4 + (8 * n + 8) * (2 * n)) * 2 ^ (2 * n) := by
  have hcodes (C : SAT.Clause (Fin n)) :
      C.image Encoding.literalCode ⊆ Finset.range (2 * n) := by
    intro i hi
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (Encoding.literalCode_lt l)
  have hwidth : ∀ C ∈ ExecCNF.normalize SAT.Literal.negate F, C.length ≤ 2 * n := by
    intro C hC
    calc
      C.length = C.toFinset.card :=
        (List.toFinset_card_of_nodup
          (ExecCNF.normalize_literal_nodup SAT.Literal.negate F C hC)).symm
      _ = (C.toFinset.image Encoding.literalCode).card :=
        (Finset.card_image_of_injective _ Encoding.literalCode_injective).symm
      _ ≤ (Finset.range (2 * n)).card := Finset.card_le_card (hcodes C.toFinset)
      _ = 2 * n := Finset.card_range _
  have hlength : (ExecCNF.normalize SAT.Literal.negate F).length ≤ 2 ^ (2 * n) := by
    rw [ExecCNF.normalize_length_eq_card]
    calc
      (ExecCNF.formulaSet (ExecCNF.normalize SAT.Literal.negate F)).card =
          ((ExecCNF.formulaSet (ExecCNF.normalize SAT.Literal.negate F)).image
            (Finset.image Encoding.literalCode)).card :=
        (Finset.card_image_of_injective _
          (Finset.image_injective Encoding.literalCode_injective)).symm
      _ ≤ (Finset.range (2 * n)).powerset.card := by
        apply Finset.card_le_card
        intro C hC
        obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hC
        exact Finset.mem_powerset.mpr (hcodes D)
      _ = 2 ^ (2 * n) := by simp
  exact (encodeRawCNF_length_upper _ hwidth).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlength) _)

private theorem encodeList_length_perm {α : Type*} (enc : α → List Bool)
    {as bs : List α} (h : as.Perm bs) :
    (Encoding.encodeList enc as).length = (Encoding.encodeList enc bs).length := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [Encoding.length_encodeList_cons, ih]
  | swap a b as => simp only [Encoding.length_encodeList_cons]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem encodeList_length_map_congr {α β γ : Type*}
    (enc₁ : β → List Bool) (enc₂ : γ → List Bool) (f : α → β) (g : α → γ)
    (as : List α) (h : ∀ a ∈ as, (enc₁ (f a)).length = (enc₂ (g a)).length) :
    (Encoding.encodeList enc₁ (as.map f)).length =
      (Encoding.encodeList enc₂ (as.map g)).length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, Encoding.length_encodeList_cons]
      rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- Sorting literals and clauses changes their order but not the serialized size.
The hypotheses exclude both literal repetitions and semantically duplicate clauses. -/
theorem encodeRawCNFBody_length_eq (F : RawCNF n)
    (hC : ∀ C ∈ F, C.Nodup) (hF : (F.map ExecCNF.clauseSet).Nodup) :
    (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
      (F.map (List.map Encoding.literalCode))).length =
      (Encoding.encodeCNFBody (ExecCNF.formulaSet F)).length := by
  have hclause (C : List (SAT.Literal (Fin n))) (h : C ∈ F) :
      (C.map Encoding.literalCode).Perm (Encoding.clauseNumbers (ExecCNF.clauseSet C)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
      ((hC C h).map Encoding.literalCode_injective) (Finset.sort_nodup _ _)
    ext i
    simp [ExecCNF.clauseSet]
  have hformula : ((F.map ExecCNF.clauseSet).map Encoding.clauseNumbers).Perm
      (Encoding.cnfNumbers (ExecCNF.formulaSet F)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
      (hF.map Encoding.clauseNumbers_injective) (Finset.sort_nodup _ _)
    ext C
    simp [ExecCNF.formulaSet]
  calc
    (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
        (F.map (List.map Encoding.literalCode))).length =
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
          ((F.map ExecCNF.clauseSet).map Encoding.clauseNumbers)).length := by
      rw [List.map_map]
      apply encodeList_length_map_congr
      intro C h
      exact encodeList_length_perm Encoding.encodeNat (hclause C h)
    _ = (Encoding.encodeCNFBody (ExecCNF.formulaSet F)).length :=
      encodeList_length_perm _ hformula

theorem encodeRawCNF_length_eq_formulaBitLength (F : RawCNF n)
    (hC : ∀ C ∈ F, C.Nodup) (hF : (F.map ExecCNF.clauseSet).Nodup) :
    (encodeRawCNF F).length = Encoding.formulaBitLength (ExecCNF.formulaSet F) := by
  simp only [encodeRawCNF, List.length_append, Encoding.length_encodeNat,
    Encoding.formulaBitLength_eq, encodeRawCNFBody_length_eq F hC hF]

theorem encodeRawCNF_normalize_length_eq_formulaBitLength (F : RawCNF n) :
    (encodeRawCNF (ExecCNF.normalize SAT.Literal.negate F)).length =
      Encoding.formulaBitLength (SAT.normalize (ExecCNF.formulaSet F)) := by
  rw [encodeRawCNF_length_eq_formulaBitLength _
    (ExecCNF.normalize_literal_nodup _ _) (ExecCNF.normalize_map_nodup _ _),
    ExecCNF.normalize_set]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
