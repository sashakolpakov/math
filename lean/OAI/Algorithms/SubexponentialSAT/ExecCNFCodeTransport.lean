import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecQuantitativeSparsify
import OAI.Algorithms.SubexponentialSAT.SubexpFrontend

namespace OAI.Algorithms

/-!
# Exact list transport through literal codes

These equalities preserve clause order and the last-occurrence conventions.
They connect the encoded normalization programs to the typed executable CNF
operations, rather than identifying only their finite-set semantics.
-/

namespace SubexponentialSAT.ExecCNFCodeTransport

open ExecCNF

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

@[simp] theorem contains_map (f : α → β) (hf : Function.Injective f)
    (x : α) (C : Clause α) : contains (f x) (C.map f) = contains x C := by
  induction C with
  | nil => rfl
  | cons y ys ih => simp [contains, hf.eq_iff, ih]

@[simp] theorem subset_map (f : α → β) (hf : Function.Injective f)
    (C D : Clause α) : subset (C.map f) (D.map f) = subset C D := by
  induction C with
  | nil => rfl
  | cons x xs ih => simp [subset, contains_map f hf, ih]

@[simp] theorem equivalent_map (f : α → β) (hf : Function.Injective f)
    (C D : Clause α) : equivalent (C.map f) (D.map f) = equivalent C D := by
  simp [equivalent, subset_map f hf]

@[simp] theorem strictSubset_map (f : α → β) (hf : Function.Injective f)
    (C D : Clause α) : strictSubset (C.map f) (D.map f) = strictSubset C D := by
  simp [strictSubset, subset_map f hf]

@[simp] theorem dedupLiterals_map (f : α → β) (hf : Function.Injective f)
    (C : Clause α) : dedupLiterals (C.map f) = (dedupLiterals C).map f := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, dedupLiterals, contains_map f hf]
      split <;> simp_all

@[simp] theorem dedupClauses_map (f : α → β) (hf : Function.Injective f)
    (F : Formula α) : dedupClauses (F.map (List.map f)) =
      (dedupClauses F).map (List.map f) := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      simp only [List.map_cons, dedupClauses, List.any_map, Function.comp_def,
        equivalent_map f hf]
      split <;> simp_all

@[simp] theorem cleanLiterals_map (f : α → β) (hf : Function.Injective f)
    (F : Formula α) : cleanLiterals (F.map (List.map f)) =
      (cleanLiterals F).map (List.map f) := by
  simp [cleanLiterals, List.map_map, Function.comp_def, dedupLiterals_map f hf]

@[simp] theorem tautology_map (f : α → β) (hf : Function.Injective f)
    (negα : α → α) (negβ : β → β) (hn : ∀ x, f (negα x) = negβ (f x))
    (C : Clause α) : tautology negβ (C.map f) = tautology negα C := by
  simp only [tautology, List.any_map, Function.comp_def, ← hn, contains_map f hf]

omit [DecidableEq α] [DecidableEq β] in
private theorem filter_map_comm (f : α → β) (p : α → Bool) (q : β → Bool)
    (h : ∀ x, q (f x) = p x) (L : List α) :
    (L.map f).filter q = (L.filter p).map f := by
  induction L with
  | nil => rfl
  | cons x xs ih => cases hx : p x <;> simp [ h, hx, ih]

@[simp] theorem removeTautologies_map (f : α → β) (hf : Function.Injective f)
    (negα : α → α) (negβ : β → β) (hn : ∀ x, f (negα x) = negβ (f x))
    (F : Formula α) : removeTautologies negβ (F.map (List.map f)) =
      (removeTautologies negα F).map (List.map f) := by
  apply filter_map_comm (List.map f)
  intro C
  simp only [tautology_map f hf negα negβ hn]

@[simp] theorem absorb_map (f : α → β) (hf : Function.Injective f)
    (F : Formula α) : absorb (F.map (List.map f)) = (absorb F).map (List.map f) := by
  unfold absorb
  rw [dedupClauses_map f hf]
  apply filter_map_comm (List.map f)
  intro C
  simp only [List.any_map, Function.comp_def, strictSubset_map f hf]

@[simp] theorem normalize_map (f : α → β) (hf : Function.Injective f)
    (negα : α → α) (negβ : β → β) (hn : ∀ x, f (negα x) = negβ (f x))
    (F : Formula α) : ExecCNF.normalize negβ (F.map (List.map f)) =
      (ExecCNF.normalize negα F).map (List.map f) := by
  simp only [ExecCNF.normalize, cleanLiterals_map f hf,
    removeTautologies_map f hf negα negβ hn, absorb_map f hf]

@[simp] theorem eraseClauses_map (f : α → β) (hf : Function.Injective f)
    (F S : Formula α) : eraseClauses (F.map (List.map f)) (S.map (List.map f)) =
      (eraseClauses F S).map (List.map f) := by
  apply filter_map_comm (List.map f)
  intro C
  simp only [List.any_map, Function.comp_def, equivalent_map f hf]

omit [DecidableEq α] [DecidableEq β] in
@[simp] theorem clauses_map (f : α → β) (H : Clause α) (P : Formula α) :
    clauses (H.map f) (P.map (List.map f)) = (clauses H P).map (List.map f) := by
  simp [clauses, List.map_map, Function.comp_def]

@[simp] theorem childA_map (f : α → β) (hf : Function.Injective f)
    (F : Formula α) (H : Clause α) (P : Formula α) :
    childA (F.map (List.map f)) (H.map f) (P.map (List.map f)) =
      (childA F H P).map (List.map f) := by
  simp only [childA, clauses_map, eraseClauses_map f hf, ← List.map_cons, absorb_map f hf]

@[simp] theorem childB_map (f : α → β) (hf : Function.Injective f)
    (F : Formula α) (H : Clause α) (P : Formula α) :
    childB (F.map (List.map f)) (H.map f) (P.map (List.map f)) =
      (childB F H P).map (List.map f) := by
  simp only [childB, clauses_map, eraseClauses_map f hf, ← List.map_append, absorb_map f hf]

theorem dedupLiterals_eq_of_nodup (C : Clause α) (hC : C.Nodup) : dedupLiterals C = C := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hC
      have h : ¬ contains x xs = true := by simpa only [contains_true] using hx
      simp only [dedupLiterals, ite_eq_right h, ih hxs]

theorem cleanLiterals_eq_of_nodup (F : Formula α) (hF : ∀ C ∈ F, C.Nodup) :
    cleanLiterals F = F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      simp only [cleanLiterals, List.map_cons]
      rw [dedupLiterals_eq_of_nodup C (hF C (by simp))]
      congr 1
      exact ih (fun D hD => hF D (by simp [hD]))

@[simp] theorem cleanLiterals_normalize (neg : α → α) (F : Formula α) :
    cleanLiterals (normalize neg F) = normalize neg F :=
  cleanLiterals_eq_of_nodup _ (normalize_literal_nodup neg F)

/-- The extra pass in the typed worklist does not alter order or multiplicity. -/
theorem normalizedInput_eq_normalize {n : ℕ}
    (F : Formula (SAT.Literal (Fin n))) :
    ExecSparsifyWorklist.normalizedInput F = normalize SAT.Literal.negate F := by
  exact cleanLiterals_normalize SAT.Literal.negate F

/-- Exact encoded normalization, including last-occurrence choices and order. -/
theorem normalize_literalCode {n : ℕ} (F : Formula (SAT.Literal (Fin n))) :
    normalize SubexpFrontend.negateCode (F.map (List.map Encoding.literalCode)) =
      (normalize SAT.Literal.negate F).map (List.map Encoding.literalCode) :=
  normalize_map Encoding.literalCode Encoding.literalCode_injective
    SAT.Literal.negate SubexpFrontend.negateCode SubexpFrontend.literalCode_negate F

/-- This is the list-level interface consumed by the actual normalizer. -/
theorem normalizedInput_literalCode {n : ℕ} (F : Formula (SAT.Literal (Fin n))) :
    (ExecSparsifyWorklist.normalizedInput F).map (List.map Encoding.literalCode) =
      normalize SubexpFrontend.negateCode (F.map (List.map Encoding.literalCode)) := by
  rw [normalizedInput_eq_normalize, normalize_literalCode]

/-- The actual petal filter commutes with injective literal encoding. -/
theorem petal_filter_map (f : α → β) (hf : Function.Injective f)
    (C H : Clause α) :
    (C.map f).filter (fun x => !decide (x ∈ H.map f)) =
      (C.filter (fun x => !decide (x ∈ H))).map f := by
  apply filter_map_comm f
  intro x
  simp [List.mem_map, hf.eq_iff]

theorem petal_filter_set (C H : Clause α) :
    clauseSet (C.filter (fun x => !decide (x ∈ H))) = clauseSet C \ clauseSet H := by
  ext x
  simp [clauseSet]

theorem petal_family_map (f : α → β) (hf : Function.Injective f)
    (G : Formula α) (H : Clause α) :
    (G.map (List.map f)).map (fun C => C.filter (fun x => !decide (x ∈ H.map f))) =
      (G.map (fun C => C.filter (fun x => !decide (x ∈ H)))).map (List.map f) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro C _
  exact petal_filter_map f hf C H

theorem petal_family_set (G : Formula α) (H : Clause α) :
    formulaSet (G.map (fun C => C.filter (fun x => !decide (x ∈ H)))) =
      (formulaSet G).image (fun C => C \ clauseSet H) := by
  ext D
  constructor
  · intro hD
    obtain ⟨C, hC, he⟩ := mem_formulaSet.mp hD
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hC
    exact Finset.mem_image.mpr ⟨clauseSet A, mem_formulaSet.mpr ⟨A, hA, rfl⟩,
      (petal_filter_set A H).symm.trans he⟩
  · intro hD
    obtain ⟨C, hC, he⟩ := Finset.mem_image.mp hD
    obtain ⟨A, hA, rfl⟩ := mem_formulaSet.mp hC
    exact mem_formulaSet.mpr ⟨A.filter (fun x => !decide (x ∈ H)),
      List.mem_map.mpr ⟨A, hA, rfl⟩, (petal_filter_set A H).trans he⟩

/-- The canonical external syntax reaches exactly the same ordered leaf input. -/
theorem normalized_formulaList_codes {n : ℕ} (F : SAT.CNF (Fin n)) :
    (ExecSparsifyWorklist.normalizedInput (ExecQuantitativeSparsify.formulaList F)).map
        (List.map Encoding.literalCode) =
      normalize SubexpFrontend.negateCode (Encoding.cnfNumbers F) := by
  rw [normalizedInput_literalCode, ExecQuantitativeSparsify.formulaList_codes]

theorem encode_normalized_formulaList {n : ℕ} (F : SAT.CNF (Fin n)) :
    ExecQuantitativeSparsify.encodeRawFormula
        (ExecSparsifyWorklist.normalizedInput (ExecQuantitativeSparsify.formulaList F)) =
      Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
        (normalize SubexpFrontend.negateCode (Encoding.cnfNumbers F)) := by
  rw [ExecQuantitativeSparsify.encodeRawFormula, normalized_formulaList_codes]

end SubexponentialSAT.ExecCNFCodeTransport

end OAI.Algorithms
