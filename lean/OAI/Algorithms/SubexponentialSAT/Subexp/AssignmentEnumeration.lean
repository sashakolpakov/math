import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalExpectation
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearch

namespace OAI.Algorithms

/-!
# Explicit enumerations for the conditional-expectation assignment

Words are enumerated by a finite recursion over the alphabet `List.finRange r`.
Seed indices are enumerated from supplied factor and vertex lists. Numeric
codes use `idxOf`, and inverse lookups use the same lists. No arbitrary finite
equivalence or choice operator occurs in these executable definitions.
-/

namespace SubexponentialSAT.Subexp.AssignmentEnumeration

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpTypeVariance SubexponentialSAT.SlotAssignment

section Tuples

variable {α : Type*}

/-- Distinct alphabet entries and distinct tails give distinct tuples. -/
theorem tuples_nodup (alphabet : List α) (hn : alphabet.Nodup) (Q : ℕ) :
    (CoefficientSearch.tuples alphabet Q).Nodup := by
  induction Q with
  | zero => simp [CoefficientSearch.tuples]
  | succ Q ih =>
    rw [CoefficientSearch.tuples, List.nodup_flatMap]
    refine ⟨fun a _ => ih.map (by
      intro x y h
      exact (Fin.cons_inj.mp h).2), ?_⟩
    apply hn.imp
    intro a b hab f hfa hfb
    obtain ⟨x, _, hxf⟩ := List.mem_map.mp hfa
    obtain ⟨y, _, hyf⟩ := List.mem_map.mp hfb
    exact hab (Fin.cons_inj.mp (hxf.trans hyf.symm)).1

end Tuples

/-- The complete word alphabet, in the recursion's explicit lexicographic order. -/
def wordAlphabet (r Q : ℕ) : List (Word r Q) :=
  CoefficientSearch.tuples (List.finRange r) Q

@[simp] theorem wordAlphabet_length (r Q : ℕ) :
    (wordAlphabet r Q).length = r ^ Q := by
  simp [wordAlphabet]

theorem wordAlphabet_nodup (r Q : ℕ) : (wordAlphabet r Q).Nodup :=
  tuples_nodup _ (List.nodup_finRange r) Q

theorem mem_wordAlphabet (r Q : ℕ) (w : Word r Q) : w ∈ wordAlphabet r Q :=
  CoefficientSearch.mem_tuples _ (fun _ => List.mem_finRange _) Q w

/-- Explicit default for a nonempty color alphabet. -/
def zeroWord (r Q : ℕ) (hr : 0 < r) : Word r Q := fun _ => ⟨0, hr⟩

theorem wordAlphabet_ne_nil (r Q : ℕ) (hr : 0 < r) : wordAlphabet r Q ≠ [] :=
  List.ne_nil_of_mem (mem_wordAlphabet r Q (zeroWord r Q hr))

/-- Head and tail supplied to the existing sequential choice procedure. -/
def firstWord (r Q : ℕ) (hr : 0 < r) : Word r Q :=
  (wordAlphabet r Q).headD (zeroWord r Q hr)

def remainingWords (r Q : ℕ) : List (Word r Q) := (wordAlphabet r Q).tail

theorem firstWord_cons_remaining (r Q : ℕ) (hr : 0 < r) :
    firstWord r Q hr :: remainingWords r Q = wordAlphabet r Q := by
  have hne := wordAlphabet_ne_nil r Q hr
  unfold firstWord remainingWords
  cases h : wordAlphabet r Q with
  | nil => exact False.elim (hne h)
  | cons w ws => rfl

theorem choices_nodup (r Q : ℕ) (hr : 0 < r) :
    (firstWord r Q hr :: remainingWords r Q).Nodup := by
  rw [firstWord_cons_remaining]
  exact wordAlphabet_nodup r Q

theorem choices_complete (r Q : ℕ) (hr : 0 < r) (w : Word r Q) :
    w ∈ firstWord r Q hr :: remainingWords r Q := by
  rw [firstWord_cons_remaining]
  exact mem_wordAlphabet r Q w

@[simp] theorem choices_length (r Q : ℕ) (hr : 0 < r) :
    (firstWord r Q hr :: remainingWords r Q).length = r ^ Q := by
  rw [firstWord_cons_remaining, wordAlphabet_length]

/-- Numeric word codes are exactly the positions used by `indexCode`. -/
def wordCode (r Q : ℕ) (w : Word r Q) : ℕ :=
  SubexponentialSAT.LocalExpectation.indexCode (wordAlphabet r Q) w

theorem wordCode_lt (r Q : ℕ) (w : Word r Q) : wordCode r Q w < r ^ Q := by
  have h := List.idxOf_lt_length_iff.mpr (mem_wordAlphabet r Q w)
  simpa only [wordCode, SubexponentialSAT.LocalExpectation.indexCode, wordAlphabet_length] using h

def wordCodeFin (r Q : ℕ) (w : Word r Q) : Fin (r ^ Q) :=
  ⟨wordCode r Q w, wordCode_lt r Q w⟩

/-- Bounded word lookup in the actual enumeration. -/
def wordAt (r Q : ℕ) (j : Fin (r ^ Q)) : Word r Q :=
  (wordAlphabet r Q).get ⟨j.val, by simpa only [wordAlphabet_length] using j.isLt⟩

/-- Partial lookup is available when a caller holds only a natural number. -/
def wordAt? (r Q n : ℕ) : Option (Word r Q) := (wordAlphabet r Q)[n]?

@[simp] theorem wordAt_wordCode (r Q : ℕ) (w : Word r Q) :
    wordAt r Q (wordCodeFin r Q w) = w := by
  simp [wordAt, wordCodeFin, wordCode, SubexponentialSAT.LocalExpectation.indexCode]

@[simp] theorem wordCode_wordAt (r Q : ℕ) (j : Fin (r ^ Q)) :
    wordCodeFin r Q (wordAt r Q j) = j := by
  apply Fin.ext
  exact (wordAlphabet_nodup r Q).idxOf_getElem j.val _

@[simp] theorem wordAt?_wordCode (r Q : ℕ) (w : Word r Q) :
    wordAt? r Q (wordCode r Q w) = some w :=
  List.getElem?_idxOf (mem_wordAlphabet r Q w)

/-- An explicit index equivalence whose two functions are lookup and `idxOf`. -/
def wordIndexEquiv (r Q : ℕ) : Fin (r ^ Q) ≃ Word r Q where
  toFun := wordAt r Q
  invFun := wordCodeFin r Q
  left_inv := wordCode_wordAt r Q
  right_inv := wordAt_wordCode r Q

/-- Explicitly enumerate a head word and all slot words. -/
def universalAlphabet (r Q Δ : ℕ) : List (UniversalType r Q Δ) :=
  ((wordAlphabet r Q).product (CoefficientSearch.tuples (wordAlphabet r Q) Δ)).map
    (equivProd r Q Δ).symm

theorem universalAlphabet_nodup (r Q Δ : ℕ) : (universalAlphabet r Q Δ).Nodup :=
  ((wordAlphabet_nodup r Q).product
    (tuples_nodup _ (wordAlphabet_nodup r Q) Δ)).map (equivProd r Q Δ).symm.injective

theorem mem_universalAlphabet (r Q Δ : ℕ) (u : UniversalType r Q Δ) :
    u ∈ universalAlphabet r Q Δ := by
  apply List.mem_map.mpr
  refine ⟨(u.head, u.slot), List.mem_product.mpr ⟨mem_wordAlphabet r Q u.head, ?_⟩, rfl⟩
  exact CoefficientSearch.mem_tuples _ (mem_wordAlphabet r Q) Δ u.slot

@[simp] theorem universalAlphabet_length (r Q Δ : ℕ) :
    (universalAlphabet r Q Δ).length = r ^ (Q * (Δ + 1)) := by
  simp only [universalAlphabet, List.length_map]
  have hp : ((wordAlphabet r Q).product
      (CoefficientSearch.tuples (wordAlphabet r Q) Δ)).length =
      (wordAlphabet r Q).length *
        (CoefficientSearch.tuples (wordAlphabet r Q) Δ).length := List.length_product _ _
  rw [hp, CoefficientSearch.tuples_length, wordAlphabet_length, pow_mul, pow_succ]
  exact Nat.mul_comm _ _

section SumLists

variable {α β : Type*}

/-- List the left summand followed by the right summand. -/
def sumList (as : List α) (bs : List β) : List (α ⊕ β) :=
  as.map Sum.inl ++ bs.map Sum.inr

@[simp] theorem sumList_length (as : List α) (bs : List β) :
    (sumList as bs).length = as.length + bs.length := by simp [sumList]

theorem sumList_nodup (as : List α) (bs : List β)
    (ha : as.Nodup) (hb : bs.Nodup) : (sumList as bs).Nodup := by
  apply List.Nodup.append (ha.map Sum.inl_injective) (hb.map Sum.inr_injective)
  intro x hx hy
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b, _, h⟩ := List.mem_map.mp hy
  cases h

theorem sumList_complete (as : List α) (bs : List β)
    (ha : ∀ a, a ∈ as) (hb : ∀ b, b ∈ bs) (x : α ⊕ β) : x ∈ sumList as bs := by
  cases x <;> simp [sumList, ha, hb]

end SumLists

section Seeds

variable {V E : Type*}

/-- Factors, vertex heads, then all vertex/slot padding words. -/
def seedIndices (vertices : List V) (factors : List E) (Δ : ℕ) :
    List (SeedIndex V E Δ) :=
  sumList factors (sumList vertices (vertices.product (List.finRange Δ)))

theorem seedIndices_nodup (vertices : List V) (factors : List E) (Δ : ℕ)
    (hv : vertices.Nodup) (he : factors.Nodup) :
    (seedIndices vertices factors Δ).Nodup :=
  sumList_nodup _ _ he
    (sumList_nodup _ _ hv (hv.product (List.nodup_finRange Δ)))

theorem mem_seedIndices (vertices : List V) (factors : List E) (Δ : ℕ)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors) (s : SeedIndex V E Δ) :
    s ∈ seedIndices vertices factors Δ := by
  apply sumList_complete _ _ he
  apply sumList_complete _ _ hv
  intro x
  exact List.mem_product.mpr ⟨hv x.1, List.mem_finRange x.2⟩

@[simp] theorem seedIndices_length (vertices : List V) (factors : List E) (Δ : ℕ) :
    (seedIndices vertices factors Δ).length =
      factors.length + (Δ + 1) * vertices.length := by
  simp only [seedIndices, sumList_length]
  have hp : (vertices.product (List.finRange Δ)).length =
      vertices.length * (List.finRange Δ).length := List.length_product _ _
  rw [hp, List.length_finRange]
  ring

theorem enumeration_length [Fintype V] [DecidableEq V]
    (vertices : List V) (hn : vertices.Nodup) (hc : ∀ v, v ∈ vertices) :
    vertices.length = Fintype.card V := by
  rw [← List.toFinset_card_of_nodup hn]
  have h : vertices.toFinset = Finset.univ := by ext v; simp [hc v]
  rw [h, Finset.card_univ]

theorem seedIndices_length_card [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (vertices : List V) (factors : List E) (Δ : ℕ)
    (hvn : vertices.Nodup) (hvc : ∀ v, v ∈ vertices)
    (hen : factors.Nodup) (hec : ∀ e, e ∈ factors) :
    (seedIndices vertices factors Δ).length =
      Fintype.card E + (Δ + 1) * Fintype.card V := by
  rw [seedIndices_length, enumeration_length vertices hvn hvc,
    enumeration_length factors hen hec]

variable [DecidableEq V] [DecidableEq E]

def seedCode (vertices : List V) (factors : List E) (Δ : ℕ)
    (s : SeedIndex V E Δ) : ℕ :=
  SubexponentialSAT.LocalExpectation.indexCode (seedIndices vertices factors Δ) s

def seedAt? (vertices : List V) (factors : List E) (Δ n : ℕ) :
    Option (SeedIndex V E Δ) := (seedIndices vertices factors Δ)[n]?

theorem seedAt?_seedCode (vertices : List V) (factors : List E) (Δ : ℕ)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors) (s : SeedIndex V E Δ) :
    seedAt? vertices factors Δ (seedCode vertices factors Δ s) = some s := by
  let _ : BEq (SeedIndex V E Δ) := instBEqOfDecidableEq
  exact List.getElem?_idxOf (mem_seedIndices vertices factors Δ hv he s)

theorem seedCode_lt (vertices : List V) (factors : List E) (Δ : ℕ)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors) (s : SeedIndex V E Δ) :
    seedCode vertices factors Δ s < factors.length + (Δ + 1) * vertices.length := by
  let _ : BEq (SeedIndex V E Δ) := instBEqOfDecidableEq
  have h := List.idxOf_lt_length_iff.mpr (mem_seedIndices vertices factors Δ hv he s)
  simpa only [seedCode, SubexponentialSAT.LocalExpectation.indexCode, seedIndices_length] using h

def seedCodeFin (vertices : List V) (factors : List E) (Δ : ℕ)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors) (s : SeedIndex V E Δ) :
    Fin (factors.length + (Δ + 1) * vertices.length) :=
  ⟨seedCode vertices factors Δ s, seedCode_lt vertices factors Δ hv he s⟩

def seedAt (vertices : List V) (factors : List E) (Δ : ℕ)
    (n : Fin (factors.length + (Δ + 1) * vertices.length)) : SeedIndex V E Δ :=
  (seedIndices vertices factors Δ).get
    ⟨n.val, by simpa only [seedIndices_length] using n.isLt⟩

@[simp] theorem seedAt_seedCode (vertices : List V) (factors : List E) (Δ : ℕ)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors) (s : SeedIndex V E Δ) :
    seedAt vertices factors Δ (seedCodeFin vertices factors Δ hv he s) = s := by
  let _ : BEq (SeedIndex V E Δ) := instBEqOfDecidableEq
  simp [seedAt, seedCodeFin, seedCode, SubexponentialSAT.LocalExpectation.indexCode]

@[simp] theorem seedCode_seedAt (vertices : List V) (factors : List E) (Δ : ℕ)
    (hvn : vertices.Nodup) (hen : factors.Nodup)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (n : Fin (factors.length + (Δ + 1) * vertices.length)) :
    seedCodeFin vertices factors Δ hv he (seedAt vertices factors Δ n) = n := by
  apply Fin.ext
  let _ : BEq (SeedIndex V E Δ) := instBEqOfDecidableEq
  exact (seedIndices_nodup vertices factors Δ hvn hen).idxOf_getElem n.val _

/-- Both directions execute the supplied-list lookup and position search. -/
def seedIndexEquiv (vertices : List V) (factors : List E) (Δ : ℕ)
    (hvn : vertices.Nodup) (hen : factors.Nodup)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors) :
    Fin (factors.length + (Δ + 1) * vertices.length) ≃ SeedIndex V E Δ where
  toFun := seedAt vertices factors Δ
  invFun := seedCodeFin vertices factors Δ hv he
  left_inv := seedCode_seedAt vertices factors Δ hvn hen hv he
  right_inv := seedAt_seedCode vertices factors Δ hv he

theorem seedCode_injective (vertices : List V) (factors : List E) (Δ : ℕ)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors) :
    Function.Injective (seedCode vertices factors Δ) := by
  let _ : BEq (SeedIndex V E Δ) := instBEqOfDecidableEq
  intro s t h
  exact (List.idxOf_inj (mem_seedIndices vertices factors Δ hv he s)).mp h

theorem seedCodes_eq_range (vertices : List V) (factors : List E) (Δ : ℕ)
    (hv : vertices.Nodup) (he : factors.Nodup) :
    (seedIndices vertices factors Δ).map (seedCode vertices factors Δ) =
      List.range (factors.length + (Δ + 1) * vertices.length) := by
  let _ : BEq (SeedIndex V E Δ) := instBEqOfDecidableEq
  apply List.ext_getElem
  · simp only [List.length_map, seedIndices_length, List.length_range]
  · intro n hn₁ hn₂
    simp only [List.getElem_map, List.getElem_range, seedCode,
      SubexponentialSAT.LocalExpectation.indexCode]
    exact (seedIndices_nodup vertices factors Δ hv he).idxOf_getElem n (by simpa using hn₁)

end Seeds

section ChoiceDecoding

variable {I W : Type*}

/-- The search stores chosen values newest first; numerical coordinates use
the reverse list, so coordinate zero is the first choice. -/
theorem decode_eq_reverse_getD (default : W) (values : List W) (n : ℕ) :
    SubexponentialSAT.LocalExpectation.decode default values n = values.reverse.getD n default := by
  induction values with
  | nil => rfl
  | cons w values ih =>
    simp only [SubexponentialSAT.LocalExpectation.decode, List.reverse_cons]
    by_cases heq : n = values.length
    · subst n
      simp only [Function.update_self]
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    · rw [Function.update_of_ne heq, ih]
      by_cases hlt : n < values.length
      · rw [List.getD_append _ _ _ _ (by simpa using hlt)]
      · have hge : values.length + 1 ≤ n := by omega
        rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_succ_le hge),
          List.getD_eq_default _ _ (by simpa using hge)]

/-- Serialize a total assignment in exactly the search's reversed-list format. -/
def encodeChoices (indices : List I) (assignment : I → W) : List W :=
  (indices.map assignment).reverse

@[simp] theorem encodeChoices_length (indices : List I) (assignment : I → W) :
    (encodeChoices indices assignment).length = indices.length := by
  simp [encodeChoices]

theorem decode_encodeChoices [DecidableEq I] (default : W)
    (indices : List I) (assignment : I → W) (i : I) (hi : i ∈ indices) :
    SubexponentialSAT.LocalExpectation.decode default (encodeChoices indices assignment)
      (SubexponentialSAT.LocalExpectation.indexCode indices i) = assignment i := by
  rw [decode_eq_reverse_getD]
  simp only [encodeChoices, List.reverse_reverse, List.getD_eq_getElem?_getD,
    List.getElem?_map, SubexponentialSAT.LocalExpectation.indexCode, List.getElem?_idxOf hi]
  rfl

theorem assignWithEvaluator_length (a : W) (tail : List W)
    (evaluate : ℕ → List W → ℚ) (n : ℕ) (fixed : List W) :
    (SubexponentialSAT.ConditionalExpectation.assignWithEvaluator a tail evaluate n fixed).length =
      n + fixed.length := by
  induction n generalizing fixed with
  | zero => simp [SubexponentialSAT.ConditionalExpectation.assignWithEvaluator]
  | succ n ih =>
    simp only [SubexponentialSAT.ConditionalExpectation.assignWithEvaluator, ih, List.length_cons]
    omega

end ChoiceDecoding

section ComputedAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E) {r Q Δ : ℕ} [NeZero r]
    (slots : SlotMap P Δ)

/-- The existing assignment algorithm with its word and seed enumerations
constructed explicitly from the input vertex and factor lists. -/
def enumeratedAssignment (vertices : List V) (factors : List E) :
    Assignment V E r Q Δ :=
  LocalExpectation.computedAssignment P slots
    (firstWord r Q (Nat.pos_of_neZero r)) (remainingWords r Q) vertices
    (seedIndices vertices factors Δ)

/-- The actual reverse-chronological choices made by that algorithm. -/
def assignmentValues (vertices : List V) (factors : List E) : List (Word r Q) :=
  SubexponentialSAT.LocalExpectation.localAssign
    (firstWord r Q (Nat.pos_of_neZero r)) (remainingWords r Q)
    (vertices.product vertices)
    (LocalExpectation.numberedPairSupport P slots (seedIndices vertices factors Δ))
    (LocalExpectation.numberedPairTerm P slots (seedIndices vertices factors Δ))
    (LocalExpectation.pairOffset (V := V) (r := r) (Q := Q) (Δ := Δ))
    (firstWord r Q (Nat.pos_of_neZero r)) (seedIndices vertices factors Δ).length

@[simp] theorem assignmentValues_length (vertices : List V) (factors : List E) :
    (assignmentValues (r := r) (Q := Q) P slots vertices factors).length =
      factors.length + (Δ + 1) * vertices.length := by
  simp only [assignmentValues, SubexponentialSAT.LocalExpectation.localAssign,
    assignWithEvaluator_length, List.length_nil, Nat.add_zero, seedIndices_length]

theorem enumeratedAssignment_apply (vertices : List V) (factors : List E)
    (s : SeedIndex V E Δ) :
    enumeratedAssignment (r := r) (Q := Q) P slots vertices factors s =
      SubexponentialSAT.LocalExpectation.decode (firstWord r Q (Nat.pos_of_neZero r))
        (assignmentValues P slots vertices factors) (seedCode vertices factors Δ s) := rfl

/-- The assigned word is found at precisely its seed code in the chronological
choice list. Every seed lookup is in range. -/
theorem assignmentValues_lookup (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors) (s : SeedIndex V E Δ) :
    ((assignmentValues (r := r) (Q := Q) P slots vertices factors).reverse)[seedCode vertices factors Δ s]? =
      some (enumeratedAssignment P slots vertices factors s) := by
  have hlt : seedCode vertices factors Δ s <
      (assignmentValues (r := r) (Q := Q) P slots vertices factors).reverse.length := by
    simpa only [List.length_reverse, assignmentValues_length] using
      seedCode_lt vertices factors Δ hv he s
  rw [enumeratedAssignment_apply, decode_eq_reverse_getD,
    List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt]

/-- The deviation theorem now requires only the actual input lists; alphabet
and seed completeness are discharged by the explicit constructions above. -/
theorem enumeratedAssignment_deviation_le (vertices : List V) (factors : List E)
    (hvn : vertices.Nodup) (hvc : ∀ v, v ∈ vertices)
    (hen : factors.Nodup) (hec : ∀ e, e ∈ factors) {k : ℕ} (hP : P.Bounded k Δ) :
    LocalExpectation.pairObjective P slots
        (enumeratedAssignment (r := r) (Q := Q) P slots vertices factors) ≤
      (Fintype.card (UniversalType r Q Δ) : ℚ) *
        (1 + (Δ * k : ℕ)) * (Fintype.card V : ℚ) :=
  LocalExpectation.computedAssignment_deviation_le P slots
    (firstWord r Q (Nat.pos_of_neZero r)) (remainingWords r Q)
    (choices_nodup r Q _) (choices_complete r Q _)
    vertices hvn hvc (seedIndices vertices factors Δ)
    (seedIndices_nodup vertices factors Δ hvn hen)
    (mem_seedIndices vertices factors Δ hvc hec) hP

end ComputedAssignment

end SubexponentialSAT.Subexp.AssignmentEnumeration

end OAI.Algorithms
