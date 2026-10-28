import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SunflowerBranch

namespace OAI.Algorithms

/-!
# Executable list operations for CNF formulas

These definitions use explicit finite lists and decidable literal comparisons.
The structural bounds count list elements or comparison invocations; they make
no assumption that an arbitrary `DecidableEq` comparison has unit bit cost.
-/

namespace SubexponentialSAT.ExecCNF

universe u
abbrev Clause (α : Type u) := List α
abbrev Formula (α : Type u) := List (Clause α)

variable {α : Type u} [DecidableEq α]

def clauseSet (C : Clause α) : Finset α := C.toFinset

def formulaSet (F : Formula α) : Finset (Finset α) := (F.map clauseSet).toFinset

@[simp] theorem mem_clauseSet {x : α} {C : Clause α} : x ∈ clauseSet C ↔ x ∈ C := by
  simp [clauseSet]

@[simp] theorem mem_formulaSet {C : Finset α} {F : Formula α} :
    C ∈ formulaSet F ↔ ∃ D ∈ F, clauseSet D = C := by
  simp [formulaSet]

@[simp] theorem clauseSet_nil : clauseSet ([] : Clause α) = ∅ := rfl
@[simp] theorem clauseSet_cons (x : α) (C : Clause α) :
    clauseSet (x :: C) = insert x (clauseSet C) := by simp [clauseSet]
@[simp] theorem clauseSet_append (C D : Clause α) :
    clauseSet (C ++ D) = clauseSet C ∪ clauseSet D := by simp [clauseSet]
@[simp] theorem formulaSet_nil : formulaSet ([] : Formula α) = ∅ := rfl
@[simp] theorem formulaSet_cons (C : Clause α) (F : Formula α) :
    formulaSet (C :: F) = insert (clauseSet C) (formulaSet F) := by simp [formulaSet]
@[simp] theorem formulaSet_append (F G : Formula α) :
    formulaSet (F ++ G) = formulaSet F ∪ formulaSet G := by simp [formulaSet]

/-- A left-to-right linear literal-membership scan. -/
def contains (x : α) : List α → Bool
  | [] => false
  | y :: ys => if x = y then true else contains x ys

@[simp] theorem contains_true (x : α) (L : List α) : contains x L = true ↔ x ∈ L := by
  induction L with
  | nil => simp [contains]
  | cons y ys ih =>
    by_cases h : x = y
    · simp [contains, h]
    · simp [contains, h, ih]

/-- Every literal of the first list is searched for in the second. -/
def subset : Clause α → Clause α → Bool
  | [], _ => true
  | x :: xs, D => contains x D && subset xs D

@[simp] theorem subset_true (C D : Clause α) :
    subset C D = true ↔ clauseSet C ⊆ clauseSet D := by
  induction C with
  | nil => simp [subset]
  | cons x xs ih => simp [subset, ih, Finset.insert_subset_iff]

def equivalent (C D : Clause α) : Bool := subset C D && subset D C

@[simp] theorem equivalent_true (C D : Clause α) :
    equivalent C D = true ↔ clauseSet C = clauseSet D := by
  simp only [equivalent, Bool.and_eq_true, subset_true]
  exact ⟨fun h => Finset.Subset.antisymm h.1 h.2,
    fun h => ⟨h ▸ Finset.Subset.refl _, h ▸ Finset.Subset.refl _⟩⟩

def strictSubset (C D : Clause α) : Bool := subset C D && !(subset D C)

@[simp] theorem strictSubset_true (C D : Clause α) :
    strictSubset C D = true ↔ clauseSet C ⊂ clauseSet D := by
  simp only [strictSubset, Bool.and_eq_true, subset_true]
  constructor
  · rintro ⟨hCD, hf⟩
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hCD, ?_⟩
    intro heq
    have ht : subset D C = true := subset_true D C |>.mpr (heq ▸ Finset.Subset.refl _)
    simp [ht] at hf
  · intro h
    obtain ⟨hCD, hne⟩ := Finset.ssubset_iff_subset_ne.mp h
    refine ⟨hCD, ?_⟩
    cases hb : subset D C with
    | false => rfl
    | true => exact False.elim (hne (Finset.Subset.antisymm hCD ((subset_true D C).mp hb)))

/-- Keep the last occurrence of each literal, preserving that order. -/
def dedupLiterals : Clause α → Clause α
  | [] => []
  | x :: xs => if contains x xs = true then dedupLiterals xs else x :: dedupLiterals xs

@[simp] theorem mem_dedupLiterals (x : α) (C : Clause α) :
    x ∈ dedupLiterals C ↔ x ∈ C := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons y ys ih =>
    by_cases h : contains y ys = true
    · have hy : y ∈ ys := (contains_true y ys).mp h
      simp only [dedupLiterals, h, ite_true, List.mem_cons, ih]
      exact ⟨Or.inr, fun hx => hx.elim (fun heq => heq ▸ hy) id⟩
    · simp [dedupLiterals, h, ih]

@[simp] theorem clauseSet_dedupLiterals (C : Clause α) :
    clauseSet (dedupLiterals C) = clauseSet C := by
  ext x
  simp

theorem dedupLiterals_nodup (C : Clause α) : (dedupLiterals C).Nodup := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih
    · simp only [dedupLiterals, ite_eq_right h, List.nodup_cons]
      exact ⟨fun hm => h ((contains_true x xs).mpr ((mem_dedupLiterals x xs).mp hm)), ih⟩

theorem dedupLiterals_length_le (C : Clause α) : (dedupLiterals C).length ≤ C.length := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih.trans (Nat.le_succ _)
    · simpa [dedupLiterals, h] using Nat.succ_le_succ ih

/-- Remove duplicate clauses using set equality, including permutations. -/
def dedupClauses : Formula α → Formula α
  | [] => []
  | C :: F => if F.any (fun D => equivalent C D) = true then dedupClauses F
      else C :: dedupClauses F

@[simp] theorem any_equivalent_true (C : Clause α) (F : Formula α) :
    F.any (fun D => equivalent C D) = true ↔ clauseSet C ∈ formulaSet F := by
  simp only [List.any_eq_true, equivalent_true, mem_formulaSet]
  constructor
  · rintro ⟨D, hD, heq⟩
    exact ⟨D, hD, heq.symm⟩
  · rintro ⟨D, hD, heq⟩
    exact ⟨D, hD, heq.symm⟩

@[simp] theorem formulaSet_dedupClauses (F : Formula α) :
    formulaSet (dedupClauses F) = formulaSet F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    by_cases h : F.any (fun D => equivalent C D) = true
    · simp only [dedupClauses, h, ite_true, formulaSet_cons, ih]
      exact (Finset.insert_eq_of_mem ((any_equivalent_true C F).mp h)).symm
    · simp [dedupClauses, h, ih]

theorem dedupClauses_map_nodup (F : Formula α) : ((dedupClauses F).map clauseSet).Nodup := by
  induction F with
  | nil => simp [dedupClauses]
  | cons C F ih =>
    by_cases h : F.any (fun D => equivalent C D) = true
    · simpa [dedupClauses, h] using ih
    · simp only [dedupClauses, ite_eq_right h, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hm
      have hmem : clauseSet C ∈ formulaSet (dedupClauses F) := by
        exact List.mem_toFinset.mpr hm
      rw [formulaSet_dedupClauses] at hmem
      exact h ((any_equivalent_true C F).mpr hmem)

theorem dedupClauses_length_le (F : Formula α) : (dedupClauses F).length ≤ F.length := by
  induction F with
  | nil => simp [dedupClauses]
  | cons C F ih =>
    by_cases h : F.any (fun D => equivalent C D) = true
    · simpa [dedupClauses, h] using ih.trans (Nat.le_succ _)
    · simpa [dedupClauses, h] using Nat.succ_le_succ ih

end SubexponentialSAT.ExecCNF

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

@[simp] theorem not_true_iff (b : Bool) : (!b) = true ↔ ¬ b = true := by
  cases b <;> simp

theorem formulaSet_filter (F : Formula α) (p : Clause α → Bool)
    (q : Finset α → Prop) [DecidablePred q]
    (hp : ∀ C, p C = true ↔ q (clauseSet C)) :
    formulaSet (F.filter p) = (formulaSet F).filter q := by
  ext C
  simp only [mem_formulaSet, Finset.mem_filter]
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨hD, htest⟩ := List.mem_filter.mp hD
    exact ⟨⟨D, hD, rfl⟩, (hp D).mp htest⟩
  · rintro ⟨⟨D, hD, rfl⟩, hq⟩
    exact ⟨D, List.mem_filter.mpr ⟨hD, (hp D).mpr hq⟩, rfl⟩

@[simp] theorem any_strictSubset_true (C : Clause α) (F : Formula α) :
    F.any (fun D => strictSubset D C) = true ↔ ∃ D ∈ formulaSet F, D ⊂ clauseSet C := by
  simp only [List.any_eq_true, strictSubset_true, mem_formulaSet]
  constructor
  · rintro ⟨D, hD, hsub⟩
    exact ⟨clauseSet D, ⟨D, hD, rfl⟩, hsub⟩
  · rintro ⟨D, ⟨E, hE, rfl⟩, hsub⟩
    exact ⟨E, hE, hsub⟩

/-- Test whether a clause contains a literal together with its designated opposite. -/
def tautology (neg : α → α) (C : Clause α) : Bool :=
  C.any fun x => contains (neg x) C

@[simp] theorem tautology_true (neg : α → α) (C : Clause α) :
    tautology neg C = true ↔ ∃ x ∈ clauseSet C, neg x ∈ clauseSet C := by
  simp [tautology, List.any_eq_true]

def removeTautologies (neg : α → α) (F : Formula α) : Formula α :=
  F.filter fun C => !(tautology neg C)

@[simp] theorem formulaSet_removeTautologies (neg : α → α) (F : Formula α) :
    formulaSet (removeTautologies neg F) =
      (formulaSet F).filter (fun C => ¬ ∃ x ∈ C, neg x ∈ C) := by
  apply formulaSet_filter
  intro C
  simp only [not_true_iff, tautology_true]

/-- Strict-superset deletion; semantic duplicate clauses are removed first. -/
def absorb (F : Formula α) : Formula α :=
  (dedupClauses F).filter fun C => !(F.any fun D => strictSubset D C)

@[simp] theorem formulaSet_absorb (F : Formula α) :
    formulaSet (absorb F) =
      (formulaSet F).filter (fun C => ¬ ∃ D ∈ formulaSet F, D ⊂ C) := by
  change formulaSet ((dedupClauses F).filter _) = _
  rw [formulaSet_filter (dedupClauses F) _
    (fun C => ¬ ∃ D ∈ formulaSet F, D ⊂ C)]
  · rw [formulaSet_dedupClauses]
  · intro C
    simp only [not_true_iff, any_strictSubset_true]

/-- Literal deduplication is separate from clause deduplication. -/
def cleanLiterals (F : Formula α) : Formula α := F.map dedupLiterals

@[simp] theorem formulaSet_cleanLiterals (F : Formula α) :
    formulaSet (cleanLiterals F) = formulaSet F := by
  simp [cleanLiterals, formulaSet, List.map_map, Function.comp_def]

def normalize (neg : α → α) (F : Formula α) : Formula α :=
  absorb (removeTautologies neg (cleanLiterals F))

/-- Remove every clause equal as a set to a selected clause. -/
def eraseClauses (F S : Formula α) : Formula α :=
  F.filter fun C => !(S.any fun D => equivalent C D)

@[simp] theorem formulaSet_eraseClauses (F S : Formula α) :
    formulaSet (eraseClauses F S) = formulaSet F \ formulaSet S := by
  unfold eraseClauses
  rw [formulaSet_filter F _ (fun C => C ∉ formulaSet S)]
  · ext C
    simp
  · intro C
    simp only [not_true_iff, any_equivalent_true]

/-- Raw selected clauses formed by attaching the common core. -/
def clauses (H : Clause α) (P : Formula α) : Formula α := P.map (fun p => H ++ p)

@[simp] theorem formulaSet_clauses (H : Clause α) (P : Formula α) :
    formulaSet (clauses H P) = (formulaSet P).image (fun p => clauseSet H ∪ p) := by
  ext C
  simp only [mem_formulaSet, clauses, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨D, ⟨p, hp, rfl⟩, heq⟩
    exact ⟨clauseSet p, ⟨p, hp, rfl⟩, (clauseSet_append H p).symm.trans heq⟩
  · rintro ⟨D, ⟨p, hp, rfl⟩, heq⟩
    exact ⟨H ++ p, ⟨p, hp, rfl⟩, (clauseSet_append H p).trans heq⟩

def childA (F : Formula α) (H : Clause α) (P : Formula α) : Formula α :=
  absorb (H :: eraseClauses F (clauses H P))

def childB (F : Formula α) (H : Clause α) (P : Formula α) : Formula α :=
  absorb (eraseClauses F (clauses H P) ++ P)

theorem dedupClauses_subset (F : Formula α) : dedupClauses F ⊆ F := by
  intro C hC
  induction F with
  | nil => simp [dedupClauses] at hC
  | cons D F ih =>
    by_cases h : F.any (fun E => equivalent D E) = true
    · have htail : C ∈ dedupClauses F := by simpa [dedupClauses, h] using hC
      exact List.mem_cons_of_mem D (ih htail)
    · have hsplit : C = D ∨ C ∈ dedupClauses F := by simpa [dedupClauses, h] using hC
      exact hsplit.elim (fun h => h ▸ List.mem_cons_self) (fun h => List.mem_cons_of_mem D (ih h))

theorem absorb_subset (F : Formula α) : absorb F ⊆ F := by
  intro C hC
  exact dedupClauses_subset F (List.mem_filter.mp hC).1

theorem removeTautologies_length_le (neg : α → α) (F : Formula α) :
    (removeTautologies neg F).length ≤ F.length := List.length_filter_le _ _

theorem absorb_length_le (F : Formula α) : (absorb F).length ≤ F.length :=
  (List.length_filter_le _ _).trans (dedupClauses_length_le F)

theorem normalize_length_le (neg : α → α) (F : Formula α) :
    (normalize neg F).length ≤ F.length := by
  exact (absorb_length_le _).trans ((removeTautologies_length_le _ _).trans
    (by simp [cleanLiterals]))

theorem eraseClauses_length_le (F S : Formula α) : (eraseClauses F S).length ≤ F.length :=
  List.length_filter_le _ _

omit [DecidableEq α] in
@[simp] theorem clauses_length (H : Clause α) (P : Formula α) :
    (clauses H P).length = P.length := by simp [clauses]

theorem childA_length_le (F : Formula α) (H : Clause α) (P : Formula α) :
    (childA F H P).length ≤ F.length + 1 :=
  (absorb_length_le _).trans (Nat.succ_le_succ (eraseClauses_length_le _ _))

theorem childB_length_le (F : Formula α) (H : Clause α) (P : Formula α) :
    (childB F H P).length ≤ F.length + P.length := by
  apply (absorb_length_le _).trans
  simpa using Nat.add_le_add_right (eraseClauses_length_le F (clauses H P)) P.length

section SAT
variable {V : Type u} [DecidableEq V]

@[simp] theorem absorb_set (F : Formula (SubexponentialSAT.SAT.Literal V)) :
    formulaSet (absorb F) = SubexponentialSAT.SAT.absorb (formulaSet F) := formulaSet_absorb F

@[simp] theorem normalize_set (F : Formula (SubexponentialSAT.SAT.Literal V)) :
    formulaSet (normalize SubexponentialSAT.SAT.Literal.negate F) = SubexponentialSAT.SAT.normalize (formulaSet F) := by
  simp only [normalize, absorb_set, formulaSet_removeTautologies, formulaSet_cleanLiterals]
  rfl

@[simp] theorem childA_set (F : Formula (SubexponentialSAT.SAT.Literal V))
    (H : Clause (SubexponentialSAT.SAT.Literal V)) (P : Formula (SubexponentialSAT.SAT.Literal V)) :
    formulaSet (childA F H P) =
      SubexponentialSAT.SunflowerBranch.childA (formulaSet F) (clauseSet H) (formulaSet P) := by
  simp only [childA, absorb_set, formulaSet_cons, formulaSet_eraseClauses, formulaSet_clauses]
  rfl

@[simp] theorem childB_set (F : Formula (SubexponentialSAT.SAT.Literal V))
    (H : Clause (SubexponentialSAT.SAT.Literal V)) (P : Formula (SubexponentialSAT.SAT.Literal V)) :
    formulaSet (childB F H P) =
      SubexponentialSAT.SunflowerBranch.childB (formulaSet F) (clauseSet H) (formulaSet P) := by
  simp only [childB, absorb_set, formulaSet_append, formulaSet_eraseClauses, formulaSet_clauses]
  rfl

theorem eval_normalize (a : SubexponentialSAT.SAT.Assignment V) (F : Formula (SubexponentialSAT.SAT.Literal V)) :
    SubexponentialSAT.SAT.CNF.eval a (formulaSet (normalize SubexponentialSAT.SAT.Literal.negate F)) =
      SubexponentialSAT.SAT.CNF.eval a (formulaSet F) := by
  rw [normalize_set, SubexponentialSAT.SAT.eval_normalize]

theorem eval_children_iff (a : SubexponentialSAT.SAT.Assignment V) (F : Formula (SubexponentialSAT.SAT.Literal V))
    (H : Clause (SubexponentialSAT.SAT.Literal V)) (P : Formula (SubexponentialSAT.SAT.Literal V))
    (hsub : formulaSet (clauses H P) ⊆ formulaSet F) :
    SubexponentialSAT.SAT.CNF.eval a (formulaSet F) = true ↔
      SubexponentialSAT.SAT.CNF.eval a (formulaSet (childA F H P)) = true ∨
      SubexponentialSAT.SAT.CNF.eval a (formulaSet (childB F H P)) = true := by
  rw [childA_set, childB_set]
  exact SubexponentialSAT.SunflowerBranch.eval_children_iff a _ _ _ (by simpa [SubexponentialSAT.SunflowerBranch.clauses] using hsub)

end SAT
end SubexponentialSAT.ExecCNF

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

/-- The number of literal equality tests executed by `contains`. -/
def containsComparisons (x : α) : List α → ℕ
  | [] => 0
  | y :: ys => if x = y then 1 else 1 + containsComparisons x ys

theorem containsComparisons_le (x : α) (L : List α) :
    containsComparisons x L ≤ L.length := by
  induction L with
  | nil => simp [containsComparisons]
  | cons y ys ih =>
    by_cases h : x = y
    · simp [containsComparisons, h]
    · simpa [containsComparisons, h, Nat.add_comm] using Nat.succ_le_succ ih

/-- Literal equality tests in the short-circuit subset scan. -/
def subsetComparisons : Clause α → Clause α → ℕ
  | [], _ => 0
  | x :: xs, D => containsComparisons x D +
      if contains x D = true then subsetComparisons xs D else 0

theorem subsetComparisons_le (C D : Clause α) :
    subsetComparisons C D ≤ C.length * D.length := by
  induction C with
  | nil => simp [subsetComparisons]
  | cons x xs ih =>
    calc
      subsetComparisons (x :: xs) D ≤ D.length + xs.length * D.length := by
        apply Nat.add_le_add (containsComparisons_le x D)
        split
        · exact ih
        · exact Nat.zero_le _
      _ = (x :: xs).length * D.length := by simp [Nat.add_mul, Nat.add_comm]

theorem absorb_map_nodup (F : Formula α) : ((absorb F).map clauseSet).Nodup := by
  apply List.Sublist.nodup _ (dedupClauses_map_nodup F)
  exact List.Sublist.map clauseSet List.filter_sublist

theorem normalize_map_nodup (neg : α → α) (F : Formula α) :
    ((normalize neg F).map clauseSet).Nodup := absorb_map_nodup _

theorem normalize_literal_nodup (neg : α → α) (F : Formula α) :
    ∀ C ∈ normalize neg F, C.Nodup := by
  intro C hC
  have h1 := absorb_subset _ hC
  have h2 := (List.mem_filter.mp h1).1
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h2
  exact dedupLiterals_nodup D

theorem dedupLiterals_length_eq_card (C : Clause α) :
    (dedupLiterals C).length = (clauseSet C).card := by
  have h := List.toFinset_card_of_nodup (dedupLiterals_nodup C)
  change (clauseSet (dedupLiterals C)).card = _ at h
  rw [clauseSet_dedupLiterals] at h
  exact h.symm

theorem normalize_length_eq_card (neg : α → α) (F : Formula α) :
    (normalize neg F).length = (formulaSet (normalize neg F)).card := by
  have h := List.toFinset_card_of_nodup (normalize_map_nodup neg F)
  simpa only [formulaSet, List.length_map] using h.symm

/-- Executable total literal count after removing both kinds of duplicates.
This is a list computation, not a call to the finite-set specification. -/
def mass (F : Formula α) : ℕ :=
  ((dedupClauses F).map fun C => (dedupLiterals C).length).sum

theorem mass_eq_set_sum (F : Formula α) :
    mass F = (formulaSet F).sum Finset.card := by
  unfold mass
  simp_rw [dedupLiterals_length_eq_card]
  have h := List.sum_toFinset Finset.card (dedupClauses_map_nodup F)
  simp only [List.map_map, Function.comp_def] at h
  rw [← h]
  change (formulaSet (dedupClauses F)).sum Finset.card = _
  rw [formulaSet_dedupClauses]

section SAT
variable {V : Type u} [DecidableEq V]

@[simp] theorem mass_eq_literalMass (F : Formula (SubexponentialSAT.SAT.Literal V)) :
    mass F = SubexponentialSAT.SunflowerBranch.literalMass (formulaSet F) := mass_eq_set_sum F

theorem mass_childA_lt (F : Formula (SubexponentialSAT.SAT.Literal V))
    (H : Clause (SubexponentialSAT.SAT.Literal V)) (P : Formula (SubexponentialSAT.SAT.Literal V))
    {d : ℕ} (s : SubexponentialSAT.SunflowerBranch.Sunflower V d)
    (hH : clauseSet H = s.core) (hP : formulaSet P = s.petals)
    (hsub : SubexponentialSAT.SunflowerBranch.clauses s.core s.petals ⊆ formulaSet F) :
    mass (childA F H P) < mass F := by
  rw [mass_eq_literalMass, mass_eq_literalMass, childA_set, hH, hP]
  exact s.literalMass_childA_lt hsub

theorem mass_childB_lt (F : Formula (SubexponentialSAT.SAT.Literal V))
    (H : Clause (SubexponentialSAT.SAT.Literal V)) (P : Formula (SubexponentialSAT.SAT.Literal V))
    {d : ℕ} (s : SubexponentialSAT.SunflowerBranch.Sunflower V d)
    (hH : clauseSet H = s.core) (hP : formulaSet P = s.petals)
    (hsub : SubexponentialSAT.SunflowerBranch.clauses s.core s.petals ⊆ formulaSet F) :
    mass (childB F H P) < mass F := by
  rw [mass_eq_literalMass, mass_eq_literalMass, childB_set, hH, hP]
  exact s.literalMass_childB_lt hsub

end SAT
end SubexponentialSAT.ExecCNF

end OAI.Algorithms
