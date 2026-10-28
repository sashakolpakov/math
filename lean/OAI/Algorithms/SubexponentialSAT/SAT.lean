import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-! Concrete finite CNF syntax and semantics for the candidate SAT argument. -/

namespace SubexponentialSAT.SAT

universe u

abbrev Assignment (V : Type u) := V → Bool

/-- `positive = false` represents a negated variable. -/
structure Literal (V : Type u) where
  «variable» : V
  positive : Bool
  deriving DecidableEq

abbrev Clause (V : Type u) := Finset (Literal V)
abbrev CNF (V : Type u) := Finset (Clause V)

variable {V : Type u}

def Literal.eval (a : Assignment V) (l : Literal V) : Bool :=
  a l.variable == l.positive

def Literal.negate (l : Literal V) : Literal V :=
  ⟨l.variable, !l.positive⟩

@[simp] theorem Literal.eval_eq_true (a : Assignment V) (l : Literal V) :
    l.eval a = true ↔ a l.variable = l.positive := by
  simp [Literal.eval]

@[simp] theorem Literal.negate_negate (l : Literal V) : l.negate.negate = l := by
  cases l with
  | mk v p => cases p <;> rfl

@[simp] theorem Literal.eval_negate (a : Assignment V) (l : Literal V) :
    l.negate.eval a = !(l.eval a) := by
  cases l with
  | mk v p => cases p <;> cases h : a v <;> simp [Literal.eval, Literal.negate, h]

variable [DecidableEq V]

def Clause.eval (a : Assignment V) (C : Clause V) : Bool :=
  decide (∃ l ∈ C, l.eval a = true)

def CNF.eval (a : Assignment V) (F : CNF V) : Bool :=
  decide (∀ C ∈ F, C.eval a = true)

def Satisfiable (F : CNF V) : Prop := ∃ a : Assignment V, F.eval a = true

omit [DecidableEq V] in
@[simp] theorem Clause.eval_eq_true (a : Assignment V) (C : Clause V) :
    C.eval a = true ↔ ∃ l ∈ C, l.eval a = true := by
  simp [Clause.eval]

omit [DecidableEq V] in
@[simp] theorem CNF.eval_eq_true (a : Assignment V) (F : CNF V) :
    F.eval a = true ↔ ∀ C ∈ F, C.eval a = true := by
  simp [CNF.eval]

omit [DecidableEq V] in
@[simp] theorem Clause.eval_empty (a : Assignment V) :
    (∅ : Clause V).eval a = false := by simp [Clause.eval]

omit [DecidableEq V] in
@[simp] theorem CNF.eval_empty (a : Assignment V) :
    (∅ : CNF V).eval a = true := by simp [CNF.eval]

section Decidable

@[simp] theorem Clause.eval_insert (a : Assignment V) (l : Literal V) (C : Clause V) :
    (insert l C).eval a = (l.eval a || C.eval a) := by
  apply Bool.eq_iff_iff.mpr
  simp [Clause.eval]

@[simp] theorem CNF.eval_insert (a : Assignment V) (C : Clause V) (F : CNF V) :
    (insert C F).eval a = (C.eval a && F.eval a) := by
  apply Bool.eq_iff_iff.mpr
  simp [CNF.eval]

def WidthAtMost (k : ℕ) (F : CNF V) : Prop := ∀ C ∈ F, C.card ≤ k

/-- Maximum literal count of a clause; the empty formula has width zero. -/
def width (F : CNF V) : ℕ := F.sup Finset.card

omit [DecidableEq V] in
theorem width_le_iff (F : CNF V) (k : ℕ) : width F ≤ k ↔ WidthAtMost k F :=
  Finset.sup_le_iff

omit [DecidableEq V] in
@[simp] theorem width_empty : width (∅ : CNF V) = 0 := by simp [width]

def occurrences (v : V) (F : CNF V) : ℕ :=
  (F.filter fun C => ∃ l ∈ C, l.variable = v).card

def OccurrenceAtMost (B : ℕ) (F : CNF V) : Prop := ∀ v, occurrences v F ≤ B

omit [DecidableEq V] in
theorem Clause.eval_mono {a : Assignment V} {C D : Clause V} (h : C ⊆ D)
    (hC : C.eval a = true) : D.eval a = true := by
  obtain ⟨l, hl, ht⟩ := (Clause.eval_eq_true a C).mp hC
  exact (Clause.eval_eq_true a D).mpr ⟨l, h hl, ht⟩

omit [DecidableEq V] in
theorem CNF.eval_mono {a : Assignment V} {F G : CNF V} (h : F ⊆ G)
    (hG : G.eval a = true) : F.eval a = true := by
  apply (CNF.eval_eq_true a F).mpr
  intro C hC
  exact (CNF.eval_eq_true a G).mp hG C (h hC)

omit [DecidableEq V] in
theorem satisfiable_empty : Satisfiable (∅ : CNF V) :=
  ⟨fun _ => false, CNF.eval_empty _⟩

omit [DecidableEq V] in
theorem not_satisfiable_of_empty_mem {F : CNF V} (h : ∅ ∈ F) : ¬ Satisfiable F := by
  rintro ⟨a, ha⟩
  have he := (CNF.eval_eq_true a F).mp ha ∅ h
  simp at he

omit [DecidableEq V] in
theorem satisfiable_congr {F G : CNF V} (h : ∀ a, F.eval a = G.eval a) :
    Satisfiable F ↔ Satisfiable G := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (h a) ▸ ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (h a).symm ▸ ha⟩

/-- A clause containing both polarities of a literal. -/
abbrev Clause.IsTautology (C : Clause V) : Prop := ∃ l ∈ C, l.negate ∈ C

omit [DecidableEq V] in
theorem Clause.eval_of_isTautology {C : Clause V} (h : C.IsTautology)
    (a : Assignment V) : C.eval a = true := by
  obtain ⟨l, hl, hn⟩ := h
  apply (Clause.eval_eq_true a C).mpr
  cases he : l.eval a with
  | false => exact ⟨l.negate, hn, by simp [he]⟩
  | true => exact ⟨l, hl, he⟩

def removeTautologies (F : CNF V) : CNF V :=
  F.filter fun C => ¬ C.IsTautology

theorem eval_removeTautologies (a : Assignment V) (F : CNF V) :
    (removeTautologies F).eval a = F.eval a := by
  apply Bool.eq_iff_iff.mpr
  simp only [CNF.eval_eq_true]
  constructor
  · intro h C hC
    by_cases ht : C.IsTautology
    · exact Clause.eval_of_isTautology ht a
    · exact h C (Finset.mem_filter.mpr ⟨hC, ht⟩)
  · intro h C hC
    exact h C (Finset.mem_filter.mp hC).1

/-- Keep exactly the clauses having no strict subset among the clauses of `F`. -/
def absorb (F : CNF V) : CNF V :=
  F.filter fun C => ¬ ∃ D ∈ F, D ⊂ C

theorem absorb_subset (F : CNF V) : absorb F ⊆ F := Finset.filter_subset _ _

theorem exists_absorb_subset (F : CNF V) (C : Clause V) (hC : C ∈ F) :
    ∃ D ∈ absorb F, D ⊆ C := by
  classical
  revert hC
  refine Finset.strongInductionOn C ?_
  intro C ih hC
  by_cases hs : ∃ D ∈ F, D ⊂ C
  · obtain ⟨D, hD, hDC⟩ := hs
    obtain ⟨E, hE, hED⟩ := ih D hDC hD
    exact ⟨E, hE, hED.trans (Finset.ssubset_iff_subset_ne.mp hDC).1⟩
  · exact ⟨C, Finset.mem_filter.mpr ⟨hC, hs⟩, Finset.Subset.refl _⟩

theorem eval_absorb (a : Assignment V) (F : CNF V) :
    (absorb F).eval a = F.eval a := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    apply (CNF.eval_eq_true a F).mpr
    intro C hC
    obtain ⟨D, hD, hDC⟩ := exists_absorb_subset F C hC
    exact Clause.eval_mono hDC ((CNF.eval_eq_true a (absorb F)).mp h D hD)
  · exact CNF.eval_mono (absorb_subset F)

theorem absorb_antichain {F : CNF V} {C D : Clause V}
    (hC : C ∈ absorb F) (hD : D ∈ absorb F) (hDC : D ⊆ C) : D = C := by
  by_contra hne
  exact (Finset.mem_filter.mp hC).2
    ⟨D, (Finset.mem_filter.mp hD).1, Finset.ssubset_iff_subset_ne.mpr ⟨hDC, hne⟩⟩

def normalize (F : CNF V) : CNF V := absorb (removeTautologies F)

theorem eval_normalize (a : Assignment V) (F : CNF V) :
    (normalize F).eval a = F.eval a := by
  rw [normalize, eval_absorb, eval_removeTautologies]

theorem satisfiable_normalize (F : CNF V) : Satisfiable (normalize F) ↔ Satisfiable F :=
  satisfiable_congr (fun a => eval_normalize a F)

theorem normalize_subset (F : CNF V) : normalize F ⊆ F :=
  (absorb_subset _).trans (Finset.filter_subset _ _)

theorem normalize_not_tautology {F : CNF V} {C : Clause V} (hC : C ∈ normalize F) :
    ¬ C.IsTautology :=
  (Finset.mem_filter.mp (absorb_subset (removeTautologies F) hC)).2

theorem normalize_antichain {F : CNF V} {C D : Clause V}
    (hC : C ∈ normalize F) (hD : D ∈ normalize F) (hDC : D ⊆ C) : D = C :=
  absorb_antichain hC hD hDC

omit [DecidableEq V] in
theorem widthAtMost_of_subset {F G : CNF V} {k : ℕ} (h : F ⊆ G)
    (hG : WidthAtMost k G) : WidthAtMost k F :=
  fun C hC => hG C (h hC)

theorem width_normalize_le (F : CNF V) : width (normalize F) ≤ width F := by
  apply (width_le_iff (normalize F) (width F)).mpr
  exact widthAtMost_of_subset (normalize_subset F) ((width_le_iff F (width F)).mp le_rfl)

theorem occurrences_mono {F G : CNF V} (h : F ⊆ G) (v : V) :
    occurrences v F ≤ occurrences v G := by
  apply Finset.card_le_card
  intro C hC
  exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp hC).1,
    (Finset.mem_filter.mp hC).2⟩

theorem occurrenceAtMost_of_subset {F G : CNF V} {B : ℕ} (h : F ⊆ G)
    (hG : OccurrenceAtMost B G) : OccurrenceAtMost B F :=
  fun v => (occurrences_mono h v).trans (hG v)

section Finite

variable [Fintype V]

def satisfyingAssignments (F : CNF V) : Finset (Assignment V) :=
  Finset.univ.filter fun a => F.eval a = true

def count (F : CNF V) : ℕ := (satisfyingAssignments F).card

@[simp] theorem mem_satisfyingAssignments (a : Assignment V) (F : CNF V) :
    a ∈ satisfyingAssignments F ↔ F.eval a = true := by
  simp [satisfyingAssignments]

theorem count_eq_card_subtype (F : CNF V) :
    count F = Fintype.card {a : Assignment V // F.eval a = true} := by
  symm
  exact Fintype.card_of_subtype (satisfyingAssignments F)
    (fun a => mem_satisfyingAssignments a F)

theorem count_pos_iff (F : CNF V) : 0 < count F ↔ Satisfiable F := by
  simp [count, Finset.card_pos, Finset.Nonempty, Satisfiable]

theorem count_eq_zero_iff (F : CNF V) : count F = 0 ↔ ¬ Satisfiable F := by
  rw [← count_pos_iff]
  cases count F <;> simp

theorem count_le (F : CNF V) : count F ≤ 2 ^ Fintype.card V := by
  calc
    count F ≤ (Finset.univ : Finset (Assignment V)).card :=
      Finset.card_filter_le _ _
    _ = 2 ^ Fintype.card V := by simp [Assignment ]

theorem count_congr {F G : CNF V} (h : ∀ a, F.eval a = G.eval a) : count F = count G := by
  apply congrArg Finset.card
  ext a
  simp only [mem_satisfyingAssignments, h a]

theorem count_normalize (F : CNF V) : count (normalize F) = count F :=
  count_congr (fun a => eval_normalize a F)

/-- An actual finite exhaustive search. No fast runtime claim is attached to this definition. -/
def bruteForce (F : CNF V) : Bool := decide (0 < count F)

theorem bruteForce_eq_true_iff (F : CNF V) : bruteForce F = true ↔ Satisfiable F := by
  simp only [bruteForce, decide_eq_true_eq, count_pos_iff]

end Finite
end Decidable
end SubexponentialSAT.SAT

end OAI.Algorithms
