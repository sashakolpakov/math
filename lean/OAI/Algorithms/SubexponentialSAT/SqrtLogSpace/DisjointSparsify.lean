import OAI.Algorithms.SubexponentialSAT.SunflowerBranch

/-! Appendix A: literal-core branching with disjoint exact-count children. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch

open OAI.Algorithms.SubexponentialSAT.SAT

universe u
variable {V : Type u} [DecidableEq V]

/-- All clauses of the chosen width containing the chosen core. -/
def selected (F : CNF V) (c : ℕ) (H : Clause V) : CNF V :=
  F.filter fun C => C.card = c ∧ H ⊆ C

/-- Petals are remainders, with no disjointness requirement between them. -/
def petals (F : CNF V) (c : ℕ) (H : Clause V) : CNF V :=
  SunflowerBranch.petalFamily (selected F c H) H

/-- Unit clauses forcing every core literal to be false. -/
def negatedCoreUnits (H : Clause V) : CNF V :=
  H.image fun l => {l.negate}

def childA (F : CNF V) (c : ℕ) (H : Clause V) : CNF V :=
  absorb (insert H (F \ selected F c H))

def childB (F : CNF V) (c : ℕ) (H : Clause V) : CNF V :=
  absorb (((F \ selected F c H) ∪ petals F c H) ∪ negatedCoreUnits H)

/-- Only genuinely new clauses are counted as insertion events. -/
def insertedB (F : CNF V) (c : ℕ) (H : Clause V) : CNF V :=
  (petals F c H ∪ negatedCoreUnits H) \ F

@[simp] theorem mem_selected {F : CNF V} {c : ℕ} {H C : Clause V} :
    C ∈ selected F c H ↔ C ∈ F ∧ C.card = c ∧ H ⊆ C :=
  Finset.mem_filter

theorem selected_subset (F : CNF V) (c : ℕ) (H : Clause V) :
    selected F c H ⊆ F := Finset.filter_subset _ _

theorem sdiff_injOn_selected (F : CNF V) (c : ℕ) (H : Clause V) :
    Set.InjOn (fun C => C \ H) (selected F c H) :=
  SunflowerBranch.sdiff_injective_on fun _ hC => (mem_selected.mp hC).2.2

theorem petals_card (F : CNF V) (c : ℕ) (H : Clause V) :
    (petals F c H).card = (selected F c H).card :=
  Finset.card_image_of_injOn (sdiff_injOn_selected F c H)

theorem clauses_petals (F : CNF V) (c : ℕ) (H : Clause V) :
    SunflowerBranch.clauses H (petals F c H) = selected F c H :=
  SunflowerBranch.clauses_petalFamily fun _ hC => (mem_selected.mp hC).2.2

theorem petal_card {F : CNF V} {c : ℕ} {H P : Clause V}
    (hP : P ∈ petals F c H) : P.card = c - H.card := by
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hP
  rw [Finset.card_sdiff,
    Finset.inter_eq_left.mpr (mem_selected.mp hC).2.2,
    (mem_selected.mp hC).2.1]

theorem petals_filter_card (F : CNF V) (c : ℕ) (H S : Clause V)
    (hHS : Disjoint H S) :
    ((petals F c H).filter fun P => S ⊆ P).card =
      (selected F c (H ∪ S)).card := by
  have hfilter : (selected F c H).filter (fun C => S ⊆ C \ H) =
      selected F c (H ∪ S) := by
    ext C
    simp [selected, Finset.subset_sdiff, Finset.union_subset_iff, hHS.symm, and_assoc]
  unfold petals SunflowerBranch.petalFamily
  rw [Finset.filter_image, hfilter]
  exact Finset.card_image_of_injOn (SunflowerBranch.sdiff_injective_on fun C hC =>
    Finset.subset_union_left.trans (mem_selected.mp hC).2.2)

theorem negatedCoreUnits_eval (a : Assignment V) (H : Clause V) :
    (negatedCoreUnits H).eval a = true ↔ H.eval a = false := by
  simp only [CNF.eval_eq_true, negatedCoreUnits, Finset.forall_mem_image,
    Clause.eval_eq_true, Finset.mem_singleton, exists_eq_left, Literal.eval_negate,
    Bool.not_eq_true', ← Bool.not_eq_true, not_exists, not_and]

theorem eval_childA (a : Assignment V) (F : CNF V) (c : ℕ) (H : Clause V) :
    (childA F c H).eval a = true ↔
      H.eval a = true ∧ (F \ selected F c H).eval a = true := by
  simp only [childA, eval_absorb, CNF.eval_insert, Bool.and_eq_true]

theorem eval_childB (a : Assignment V) (F : CNF V) (c : ℕ) (H : Clause V) :
    (childB F c H).eval a = true ↔
      ((F \ selected F c H).eval a = true ∧ (petals F c H).eval a = true) ∧
        H.eval a = false := by
  rw [childB, eval_absorb, SunflowerBranch.cnf_union_true_iff,
    SunflowerBranch.cnf_union_true_iff, negatedCoreUnits_eval]

theorem eval_children_iff (a : Assignment V) (F : CNF V) (c : ℕ) (H : Clause V) :
    F.eval a = true ↔
      (childA F c H).eval a = true ∨ (childB F c H).eval a = true := by
  have hF : F.eval a = true ↔ (F \ selected F c H).eval a = true ∧
      (H.eval a = true ∨ (petals F c H).eval a = true) := by
    have hsplit : F = (F \ selected F c H) ∪ selected F c H :=
      (Finset.sdiff_union_of_subset (selected_subset F c H)).symm
    have hselected : (selected F c H).eval a = true ↔
        H.eval a = true ∨ (petals F c H).eval a = true := by
      rw [← clauses_petals F c H, SunflowerBranch.clauses_true_iff]
    conv_lhs => rw [hsplit]
    rw [SunflowerBranch.cnf_union_true_iff, hselected]
  rw [hF, eval_childA, eval_childB]
  cases H.eval a <;> simp

theorem children_disjoint (a : Assignment V) (F : CNF V) (c : ℕ) (H : Clause V) :
    ¬ ((childA F c H).eval a = true ∧ (childB F c H).eval a = true) := by
  rintro ⟨hA, hB⟩
  have ht := ((eval_childA a F c H).mp hA).1
  have hf := ((eval_childB a F c H).mp hB).2
  rw [ht] at hf
  contradiction

theorem satisfyingAssignments_partition [Fintype V] (F : CNF V) (c : ℕ)
    (H : Clause V) :
    satisfyingAssignments F = satisfyingAssignments (childA F c H) ∪
      satisfyingAssignments (childB F c H) := by
  ext a
  simp only [mem_satisfyingAssignments, Finset.mem_union]
  exact eval_children_iff a F c H

theorem satisfyingAssignments_disjoint [Fintype V] (F : CNF V) (c : ℕ)
    (H : Clause V) :
    Disjoint (satisfyingAssignments (childA F c H))
      (satisfyingAssignments (childB F c H)) := by
  apply Finset.disjoint_left.mpr
  intro a hA hB
  exact children_disjoint a F c H
    ⟨(mem_satisfyingAssignments _ _).mp hA, (mem_satisfyingAssignments _ _).mp hB⟩

theorem count_children [Fintype V] (F : CNF V) (c : ℕ) (H : Clause V) :
    count F = count (childA F c H) + count (childB F c H) := by
  unfold count
  rw [satisfyingAssignments_partition, Finset.card_union_of_disjoint
    (satisfyingAssignments_disjoint F c H)]

theorem core_strict_subset {F : CNF V} {c : ℕ} {H C : Clause V}
    (hC : C ∈ selected F c H) (hproper : H.card < c) : H ⊂ C := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨(mem_selected.mp hC).2.2, ?_⟩
  intro h
  have hc := (mem_selected.mp hC).2.1
  rw [← h] at hc
  omega

theorem petal_strict_subset {F : CNF V} {c : ℕ} {H C : Clause V}
    (hC : C ∈ selected F c H) (hH : H.Nonempty) : C \ H ⊂ C :=
  Finset.sdiff_ssubset (mem_selected.mp hC).2.2 hH

theorem no_old_subset_core {F : CNF V} {c : ℕ} {H E : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c) (hE : E ∈ F) : ¬ E ⊆ H := by
  intro hEH
  obtain ⟨C, hC⟩ := hsel
  have hHC := core_strict_subset hC hproper
  have hEC := hF E hE C (selected_subset F c H hC)
    (hEH.trans (Finset.ssubset_iff_subset_ne.mp hHC).1)
  have hCH : C ⊆ H := hEC ▸ hEH
  exact (Finset.ssubset_iff_subset_ne.mp hHC).2
    (Finset.Subset.antisymm (mem_selected.mp hC).2.2 hCH)

theorem no_old_subset_petal {F : CNF V} {c : ℕ} {H P E : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty)
    (hP : P ∈ petals F c H) (hE : E ∈ F) : ¬ E ⊆ P := by
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hP
  intro hEP
  have hEC := hF E hE C (selected_subset F c H hC) (hEP.trans Finset.sdiff_subset)
  have hCP : C ⊆ C \ H := hEC ▸ hEP
  exact (Finset.ssubset_iff_subset_ne.mp (petal_strict_subset hC hH)).2
    (Finset.Subset.antisymm Finset.sdiff_subset hCP)

theorem core_new {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c) : H ∉ F := by
  intro hH
  exact no_old_subset_core hF hsel hproper hH (Finset.Subset.refl _)

theorem petal_new {F : CNF V} {c : ℕ} {H P : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty)
    (hP : P ∈ petals F c H) : P ∉ F := by
  intro hPF
  exact no_old_subset_petal hF hH hP hPF (Finset.Subset.refl _)

theorem core_mem_childA {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c) : H ∈ childA F c H := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_insert_self _ _, ?_⟩
  rintro ⟨E, hE, hEH⟩
  rcases Finset.mem_insert.mp hE with rfl | hE
  · exact (Finset.ssubset_iff_subset_ne.mp hEH).2 rfl
  · exact no_old_subset_core hF hsel hproper (Finset.mem_sdiff.mp hE).1
      (Finset.ssubset_iff_subset_ne.mp hEH).1

theorem unit_not_subset_petal {F : CNF V} {c : ℕ} {H P U : Clause V}
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hP : P ∈ petals F c H)
    (hU : U ∈ negatedCoreUnits H) : ¬ U ⊆ P := by
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hU
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hP
  intro hsub
  apply hnt C (selected_subset F c H hC)
  exact ⟨l, (mem_selected.mp hC).2.2 hl,
    (Finset.mem_sdiff.mp (hsub (Finset.mem_singleton_self _))).1⟩

theorem petals_subset_childB {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) : petals F c H ⊆ childB F c H := by
  intro P hP
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hP), ?_⟩
  rintro ⟨E, hE, hEP⟩
  obtain ⟨hEPsub, hEPne⟩ := Finset.ssubset_iff_subset_ne.mp hEP
  rcases Finset.mem_union.mp hE with hE | hE
  · rcases Finset.mem_union.mp hE with hE | hE
    · exact no_old_subset_petal hF hH hP (Finset.mem_sdiff.mp hE).1 hEPsub
    · exact hEPne (Finset.eq_of_subset_of_card_le hEPsub
        (by rw [petal_card hP, petal_card hE]))
  · exact unit_not_subset_petal hnt hP hE hEPsub

theorem parent_clause_nonempty {F : CNF V} {c : ℕ} {H C : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c) (hC : C ∈ F) : C.Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  exact no_old_subset_core hF hsel hproper hC (by rw [he]; exact Finset.empty_subset _)

theorem rawB_clause_nonempty {F : CNF V} {c : ℕ} {H C : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c)
    (hC : C ∈ ((F \ selected F c H) ∪ petals F c H) ∪ negatedCoreUnits H) :
    C.Nonempty := by
  rcases Finset.mem_union.mp hC with hC | hC
  · rcases Finset.mem_union.mp hC with hC | hC
    · exact parent_clause_nonempty hF hsel hproper (Finset.mem_sdiff.mp hC).1
    · apply Finset.card_pos.mp
      rw [petal_card hC]
      exact Nat.sub_pos_of_lt hproper
  · obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hC
    exact Finset.singleton_nonempty _

theorem units_subset_childB {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c) : negatedCoreUnits H ⊆ childB F c H := by
  intro U hU
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_union_right _ hU, ?_⟩
  rintro ⟨E, hE, hEU⟩
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hU
  have hne := rawB_clause_nonempty hF hsel hproper hE
  rw [Finset.eq_empty_of_ssubset_singleton hEU] at hne
  exact Finset.not_nonempty_empty hne

theorem insertedB_subset_childB {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hsel : (selected F c H).Nonempty)
    (hH : H.Nonempty) (hproper : H.card < c)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) : insertedB F c H ⊆ childB F c H := by
  intro C hC
  rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hC).1 with hC | hC
  · exact petals_subset_childB hF hH hnt hC
  · exact units_subset_childB hF hsel hproper hC

theorem petals_subset_insertedB {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty) :
    petals F c H ⊆ insertedB F c H := by
  intro P hP
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hP, petal_new hF hH hP⟩

theorem childA_subset (F : CNF V) (c : ℕ) (H : Clause V) :
    childA F c H ⊆ F ∪ {H} := by
  intro C hC
  rcases Finset.mem_insert.mp (absorb_subset _ hC) with rfl | hC
  · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hC).1

theorem childB_subset (F : CNF V) (c : ℕ) (H : Clause V) :
    childB F c H ⊆ F ∪ insertedB F c H := by
  intro C hC
  by_cases hCF : C ∈ F
  · exact Finset.mem_union_left _ hCF
  · apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hCF⟩
    rcases Finset.mem_union.mp (absorb_subset _ hC) with hC | hC
    · rcases Finset.mem_union.mp hC with hC | hC
      · exact False.elim (hCF (Finset.mem_sdiff.mp hC).1)
      · exact Finset.mem_union_left _ hC
    · exact Finset.mem_union_right _ hC

theorem insertedB_disjoint (F : CNF V) (c : ℕ) (H : Clause V) :
    Disjoint F (insertedB F c H) := Finset.disjoint_sdiff

theorem removed_childA_contains_core {F : CNF V} {c : ℕ} {H C : Clause V}
    (hF : SunflowerBranch.Antichain F) (hproper : H.card < c)
    (hC : C ∈ F) (hremoved : C ∉ childA F c H) : H ⊂ C := by
  by_cases hsel : C ∈ selected F c H
  · exact core_strict_subset hsel hproper
  · have hraw : C ∈ insert H (F \ selected F c H) :=
      Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hC, hsel⟩)
    have hex : ∃ E ∈ insert H (F \ selected F c H), E ⊂ C := by
      by_contra h
      exact hremoved (Finset.mem_filter.mpr ⟨hraw, h⟩)
    obtain ⟨E, hE, hEC⟩ := hex
    rcases Finset.mem_insert.mp hE with rfl | hE
    · exact hEC
    · exact False.elim ((Finset.ssubset_iff_subset_ne.mp hEC).2
        (hF E (Finset.mem_sdiff.mp hE).1 C hC
          (Finset.ssubset_iff_subset_ne.mp hEC).1))

theorem removed_childB_contains_inserted {F : CNF V} {c : ℕ} {H C : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty)
    (hC : C ∈ F) (hremoved : C ∉ childB F c H) :
    ∃ P ∈ insertedB F c H, P ⊂ C := by
  by_cases hsel : C ∈ selected F c H
  · exact ⟨C \ H, petals_subset_insertedB hF hH
      (Finset.mem_image.mpr ⟨C, hsel, rfl⟩), petal_strict_subset hsel hH⟩
  · have hraw : C ∈ ((F \ selected F c H) ∪ petals F c H) ∪ negatedCoreUnits H :=
      Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hC, hsel⟩))
    have hex : ∃ E ∈ ((F \ selected F c H) ∪ petals F c H) ∪ negatedCoreUnits H,
        E ⊂ C := by
      by_contra h
      exact hremoved (Finset.mem_filter.mpr ⟨hraw, h⟩)
    obtain ⟨E, hE, hEC⟩ := hex
    have hEF : E ∉ F := by
      intro hEF
      exact (Finset.ssubset_iff_subset_ne.mp hEC).2
        (hF E hEF C hC (Finset.ssubset_iff_subset_ne.mp hEC).1)
    refine ⟨E, Finset.mem_sdiff.mpr ⟨?_, hEF⟩, hEC⟩
    rcases Finset.mem_union.mp hE with hE | hE
    · rcases Finset.mem_union.mp hE with hE | hE
      · exact False.elim (hEF (Finset.mem_sdiff.mp hE).1)
      · exact Finset.mem_union_left _ hE
    · exact Finset.mem_union_right _ hE

theorem insertedB_nonempty {F : CNF V} {c : ℕ} {H P : Clause V}
    (hproper : H.card < c) (hP : P ∈ insertedB F c H) : P.Nonempty := by
  rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hP).1 with hP | hP
  · apply Finset.card_pos.mp
    rw [petal_card hP]
    exact Nat.sub_pos_of_lt hproper
  · obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hP
    exact Finset.singleton_nonempty _

theorem insertedB_width_lt {F : CNF V} {c : ℕ} {H P : Clause V}
    (hH : H.Nonempty) (hproper : H.card < c) (hP : P ∈ insertedB F c H) :
    P.card < c := by
  have hHpos := Finset.card_pos.mpr hH
  rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hP).1 with hP | hP
  · rw [petal_card hP]
    omega
  · obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hP
    rw [Finset.card_singleton]
    omega

theorem selected_card_le_insertedB_width {F : CNF V} {c : ℕ} {H : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty) :
    (selected F c H).card ≤ ((insertedB F c H).filter
      fun P => P.card = c - H.card).card := by
  rw [← petals_card]
  apply Finset.card_le_card
  intro P hP
  exact Finset.mem_filter.mpr ⟨petals_subset_insertedB hF hH hP, petal_card hP⟩

theorem unit_retained_childA {F : CNF V} {c : ℕ} {H U : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty) (hproper : H.card < c)
    (hU : U ∈ F) (hcard : U.card = 1) : U ∈ childA F c H := by
  by_contra h
  have hlt := Finset.card_lt_card (removed_childA_contains_core hF hproper hU h)
  have hpos := Finset.card_pos.mpr hH
  omega

theorem unit_retained_childB {F : CNF V} {c : ℕ} {H U : Clause V}
    (hF : SunflowerBranch.Antichain F) (hH : H.Nonempty) (hproper : H.card < c)
    (hU : U ∈ F) (hcard : U.card = 1) : U ∈ childB F c H := by
  by_contra h
  obtain ⟨P, hP, hPU⟩ := removed_childB_contains_inserted hF hH hU h
  have hpos := Finset.card_pos.mpr (insertedB_nonempty hproper hP)
  have hlt := Finset.card_lt_card hPU
  omega

theorem childA_antichain (F : CNF V) (c : ℕ) (H : Clause V) :
    SunflowerBranch.Antichain (childA F c H) := SunflowerBranch.antichain_absorb _

theorem childB_antichain (F : CNF V) (c : ℕ) (H : Clause V) :
    SunflowerBranch.Antichain (childB F c H) := SunflowerBranch.antichain_absorb _

theorem childA_not_tautological {F : CNF V} {c : ℕ} {H : Clause V}
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hsel : (selected F c H).Nonempty) :
    ∀ C ∈ childA F c H, ¬ C.IsTautology := by
  intro C hC
  rcases Finset.mem_insert.mp (absorb_subset _ hC) with hCH | hC
  · subst C
    obtain ⟨D, hD⟩ := hsel
    exact SunflowerBranch.not_tautology_of_subset (mem_selected.mp hD).2.2
      (hnt D (selected_subset F c H hD))
  · exact hnt C (Finset.mem_sdiff.mp hC).1

theorem childB_not_tautological {F : CNF V} {c : ℕ} {H : Clause V}
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) :
    ∀ C ∈ childB F c H, ¬ C.IsTautology := by
  intro C hC
  rcases Finset.mem_union.mp (absorb_subset _ hC) with hC | hC
  · rcases Finset.mem_union.mp hC with hC | hC
    · exact hnt C (Finset.mem_sdiff.mp hC).1
    · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
      exact SunflowerBranch.not_tautology_of_subset Finset.sdiff_subset
        (hnt D (selected_subset F c H hD))
  · obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hC
    rintro ⟨a, ha, hna⟩
    have ha' := Finset.mem_singleton.mp ha
    have hna' := Finset.mem_singleton.mp hna
    have h := congrArg Literal.positive (ha' ▸ hna')
    cases l with
    | mk v p => cases p <;> cases h

theorem childA_widthAtMost {F : CNF V} {c k : ℕ} {H : Clause V}
    (hwidth : WidthAtMost k F) (hsel : (selected F c H).Nonempty)
    (hproper : H.card < c) : WidthAtMost k (childA F c H) := by
  intro C hC
  rcases Finset.mem_union.mp (childA_subset F c H hC) with hC | hC
  · exact hwidth C hC
  · have hCH := Finset.mem_singleton.mp hC
    obtain ⟨D, hD⟩ := hsel
    have hck : c ≤ k := (mem_selected.mp hD).2.1 ▸ hwidth D (selected_subset F c H hD)
    rw [hCH]
    exact hproper.le.trans hck

theorem childB_widthAtMost {F : CNF V} {c k : ℕ} {H : Clause V}
    (hwidth : WidthAtMost k F) (hsel : (selected F c H).Nonempty)
    (hH : H.Nonempty) (hproper : H.card < c) : WidthAtMost k (childB F c H) := by
  intro C hC
  rcases Finset.mem_union.mp (childB_subset F c H hC) with hC | hC
  · exact hwidth C hC
  · obtain ⟨D, hD⟩ := hsel
    have hck : c ≤ k := (mem_selected.mp hD).2.1 ▸ hwidth D (selected_subset F c H hD)
    exact (insertedB_width_lt hH hproper hC).le.trans hck

open scoped BigOperators

theorem literalMass_selected (F : CNF V) (c : ℕ) (H : Clause V) :
    SunflowerBranch.literalMass (selected F c H) = (selected F c H).card * c := by
  exact Finset.sum_const_nat fun _ hC => (mem_selected.mp hC).2.1

theorem literalMass_petals (F : CNF V) (c : ℕ) (H : Clause V) :
    SunflowerBranch.literalMass (petals F c H) =
      (selected F c H).card * (c - H.card) := by
  rw [← petals_card]
  exact Finset.sum_const_nat fun _ hP => petal_card hP

theorem literalMass_negatedCoreUnits (H : Clause V) :
    SunflowerBranch.literalMass (negatedCoreUnits H) = H.card := by
  have hinj : Set.InjOn (fun l : Literal V => ({l.negate} : Clause V)) H := by
    intro l _ m _ heq
    have hneg := Finset.singleton_injective heq
    simpa only [Literal.negate_negate] using congrArg Literal.negate hneg
  unfold SunflowerBranch.literalMass negatedCoreUnits
  rw [Finset.sum_image hinj]
  simp

theorem literalMass_childA_lt {F : CNF V} {c : ℕ} {H : Clause V}
    (hsel : (selected F c H).Nonempty) (hproper : H.card < c) :
    SunflowerBranch.literalMass (childA F c H) < SunflowerBranch.literalMass F := by
  obtain ⟨C, hC⟩ := hsel
  have hlt : H.card < SunflowerBranch.literalMass (selected F c H) :=
    (Finset.card_lt_card (core_strict_subset hC hproper)).trans_le
      (SunflowerBranch.clause_card_le_literalMass hC)
  have habsorb := SunflowerBranch.literalMass_absorb_le (insert H (F \ selected F c H))
  have hinsert := SunflowerBranch.literalMass_insert_le (F \ selected F c H) H
  have hsplit := SunflowerBranch.literalMass_sdiff (selected_subset F c H)
  change SunflowerBranch.literalMass (childA F c H) ≤ _ at habsorb
  omega

theorem literalMass_childB_lt {F : CNF V} {c : ℕ} {H : Clause V}
    (hH : H.Nonempty) (hproper : H.card < c) (hsize : 2 ≤ (selected F c H).card) :
    SunflowerBranch.literalMass (childB F c H) < SunflowerBranch.literalMass F := by
  have hmul : H.card < (selected F c H).card * H.card := by
    simpa using Nat.mul_lt_mul_of_pos_right (show 1 < (selected F c H).card by omega)
      (Finset.card_pos.mpr hH)
  have hlt : SunflowerBranch.literalMass (petals F c H) +
      SunflowerBranch.literalMass (negatedCoreUnits H) <
      SunflowerBranch.literalMass (selected F c H) := by
    rw [literalMass_petals, literalMass_negatedCoreUnits, literalMass_selected]
    calc
      (selected F c H).card * (c - H.card) + H.card <
          (selected F c H).card * (c - H.card) + (selected F c H).card * H.card :=
        Nat.add_lt_add_left hmul _
      _ = (selected F c H).card * c := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hproper.le]
  have habsorb := SunflowerBranch.literalMass_absorb_le
    (((F \ selected F c H) ∪ petals F c H) ∪ negatedCoreUnits H)
  have hunits := SunflowerBranch.literalMass_union_le
    ((F \ selected F c H) ∪ petals F c H) (negatedCoreUnits H)
  have hpetals := SunflowerBranch.literalMass_union_le (F \ selected F c H) (petals F c H)
  have hsplit := SunflowerBranch.literalMass_sdiff (selected_subset F c H)
  change SunflowerBranch.literalMass (childB F c H) ≤ _ at habsorb
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch
