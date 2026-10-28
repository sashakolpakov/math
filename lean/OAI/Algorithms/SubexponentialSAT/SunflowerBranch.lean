import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SAT

namespace OAI.Algorithms

/-!
# Literal-set sunflower branching

Concrete CNF children and their semantic union, together with the absorption
invariants used by the cumulative-insertion argument. Opposite polarities are
distinct literals; no variable-disjointness premise is used.
-/

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT

universe u
variable {V : Type u} [DecidableEq V]

/-- The antichain convention at each normalized node. -/
def Antichain (F : CNF V) : Prop :=
  ∀ C ∈ F, ∀ D ∈ F, C ⊆ D → C = D

theorem antichain_absorb (F : CNF V) : Antichain (absorb F) := by
  intro C hC D hD hCD
  exact absorb_antichain hD hC hCD

theorem clause_union_true_iff (a : Assignment V) (C D : Clause V) :
    (C ∪ D).eval a = true ↔ C.eval a = true ∨ D.eval a = true := by
  simp only [Clause.eval_eq_true]
  constructor
  · rintro ⟨l, hl, ht⟩
    rcases Finset.mem_union.mp hl with hC | hD
    · exact Or.inl ⟨l, hC, ht⟩
    · exact Or.inr ⟨l, hD, ht⟩
  · rintro (⟨l, hl, ht⟩ | ⟨l, hl, ht⟩)
    · exact ⟨l, Finset.mem_union_left D hl, ht⟩
    · exact ⟨l, Finset.mem_union_right C hl, ht⟩

theorem cnf_union_true_iff (a : Assignment V) (F G : CNF V) :
    (F ∪ G).eval a = true ↔ F.eval a = true ∧ G.eval a = true := by
  simp only [CNF.eval_eq_true]
  constructor
  · intro h
    exact ⟨fun C hC => h C (Finset.mem_union_left G hC),
      fun C hC => h C (Finset.mem_union_right F hC)⟩
  · rintro ⟨hF, hG⟩ C hC
    rcases Finset.mem_union.mp hC with h | h
    · exact hF C h
    · exact hG C h

/-- Add a common literal-set core to each petal. -/
def clauses (H : Clause V) (P : CNF V) : CNF V := P.image fun p => H ∪ p

/-- The unselected clauses are retained in each branch. -/
def childA (F : CNF V) (H : Clause V) (P : CNF V) : CNF V :=
  absorb (insert H (F \ clauses H P))

def childB (F : CNF V) (H : Clause V) (P : CNF V) : CNF V :=
  absorb ((F \ clauses H P) ∪ P)

theorem clauses_true_iff (a : Assignment V) (H : Clause V) (P : CNF V) :
    (clauses H P).eval a = true ↔ H.eval a = true ∨ P.eval a = true := by
  constructor
  · intro h
    by_cases hH : H.eval a = true
    · exact Or.inl hH
    · right
      apply (CNF.eval_eq_true a P).mpr
      intro p hp
      have hc := (CNF.eval_eq_true a (clauses H P)).mp h (H ∪ p)
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      exact ((clause_union_true_iff a H p).mp hc).resolve_left hH
  · intro h
    apply (CNF.eval_eq_true a (clauses H P)).mpr
    intro C hC
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
    apply (clause_union_true_iff a H p).mpr
    exact h.imp_right (fun hP => (CNF.eval_eq_true a P).mp hP p hp)

/-- The semantic identity holds for arbitrary petals, independently of the
sunflower's combinatorial disjointness properties. -/
theorem eval_children_iff (a : Assignment V) (F : CNF V) (H : Clause V)
    (P : CNF V) (hsub : clauses H P ⊆ F) :
    F.eval a = true ↔
      (childA F H P).eval a = true ∨ (childB F H P).eval a = true := by
  have split : F = (F \ clauses H P) ∪ clauses H P :=
    (Finset.sdiff_union_of_subset hsub).symm
  have hF : F.eval a = true ↔
      (F \ clauses H P).eval a = true ∧ (H.eval a = true ∨ P.eval a = true) := by
    conv_lhs => rw [split]
    rw [cnf_union_true_iff, clauses_true_iff]
  have hA : (childA F H P).eval a = true ↔
      H.eval a = true ∧ (F \ clauses H P).eval a = true := by
    simp only [childA, eval_absorb, CNF.eval_insert, Bool.and_eq_true]
  have hB : (childB F H P).eval a = true ↔
      (F \ clauses H P).eval a = true ∧ P.eval a = true := by
    rw [childB, eval_absorb, cnf_union_true_iff]
  rw [hF, hA, hB]
  constructor
  · rintro ⟨hR, hH | hP⟩
    · exact Or.inl ⟨hH, hR⟩
    · exact Or.inr ⟨hR, hP⟩
  · rintro (⟨hH, hR⟩ | ⟨hR, hP⟩)
    · exact ⟨hR, Or.inl hH⟩
    · exact ⟨hR, Or.inr hP⟩

theorem eval_children (a : Assignment V) (F : CNF V) (H : Clause V)
    (P : CNF V) (hsub : clauses H P ⊆ F) :
    F.eval a = ((childA F H P).eval a || (childB F H P).eval a) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [Bool.or_eq_true] using eval_children_iff a F H P hsub

theorem satisfiable_children_iff (F : CNF V) (H : Clause V)
    (P : CNF V) (hsub : clauses H P ⊆ F) :
    Satisfiable F ↔ Satisfiable (childA F H P) ∨ Satisfiable (childB F H P) := by
  constructor
  · rintro ⟨a, ha⟩
    rcases (eval_children_iff a F H P hsub).mp ha with h | h
    · exact Or.inl ⟨a, h⟩
    · exact Or.inr ⟨a, h⟩
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · exact ⟨a, (eval_children_iff a F H P hsub).mpr (Or.inl ha)⟩
    · exact ⟨a, (eval_children_iff a F H P hsub).mpr (Or.inr ha)⟩

theorem satisfyingAssignments_children [Fintype V] (F : CNF V) (H : Clause V)
    (P : CNF V) (hsub : clauses H P ⊆ F) :
    satisfyingAssignments F = satisfyingAssignments (childA F H P) ∪
      satisfyingAssignments (childB F H P) := by
  ext a
  simp only [mem_satisfyingAssignments, Finset.mem_union]
  exact eval_children_iff a F H P hsub

/-- Generic absorption replacement; a sunflower is one source of its hypotheses. -/
def replace (F S N : CNF V) : CNF V := absorb ((F \ S) ∪ N)

theorem replace_subset (F S N : CNF V) : replace F S N ⊆ F ∪ N := by
  intro C hC
  rcases Finset.mem_union.mp (absorb_subset _ hC) with h | h
  · exact Finset.mem_union_left N (Finset.mem_sdiff.mp h).1
  · exact Finset.mem_union_right F h

omit [DecidableEq V] in
/-- An inserted strict subset of an old clause has no old clause below it. -/
theorem no_old_subset_new {F N : CNF V} (hF : Antichain F)
    (hnew : ∀ D ∈ N, ∃ C ∈ F, D ⊂ C)
    {D E : Clause V} (hD : D ∈ N) (hE : E ∈ F) : ¬ E ⊆ D := by
  intro hED
  obtain ⟨C, hC, hDC⟩ := hnew D hD
  obtain ⟨hDC, hne⟩ := Finset.ssubset_iff_subset_ne.mp hDC
  have hEC := hF E hE C hC (hED.trans hDC)
  have hCD : C ⊆ D := hEC ▸ hED
  exact hne (Finset.Subset.antisymm hDC hCD)

omit [DecidableEq V] in
theorem new_not_mem_old {F N : CNF V} (hF : Antichain F)
    (hnew : ∀ D ∈ N, ∃ C ∈ F, D ⊂ C) {D : Clause V} (hD : D ∈ N) : D ∉ F := by
  intro hDF
  exact no_old_subset_new hF hnew hD hDF (Finset.Subset.refl _)

/-- Every proposed insertion survives absorption. -/
theorem inserted_survive {F S N : CNF V} (hF : Antichain F) (hN : Antichain N)
    (hnew : ∀ D ∈ N, ∃ C ∈ F, D ⊂ C) : N ⊆ replace F S N := by
  intro D hD
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_union_right _ hD, ?_⟩
  rintro ⟨E, hE, hED⟩
  obtain ⟨hED, hne⟩ := Finset.ssubset_iff_subset_ne.mp hED
  rcases Finset.mem_union.mp hE with hE | hE
  · exact no_old_subset_new hF hnew hD (Finset.mem_sdiff.mp hE).1 hED
  · exact hne (hN E hE D hD hED)

/-- Every deleted old clause has a strict-subset witness among new clauses. -/
theorem removed_contains_inserted {F S N : CNF V} (hF : Antichain F)
    (hselected : ∀ C ∈ S, ∃ D ∈ N, D ⊂ C)
    {C : Clause V} (hC : C ∈ F) (hremoved : C ∉ replace F S N) :
    ∃ D ∈ N, D ⊂ C := by
  by_cases hCS : C ∈ S
  · exact hselected C hCS
  · have hraw : C ∈ (F \ S) ∪ N :=
      Finset.mem_union_left N (Finset.mem_sdiff.mpr ⟨hC, hCS⟩)
    have hn : ¬ ¬ ∃ D ∈ (F \ S) ∪ N, D ⊂ C := by
      intro hn
      exact hremoved (Finset.mem_filter.mpr ⟨hraw, hn⟩)
    obtain ⟨D, hD, hDC⟩ := Classical.not_not.mp hn
    rcases Finset.mem_union.mp hD with hD | hD
    · obtain ⟨hsub, hne⟩ := Finset.ssubset_iff_subset_ne.mp hDC
      exact False.elim (hne (hF D (Finset.mem_sdiff.mp hD).1 C hC hsub))
    · exact ⟨D, hD, hDC⟩

theorem replacement_antichain (F S N : CNF V) : Antichain (replace F S N) :=
  antichain_absorb _

end SubexponentialSAT.SunflowerBranch

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
universe u
variable {V : Type u} [DecidableEq V]

/-- A uniform literal-set sunflower with a nonempty core and at least two
petals. Nonemptiness of each petal is a theorem, not a field. -/
structure Sunflower (V : Type u) [DecidableEq V] (d : ℕ) where
  core : Clause V
  petals : CNF V
  core_nonempty : core.Nonempty
  two_le : 2 ≤ petals.card
  disjoint_core : ∀ p ∈ petals, Disjoint core p
  pairwise_disjoint : ∀ p ∈ petals, ∀ q ∈ petals, p ≠ q → Disjoint p q
  uniform : ∀ p ∈ petals, (core ∪ p).card = d

namespace Sunflower
variable {d : ℕ} (s : Sunflower V d)

theorem petals_nonempty : s.petals.Nonempty :=
  Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) s.two_le)

theorem petal_card_eq {p q : Clause V} (hp : p ∈ s.petals) (hq : q ∈ s.petals) :
    p.card = q.card := by
  apply Nat.add_left_cancel (n := s.core.card)
  rw [← Finset.card_union_of_disjoint (s.disjoint_core p hp),
    ← Finset.card_union_of_disjoint (s.disjoint_core q hq), s.uniform p hp, s.uniform q hq]

theorem petal_nonempty {p : Clause V} (hp : p ∈ s.petals) : p.Nonempty := by
  by_contra hempty
  have hpempty : p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  obtain ⟨a, ha, q, hq, haq⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) s.two_le)
  obtain ⟨q, hq, hne⟩ : ∃ q ∈ s.petals, q ≠ p := by
    by_cases hap : a = p
    · exact ⟨q, hq, fun hqp => haq (hap.trans hqp.symm)⟩
    · exact ⟨a, ha, hap⟩
  have hcard : q.card = 0 := by
    rw [s.petal_card_eq hq hp, hpempty, Finset.card_empty]
  exact hne ((Finset.card_eq_zero.mp hcard).trans hpempty.symm)

theorem core_strict_subset {p : Clause V} (hp : p ∈ s.petals) :
    s.core ⊂ s.core ∪ p := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.subset_union_left, ?_⟩
  intro heq
  obtain ⟨l, hl⟩ := s.petal_nonempty hp
  have hcore : l ∈ s.core := heq.symm ▸ Finset.mem_union_right s.core hl
  exact Finset.disjoint_left.mp (s.disjoint_core p hp) hcore hl

theorem petal_strict_subset {p : Clause V} (hp : p ∈ s.petals) :
    p ⊂ s.core ∪ p := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.subset_union_right, ?_⟩
  intro heq
  obtain ⟨l, hl⟩ := s.core_nonempty
  have hpetal : l ∈ p := heq.symm ▸ Finset.mem_union_left p hl
  exact Finset.disjoint_left.mp (s.disjoint_core p hp) hl hpetal

theorem core_card_lt : s.core.card < d := by
  obtain ⟨p, hp⟩ := s.petals_nonempty
  exact lt_of_lt_of_eq (Finset.card_lt_card (s.core_strict_subset hp)) (s.uniform p hp)

theorem petal_card_lt {p : Clause V} (hp : p ∈ s.petals) : p.card < d := by
  exact lt_of_lt_of_eq (Finset.card_lt_card (s.petal_strict_subset hp)) (s.uniform p hp)

theorem petals_antichain : Antichain s.petals := by
  intro p hp q hq hpq
  exact Finset.eq_of_subset_of_card_le hpq (s.petal_card_eq hq hp).le

theorem union_injective : Set.InjOn (fun p => s.core ∪ p) s.petals := by
  intro p hp q hq heq
  change s.core ∪ p = s.core ∪ q at heq
  apply Finset.Subset.antisymm
  · intro l hl
    have hu : l ∈ s.core ∪ q := heq ▸ Finset.mem_union_right s.core hl
    rcases Finset.mem_union.mp hu with hcore | hq
    · exact False.elim (Finset.disjoint_left.mp (s.disjoint_core p hp) hcore hl)
    · exact hq
  · intro l hl
    have hu : l ∈ s.core ∪ p := heq.symm ▸ Finset.mem_union_right s.core hl
    rcases Finset.mem_union.mp hu with hcore | hp
    · exact False.elim (Finset.disjoint_left.mp (s.disjoint_core q hq) hcore hl)
    · exact hp

theorem clauses_card : (clauses s.core s.petals).card = s.petals.card :=
  Finset.card_image_iff.mpr s.union_injective

private theorem union_singleton_eq_insert (F : CNF V) (C : Clause V) :
    F ∪ {C} = insert C F := by
  ext D
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
  exact or_comm

theorem core_mem_childA {F : CNF V} (hF : Antichain F)
    (hsub : clauses s.core s.petals ⊆ F) : s.core ∈ childA F s.core s.petals := by
  have hnew : ∀ D ∈ ({s.core} : CNF V), ∃ C ∈ F, D ⊂ C := by
    intro D hD
    have hD' : D = s.core := Finset.mem_singleton.mp hD
    subst D
    obtain ⟨p, hp⟩ := s.petals_nonempty
    exact ⟨s.core ∪ p, hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩), s.core_strict_subset hp⟩
  have hsingle : Antichain ({s.core} : CNF V) := by
    intro C hC D hD _
    exact (Finset.mem_singleton.mp hC).trans (Finset.mem_singleton.mp hD).symm
  have hsurvive := inserted_survive (S := clauses s.core s.petals) hF hsingle hnew
    (Finset.mem_singleton_self s.core)
  simpa only [childA, replace, union_singleton_eq_insert] using hsurvive

theorem petals_subset_childB {F : CNF V} (hF : Antichain F)
    (hsub : clauses s.core s.petals ⊆ F) : s.petals ⊆ childB F s.core s.petals := by
  apply inserted_survive hF s.petals_antichain
  intro p hp
  exact ⟨s.core ∪ p, hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩), s.petal_strict_subset hp⟩

theorem core_new {F : CNF V} (hF : Antichain F)
    (hsub : clauses s.core s.petals ⊆ F) : s.core ∉ F := by
  intro hcore
  obtain ⟨p, hp⟩ := s.petals_nonempty
  have heq := hF s.core hcore (s.core ∪ p)
    (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩)) Finset.subset_union_left
  exact (Finset.ssubset_iff_subset_ne.mp (s.core_strict_subset hp)).2 heq

theorem petal_new {F : CNF V} (hF : Antichain F)
    (hsub : clauses s.core s.petals ⊆ F) {p : Clause V} (hp : p ∈ s.petals) : p ∉ F := by
  intro hpF
  have heq := hF p hpF (s.core ∪ p)
    (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩)) Finset.subset_union_right
  exact (Finset.ssubset_iff_subset_ne.mp (s.petal_strict_subset hp)).2 heq

theorem removed_childA_contains_core {F : CNF V} (hF : Antichain F)
    {C : Clause V} (hC : C ∈ F) (hremoved : C ∉ childA F s.core s.petals) :
    s.core ⊂ C := by
  have hselected : ∀ C ∈ clauses s.core s.petals,
      ∃ D ∈ ({s.core} : CNF V), D ⊂ C := by
    intro C hC
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨s.core, Finset.mem_singleton_self _, s.core_strict_subset hp⟩
  have hremoved' : C ∉ replace F (clauses s.core s.petals) {s.core} := by
    simpa only [replace, childA, union_singleton_eq_insert] using hremoved
  obtain ⟨D, hD, hDC⟩ := removed_contains_inserted hF hselected hC hremoved'
  simpa only [Finset.mem_singleton.mp hD] using hDC

theorem removed_childB_contains_petal {F : CNF V} (hF : Antichain F)
    {C : Clause V} (hC : C ∈ F) (hremoved : C ∉ childB F s.core s.petals) :
    ∃ p ∈ s.petals, p ⊂ C := by
  apply removed_contains_inserted hF ?_ hC hremoved
  intro C hC
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
  exact ⟨p, hp, s.petal_strict_subset hp⟩

end Sunflower
end SubexponentialSAT.SunflowerBranch

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
universe u
variable {V : Type u} [DecidableEq V]

/-- Extract the petals by removing a known common core. -/
def petalFamily (F : CNF V) (H : Clause V) : CNF V :=
  F.image fun C => C \ H

theorem sdiff_injective_on {F : CNF V} {H : Clause V}
    (hcore : ∀ C ∈ F, H ⊆ C) : Set.InjOn (fun C => C \ H) F := by
  intro C hC D hD heq
  change C \ H = D \ H at heq
  calc
    C = H ∪ (C \ H) := (Finset.union_sdiff_of_subset (hcore C hC)).symm
    _ = H ∪ (D \ H) := congrArg (fun P => H ∪ P) heq
    _ = D := Finset.union_sdiff_of_subset (hcore D hD)

theorem petalFamily_card {F : CNF V} {H : Clause V} (hcore : ∀ C ∈ F, H ⊆ C) :
    (petalFamily F H).card = F.card :=
  Finset.card_image_iff.mpr (sdiff_injective_on hcore)

theorem clauses_petalFamily {F : CNF V} {H : Clause V} (hcore : ∀ C ∈ F, H ⊆ C) :
    clauses H (petalFamily F H) = F := by
  ext C
  constructor
  · intro hC
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hp
    have hDC : D = C := (Finset.union_sdiff_of_subset (hcore D hD)).symm.trans heq
    exact hDC ▸ hD
  · intro hC
    exact Finset.mem_image.mpr ⟨C \ H, Finset.mem_image.mpr ⟨C, hC, rfl⟩,
      Finset.union_sdiff_of_subset (hcore C hC)⟩

/-- Construct the branching data from the usual common-intersection definition
of a uniform sunflower. The pairwise hypothesis is exactly the second conjunct
of `SubexponentialSAT.Sunflower.IsSunflowerWithCore`. -/
def Sunflower.ofClauses (F : CNF V) (H : Clause V) (d : ℕ)
    (hH : H.Nonempty) (hcard : 2 ≤ F.card) (hcore : ∀ C ∈ F, H ⊆ C)
    (hpair : ∀ C ∈ F, ∀ D ∈ F, C ≠ D → C ∩ D = H)
    (hwidth : ∀ C ∈ F, C.card = d) : Sunflower V d where
  core := H
  petals := petalFamily F H
  core_nonempty := hH
  two_le := (petalFamily_card hcore).symm ▸ hcard
  disjoint_core := by
    intro p hp
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hp
    apply Finset.disjoint_left.mpr
    intro l hlH hl
    exact (Finset.mem_sdiff.mp hl).2 hlH
  pairwise_disjoint := by
    intro p hp q hq hpq
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hq
    have hCD : C ≠ D := fun heq => hpq (congrArg (fun E => E \ H) heq)
    apply Finset.disjoint_left.mpr
    intro l hlC hlD
    have hinter : l ∈ C ∩ D :=
      Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hlC).1, (Finset.mem_sdiff.mp hlD).1⟩
    have hlH : l ∈ H := hpair C hC D hD hCD ▸ hinter
    exact (Finset.mem_sdiff.mp hlC).2 hlH
  uniform := by
    intro p hp
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.union_sdiff_of_subset (hcore C hC)]
    exact hwidth C hC

@[simp] theorem Sunflower.ofClauses_selected (F : CNF V) (H : Clause V) (d : ℕ)
    (hH : H.Nonempty) (hcard : 2 ≤ F.card) (hcore : ∀ C ∈ F, H ⊆ C)
    (hpair : ∀ C ∈ F, ∀ D ∈ F, C ≠ D → C ∩ D = H)
    (hwidth : ∀ C ∈ F, C.card = d) :
    clauses (Sunflower.ofClauses F H d hH hcard hcore hpair hwidth).core
      (Sunflower.ofClauses F H d hH hcard hcore hpair hwidth).petals = F :=
  clauses_petalFamily hcore

omit [DecidableEq V] in
/-- Tautology-freeness is inherited by every subclause. -/
theorem not_tautology_of_subset {C D : Clause V} (hCD : C ⊆ D)
    (hD : ¬ D.IsTautology) : ¬ C.IsTautology := by
  rintro ⟨l, hl, hn⟩
  exact hD ⟨l, hCD hl, hCD hn⟩

theorem replacement_not_tautological {F S N : CNF V}
    (hF : ∀ C ∈ F, ¬ C.IsTautology)
    (hN : ∀ D ∈ N, ∃ C ∈ F, D ⊆ C) :
    ∀ C ∈ replace F S N, ¬ C.IsTautology := by
  intro C hC
  rcases Finset.mem_union.mp (replace_subset F S N hC) with h | h
  · exact hF C h
  · obtain ⟨D, hD, hCD⟩ := hN C h
    exact not_tautology_of_subset hCD (hF D hD)

namespace Sunflower
variable {d : ℕ} (s : Sunflower V d)

theorem childA_subset (F : CNF V) : childA F s.core s.petals ⊆ F ∪ {s.core} := by
  intro C hC
  have hraw := absorb_subset _ hC
  rcases Finset.mem_insert.mp hraw with h | h
  · exact Finset.mem_union_right F (Finset.mem_singleton.mpr h)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp h).1

theorem childB_subset (F : CNF V) : childB F s.core s.petals ⊆ F ∪ s.petals :=
  replace_subset F (clauses s.core s.petals) s.petals

theorem childA_antichain (F : CNF V) : Antichain (childA F s.core s.petals) :=
  antichain_absorb _

theorem childB_antichain (F : CNF V) : Antichain (childB F s.core s.petals) :=
  antichain_absorb _

theorem childA_not_tautological {F : CNF V}
    (hF : ∀ C ∈ F, ¬ C.IsTautology) (hsub : clauses s.core s.petals ⊆ F) :
    ∀ C ∈ childA F s.core s.petals, ¬ C.IsTautology := by
  intro C hC
  rcases Finset.mem_union.mp (s.childA_subset F hC) with h | h
  · exact hF C h
  · have heq := Finset.mem_singleton.mp h
    subst C
    obtain ⟨p, hp⟩ := s.petals_nonempty
    exact not_tautology_of_subset Finset.subset_union_left
      (hF (s.core ∪ p) (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))

theorem childB_not_tautological {F : CNF V}
    (hF : ∀ C ∈ F, ¬ C.IsTautology) (hsub : clauses s.core s.petals ⊆ F) :
    ∀ C ∈ childB F s.core s.petals, ¬ C.IsTautology := by
  apply replacement_not_tautological hF
  intro p hp
  exact ⟨s.core ∪ p, hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩), Finset.subset_union_right⟩

end Sunflower
end SubexponentialSAT.SunflowerBranch

namespace SubexponentialSAT.SunflowerBranch
open SubexponentialSAT.SAT
universe u
variable {V : Type u} [DecidableEq V]

theorem antichain_normalize (F : CNF V) : Antichain (normalize F) :=
  antichain_absorb _

/-- Neither normalized child introduces a satisfying assignment of its parent. -/
theorem childA_implies_parent (a : Assignment V) (F : CNF V) (H : Clause V)
    (P : CNF V) (hsub : clauses H P ⊆ F)
    (h : (childA F H P).eval a = true) : F.eval a = true :=
  (eval_children_iff a F H P hsub).mpr (Or.inl h)

theorem childB_implies_parent (a : Assignment V) (F : CNF V) (H : Clause V)
    (P : CNF V) (hsub : clauses H P ⊆ F)
    (h : (childB F H P).eval a = true) : F.eval a = true :=
  (eval_children_iff a F H P hsub).mpr (Or.inr h)

namespace Sunflower
variable {d : ℕ} (s : Sunflower V d)

theorem two_le_width (s : Sunflower V d) : 2 ≤ d := by
  have hcore : 1 ≤ s.core.card := Finset.card_pos.mpr s.core_nonempty
  exact (Nat.succ_le_succ hcore).trans (Nat.succ_le_of_lt s.core_card_lt)

theorem childA_no_empty {F : CNF V} (hF : (∅ : Clause V) ∉ F) :
    (∅ : Clause V) ∉ childA F s.core s.petals := by
  intro h
  rcases Finset.mem_union.mp (s.childA_subset F h) with h | h
  · exact hF h
  · have heq := Finset.mem_singleton.mp h
    exact s.core_nonempty.ne_empty heq.symm

theorem childB_no_empty {F : CNF V} (hF : (∅ : Clause V) ∉ F) :
    (∅ : Clause V) ∉ childB F s.core s.petals := by
  intro h
  rcases Finset.mem_union.mp (s.childB_subset F h) with h | h
  · exact hF h
  · exact (s.petal_nonempty h).ne_empty rfl

end Sunflower
end SubexponentialSAT.SunflowerBranch

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
open scoped BigOperators
universe u
variable {V : Type u} [DecidableEq V]

/-- A finite structural measure for recursive branching; no runtime assertion. -/
def literalMass (F : CNF V) : ℕ := ∑ C ∈ F, C.card

omit [DecidableEq V] in
theorem literalMass_mono {F G : CNF V} (h : F ⊆ G) : literalMass F ≤ literalMass G :=
  Finset.sum_le_sum_of_subset h

theorem literalMass_absorb_le (F : CNF V) : literalMass (absorb F) ≤ literalMass F :=
  literalMass_mono (absorb_subset F)

omit [DecidableEq V] in
@[simp] theorem literalMass_singleton (C : Clause V) : literalMass ({C} : CNF V) = C.card := by
  simp [literalMass]

theorem literalMass_union_le (F G : CNF V) :
    literalMass (F ∪ G) ≤ literalMass F + literalMass G := by
  calc
    literalMass (F ∪ G) ≤ literalMass (F ∪ G) + literalMass (F ∩ G) := Nat.le_add_right _ _
    _ = literalMass F + literalMass G := Finset.sum_union_inter

theorem literalMass_insert_le (F : CNF V) (C : Clause V) :
    literalMass (insert C F) ≤ literalMass F + C.card := by
  have heq : insert C F = F ∪ {C} := by
    ext D
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    exact or_comm
  rw [heq]
  simpa only [literalMass_singleton] using literalMass_union_le F {C}

theorem literalMass_sdiff {F S : CNF V} (h : S ⊆ F) :
    literalMass (F \ S) + literalMass S = literalMass F := Finset.sum_sdiff h

omit [DecidableEq V] in
theorem clause_card_le_literalMass {F : CNF V} {C : Clause V} (hC : C ∈ F) :
    C.card ≤ literalMass F := by
  have hsub : ({C} : CNF V) ⊆ F := Finset.singleton_subset_iff.mpr hC
  simpa only [literalMass_singleton] using literalMass_mono hsub

namespace Sunflower
variable {d : ℕ} (s : Sunflower V d)

theorem core_card_lt_literalMass : s.core.card < literalMass (clauses s.core s.petals) := by
  obtain ⟨p, hp⟩ := s.petals_nonempty
  exact lt_of_lt_of_le (Finset.card_lt_card (s.core_strict_subset hp))
    (clause_card_le_literalMass (Finset.mem_image.mpr ⟨p, hp, rfl⟩))

theorem petals_literalMass_lt : literalMass s.petals < literalMass (clauses s.core s.petals) := by
  change (∑ p ∈ s.petals, p.card) < ∑ C ∈ s.petals.image (fun p => s.core ∪ p), C.card
  rw [Finset.sum_image s.union_injective]
  exact Finset.sum_lt_sum_of_nonempty s.petals_nonempty
    (fun p hp => Finset.card_lt_card (s.petal_strict_subset hp))

/-- Core replacement strictly decreases total literal occurrences. -/
theorem literalMass_childA_lt {F : CNF V} (hsub : clauses s.core s.petals ⊆ F) :
    literalMass (childA F s.core s.petals) < literalMass F := by
  calc
    literalMass (childA F s.core s.petals)
        ≤ literalMass (insert s.core (F \ clauses s.core s.petals)) := literalMass_absorb_le _
    _ ≤ literalMass (F \ clauses s.core s.petals) + s.core.card := literalMass_insert_le _ _
    _ < literalMass (F \ clauses s.core s.petals) + literalMass (clauses s.core s.petals) :=
      Nat.add_lt_add_left s.core_card_lt_literalMass _
    _ = literalMass F := literalMass_sdiff hsub

/-- Petal replacement strictly decreases total literal occurrences. -/
theorem literalMass_childB_lt {F : CNF V} (hsub : clauses s.core s.petals ⊆ F) :
    literalMass (childB F s.core s.petals) < literalMass F := by
  calc
    literalMass (childB F s.core s.petals)
        ≤ literalMass ((F \ clauses s.core s.petals) ∪ s.petals) := literalMass_absorb_le _
    _ ≤ literalMass (F \ clauses s.core s.petals) + literalMass s.petals := literalMass_union_le _ _
    _ < literalMass (F \ clauses s.core s.petals) + literalMass (clauses s.core s.petals) :=
      Nat.add_lt_add_left s.petals_literalMass_lt _
    _ = literalMass F := literalMass_sdiff hsub

theorem width_le_of_present {F : CNF V} {k : ℕ} (hF : WidthAtMost k F)
    (hsub : clauses s.core s.petals ⊆ F) : d ≤ k := by
  obtain ⟨p, hp⟩ := s.petals_nonempty
  calc
    d = (s.core ∪ p).card := (s.uniform p hp).symm
    _ ≤ k := hF (s.core ∪ p) (hsub (Finset.mem_image.mpr ⟨p, hp, rfl⟩))

theorem widthAtMost_childA {F : CNF V} {k : ℕ} (hF : WidthAtMost k F)
    (hsub : clauses s.core s.petals ⊆ F) : WidthAtMost k (childA F s.core s.petals) := by
  intro C hC
  rcases Finset.mem_union.mp (s.childA_subset F hC) with h | h
  · exact hF C h
  · have heq := Finset.mem_singleton.mp h
    subst C
    exact s.core_card_lt.le.trans (s.width_le_of_present hF hsub)

theorem widthAtMost_childB {F : CNF V} {k : ℕ} (hF : WidthAtMost k F)
    (hsub : clauses s.core s.petals ⊆ F) : WidthAtMost k (childB F s.core s.petals) := by
  intro C hC
  rcases Finset.mem_union.mp (s.childB_subset F hC) with h | h
  · exact hF C h
  · exact (s.petal_card_lt h).le.trans (s.width_le_of_present hF hsub)

end Sunflower
end SubexponentialSAT.SunflowerBranch

end OAI.Algorithms
