import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SAT
import OAI.Algorithms.SubexponentialSAT.SparsificationConstants

namespace OAI.Algorithms

/-! The elementary sunflower bound and its literal-occurrence corollary. -/
namespace SubexponentialSAT.Sunflower

open Finset
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- A finite family with a specified common core. Empty cores are allowed. -/
def IsSunflowerWithCore (F : Finset (Finset α)) (H : Finset α) : Prop :=
  (∀ s ∈ F, H ⊆ s) ∧ ∀ s ∈ F, ∀ t ∈ F, s ≠ t → s ∩ t = H

/-- No subfamily of exactly `z` members is a sunflower, even with empty core. -/
def SunflowerFree (F : Finset (Finset α)) (z : ℕ) : Prop :=
  ∀ G ⊆ F, G.card = z → ∀ H, ¬ IsSunflowerWithCore G H

/-- The link at `x`, represented by removing `x` from sets which contain it. -/
def link (F : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  (F.filter (fun s => x ∈ s)).image (fun s => s.erase x)

theorem mem_link {F : Finset (Finset α)} {x : α} {s : Finset α} :
    s ∈ link F x ↔ ∃ t ∈ F, x ∈ t ∧ t.erase x = s := by
  simp only [link, mem_image, mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, hx⟩, he⟩
    exact ⟨t, ht, hx, he⟩
  · rintro ⟨t, ht, hx, he⟩
    exact ⟨t, ⟨ht, hx⟩, he⟩

theorem not_mem_of_mem_link {F : Finset (Finset α)} {x : α} {s : Finset α}
    (hs : s ∈ link F x) : x ∉ s := by
  obtain ⟨t, _, _, rfl⟩ := mem_link.mp hs
  exact Finset.notMem_erase x t

theorem insert_mem_of_mem_link {F : Finset (Finset α)} {x : α} {s : Finset α}
    (hs : s ∈ link F x) : insert x s ∈ F := by
  obtain ⟨t, ht, hx, rfl⟩ := mem_link.mp hs
  simpa only [insert_erase hx] using ht

theorem card_link (F : Finset (Finset α)) (x : α) :
    (link F x).card = (F.filter (fun s => x ∈ s)).card := by
  apply card_image_iff.mpr
  intro s hs t ht he
  exact erase_injOn' x (mem_filter.mp hs).2 (mem_filter.mp ht).2 he

theorem card_link_member {F : Finset (Finset α)} {x : α} {a : ℕ}
    (hF : ∀ s ∈ F, s.card = a + 1) {s : Finset α} (hs : s ∈ link F x) :
    s.card = a := by
  obtain ⟨t, ht, hx, rfl⟩ := mem_link.mp hs
  rw [card_erase_of_mem hx, hF t ht]
  omega

theorem sunflower_insert {G : Finset (Finset α)} {H : Finset α}
    (hG : IsSunflowerWithCore G H) (x : α) :
    IsSunflowerWithCore (G.image (insert x)) (insert x H) := by
  constructor
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
    exact insert_subset_insert x (hG.1 t ht)
  · intro s hs t ht hst
    obtain ⟨s', hs', rfl⟩ := mem_image.mp hs
    obtain ⟨t', ht', rfl⟩ := mem_image.mp ht
    rw [← insert_inter_distrib]
    rw [hG.2 s' hs' t' ht' (fun he => hst (congrArg (insert x) he))]

theorem card_insert_image {F G : Finset (Finset α)} {x : α}
    (hGF : G ⊆ link F x) : (G.image (insert x)).card = G.card := by
  apply card_image_iff.mpr
  intro s hs t ht he
  have hxs := not_mem_of_mem_link (hGF hs)
  have hxt := not_mem_of_mem_link (hGF ht)
  have he' := congrArg (fun u : Finset α => u.erase x) he
  simpa only [erase_insert hxs, erase_insert hxt] using he'

theorem sunflowerFree_link {F : Finset (Finset α)} {z : ℕ}
    (hF : SunflowerFree F z) (x : α) : SunflowerFree (link F x) z := by
  intro G hG hcard H hflower
  apply hF (G.image (insert x)) ?_ ?_ (insert x H) (sunflower_insert hflower x)
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
    exact insert_mem_of_mem_link (hG ht)
  · rw [card_insert_image hG, hcard]


/-- Pairwise disjointness of a finite family. -/
def PairwiseDisjoint (F : Finset (Finset α)) : Prop :=
  ∀ s ∈ F, ∀ t ∈ F, s ≠ t → Disjoint s t

/-- A maximal disjoint subfamily hits every nonempty member of the original family. -/
theorem exists_disjoint_cover (F : Finset (Finset α))
    (hne : ∀ s ∈ F, s.Nonempty) :
    ∃ M ⊆ F, PairwiseDisjoint M ∧
      ∀ s ∈ F, ∃ x ∈ M.biUnion id, x ∈ s := by
  classical
  let candidates := F.powerset.filter PairwiseDisjoint
  have hemp : (∅ : Finset (Finset α)) ∈ candidates := by
    simp [candidates, PairwiseDisjoint]
  obtain ⟨M, hM, hmax⟩ := exists_max_image candidates Finset.card ⟨∅, hemp⟩
  have hMF : M ⊆ F := mem_powerset.mp (mem_filter.mp hM).1
  have hMD : PairwiseDisjoint M := (mem_filter.mp hM).2
  refine ⟨M, hMF, hMD, ?_⟩
  intro s hs
  by_contra hhit
  have hdis : ∀ t ∈ M, Disjoint s t := by
    intro t ht
    apply disjoint_left.mpr
    intro x hxs hxt
    apply hhit
    exact ⟨x, mem_biUnion.mpr ⟨t, ht, hxt⟩, hxs⟩
  have hsM : s ∉ M := by
    intro hsM
    obtain ⟨x, hx⟩ := hne s hs
    exact (disjoint_left.mp (hdis s hsM)) hx hx
  have hinsert : insert s M ∈ candidates := by
    apply mem_filter.mpr
    constructor
    · exact mem_powerset.mpr (insert_subset hs hMF)
    · intro u hu v hv huv
      rcases mem_insert.mp hu with rfl | huM
      · rcases mem_insert.mp hv with rfl | hvM
        · exact (huv rfl).elim
        · exact hdis v hvM
      · rcases mem_insert.mp hv with rfl | hvM
        · exact (hdis u huM).symm
        · exact hMD u huM v hvM huv
  have hc := hmax (insert s M) hinsert
  rw [Finset.card_insert_of_notMem hsM] at hc
  omega

theorem disjoint_card_le {F M : Finset (Finset α)} {z : ℕ}
    (hF : SunflowerFree F z) (hMF : M ⊆ F) (hM : PairwiseDisjoint M) :
    M.card ≤ z - 1 := by
  by_contra! hlarge
  have hzM : z ≤ M.card := by omega
  obtain ⟨G, hGM, hcard⟩ := exists_subset_card_eq hzM
  apply hF G (hGM.trans hMF) hcard ∅
  constructor
  · intro s hs
    exact empty_subset s
  · intro s hs t ht hst
    exact disjoint_iff_inter_eq_empty.mp (hM s (hGM hs) t (hGM ht) hst)

/-- The elementary sunflower bound, proved by induction on the common set size. -/
theorem uniform_card_le (F : Finset (Finset α)) (a z : ℕ) (_hz : 2 ≤ z)
    (hUniform : ∀ s ∈ F, s.card = a) (hFree : SunflowerFree F z) :
    F.card ≤ a.factorial * (z - 1) ^ a := by
  induction a generalizing F with
  | zero =>
    have hsub : F ⊆ {∅} := by
      intro s hs
      simpa only [mem_singleton] using card_eq_zero.mp (hUniform s hs)
    have hc := card_le_card hsub
    simpa using hc
  | succ a ih =>
    obtain ⟨M, hMF, hMD, hhit⟩ := exists_disjoint_cover F (by
      intro s hs
      apply card_pos.mp
      rw [hUniform s hs]
      omega)
    let U := M.biUnion id
    have hMC : M.card ≤ z - 1 := disjoint_card_le hFree hMF hMD
    have hUC : U.card ≤ (a + 1) * (z - 1) := by
      calc
        U.card ≤ ∑ s ∈ M, s.card := card_biUnion_le
        _ = M.card * (a + 1) := by
          rw [sum_congr rfl (fun s hs => hUniform s (hMF hs))]
          simp
        _ ≤ (z - 1) * (a + 1) := Nat.mul_le_mul_right (a + 1) hMC
        _ = (a + 1) * (z - 1) := Nat.mul_comm _ _
    have hlink : ∀ x : α,
        (F.filter (fun s => x ∈ s)).card ≤ a.factorial * (z - 1) ^ a := by
      intro x
      rw [← card_link]
      exact ih (link F x) (fun s hs => card_link_member hUniform hs)
        (sunflowerFree_link hFree x)
    have hsub : F ⊆ U.biUnion (fun x => F.filter (fun s => x ∈ s)) := by
      intro s hs
      obtain ⟨x, hxU, hxs⟩ := hhit s hs
      exact mem_biUnion.mpr ⟨x, hxU, mem_filter.mpr ⟨hs, hxs⟩⟩
    calc
      F.card ≤ (U.biUnion (fun x => F.filter (fun s => x ∈ s))).card :=
        card_le_card hsub
      _ ≤ ∑ x ∈ U, (F.filter (fun s => x ∈ s)).card := card_biUnion_le
      _ ≤ ∑ _x ∈ U, a.factorial * (z - 1) ^ a := sum_le_sum (fun x _ => hlink x)
      _ = U.card * (a.factorial * (z - 1) ^ a) := by simp
      _ ≤ ((a + 1) * (z - 1)) * (a.factorial * (z - 1) ^ a) :=
        Nat.mul_le_mul_right _ hUC
      _ = (a + 1).factorial * (z - 1) ^ (a + 1) := by
        simp [Nat.factorial_succ, pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
          Nat.mul_comm]


/-- If a uniform family exceeds the bound, it contains a sunflower of the requested size. -/
theorem exists_sunflower_of_card_gt (F : Finset (Finset α)) (a z : ℕ)
    (hz : 2 ≤ z) (hUniform : ∀ s ∈ F, s.card = a)
    (hLarge : a.factorial * (z - 1) ^ a < F.card) :
    ∃ G ⊆ F, G.card = z ∧ ∃ H, IsSunflowerWithCore G H := by
  classical
  by_contra hn
  have hFree : SunflowerFree F z := by
    intro G hG hcard H hflower
    exact hn ⟨G, hG, hcard, H, hflower⟩
  exact (Nat.not_le_of_lt hLarge) (uniform_card_le F a z hz hUniform hFree)

/-- Absence of sunflowers with nonempty core; disjoint families remain permitted. -/
def NonemptyCoreSunflowerFree (F : Finset (Finset α)) (z : ℕ) : Prop :=
  ∀ G ⊆ F, G.card = z → ∀ H, H.Nonempty → ¬ IsSunflowerWithCore G H

/-- In a link even empty-core sunflowers are forbidden, because the deleted element
is restored to their core. -/
theorem nonemptyCoreSunflowerFree_link {F : Finset (Finset α)} {z : ℕ}
    (hF : NonemptyCoreSunflowerFree F z) (x : α) :
    SunflowerFree (link F x) z := by
  intro G hG hcard H hflower
  apply hF (G.image (insert x)) ?_ ?_ (insert x H)
    ⟨x, mem_insert_self x H⟩ (sunflower_insert hflower x)
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
    exact insert_mem_of_mem_link (hG ht)
  · rw [card_insert_image hG, hcard]

/-- The number of members containing a fixed element in a uniform family with no
nonempty-core sunflower. The formula is valid even in width zero. -/
theorem occurrence_card_le (F : Finset (Finset α)) (j z : ℕ) (hz : 2 ≤ z)
    (hUniform : ∀ s ∈ F, s.card = j)
    (hFree : NonemptyCoreSunflowerFree F z) (x : α) :
    (F.filter (fun s => x ∈ s)).card ≤
      (j - 1).factorial * (z - 1) ^ (j - 1) := by
  rw [← card_link]
  apply uniform_card_le (link F x) (j - 1) z hz
  · intro s hs
    obtain ⟨t, ht, hx, rfl⟩ := mem_link.mp hs
    rw [card_erase_of_mem hx, hUniform t ht]
  · exact nonemptyCoreSunflowerFree_link hFree x

/-- Appendix A.2's per-literal bound, for width `j` inside an arbitrary family. -/
theorem literal_occurrence_le (F : Finset (Finset α)) (j z : ℕ) (hz : 2 ≤ z)
    (hFree : NonemptyCoreSunflowerFree (F.filter (fun s => s.card = j)) z)
    (x : α) :
    (F.filter (fun s => s.card = j ∧ x ∈ s)).card ≤
      (j - 1).factorial * (z - 1) ^ (j - 1) := by
  have hfilter : (F.filter (fun s => s.card = j)).filter (fun s => x ∈ s) =
      F.filter (fun s => s.card = j ∧ x ∈ s) := by
    ext s
    simp only [mem_filter, and_assoc]
  rw [← hfilter]
  apply occurrence_card_le _ j z hz ?_ hFree x
  intro s hs
  exact (mem_filter.mp hs).2

/-- Distinct unit sets give the separately specified bound `L₁ = 1`. -/
theorem unit_literal_occurrence_le (F : Finset (Finset α)) (x : α) :
    (F.filter (fun s => s.card = 1 ∧ x ∈ s)).card ≤ 1 := by
  have hsub : F.filter (fun s => s.card = 1 ∧ x ∈ s) ⊆ {{x}} := by
    intro s hs
    obtain ⟨_, hcard, hx⟩ := mem_filter.mp hs
    apply mem_singleton.mpr
    obtain ⟨y, rfl⟩ := card_eq_one.mp hcard
    have hxy : x = y := mem_singleton.mp hx
    rw [hxy]
  simpa using card_le_card hsub


/-- Summing the width-specific degrees bounds the total degree of one literal. -/
theorem literal_total_occurrence_le (F : Finset (Finset α)) (k : ℕ)
    (b : ℕ → ℕ) (x : α) (hWidth : ∀ s ∈ F, s.card ≤ k)
    (hBound : ∀ j, j ≤ k →
      (F.filter (fun s => s.card = j ∧ x ∈ s)).card ≤ b j) :
    (F.filter (fun s => x ∈ s)).card ≤ ∑ j ∈ range (k + 1), b j := by
  have hsub : F.filter (fun s => x ∈ s) ⊆
      (range (k + 1)).biUnion (fun j => F.filter (fun s => s.card = j ∧ x ∈ s)) := by
    intro s hs
    obtain ⟨hsF, hxs⟩ := mem_filter.mp hs
    apply mem_biUnion.mpr
    refine ⟨s.card, mem_range.mpr ?_, mem_filter.mpr ⟨hsF, rfl, hxs⟩⟩
    have := hWidth s hsF
    omega
  calc
    (F.filter (fun s => x ∈ s)).card ≤
        ((range (k + 1)).biUnion
          (fun j => F.filter (fun s => s.card = j ∧ x ∈ s))).card := card_le_card hsub
    _ ≤ ∑ j ∈ range (k + 1), (F.filter (fun s => s.card = j ∧ x ∈ s)).card :=
      card_biUnion_le
    _ ≤ ∑ j ∈ range (k + 1), b j := by
      apply sum_le_sum
      intro j hj
      exact hBound j (by have := mem_range.mp hj; omega)

/-- A variable has two signs, so a common literal-degree cap gives twice that cap
for the number of clauses containing the variable. -/
theorem variable_occurrence_le_of_literal_bound {V : Type*} [DecidableEq V]
    (F : SAT.CNF V) (B : ℕ)
    (hBound : ∀ x : SAT.Literal V, (F.filter (fun s => x ∈ s)).card ≤ B) :
    SAT.OccurrenceAtMost (2 * B) F := by
  intro v
  let pos : SAT.Literal V := ⟨v, true⟩
  let neg : SAT.Literal V := ⟨v, false⟩
  have hsub : F.filter (fun C => ∃ l ∈ C, l.variable = v) ⊆
      (F.filter (fun C => pos ∈ C)) ∪ (F.filter (fun C => neg ∈ C)) := by
    intro C hC
    obtain ⟨hCF, l, hl, hv⟩ := mem_filter.mp hC
    rcases l with ⟨w, sign⟩
    change w = v at hv
    subst w
    cases sign with
    | false => exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hCF, hl⟩))
    | true => exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hCF, hl⟩))
  calc
    SAT.occurrences v F ≤
        ((F.filter (fun C => pos ∈ C)) ∪ (F.filter (fun C => neg ∈ C))).card :=
      card_le_card hsub
    _ ≤ (F.filter (fun C => pos ∈ C)).card +
        (F.filter (fun C => neg ∈ C)).card := card_union_le _ _
    _ ≤ B + B := Nat.add_le_add (hBound pos) (hBound neg)
    _ = 2 * B := by omega

/-- Terminal sparsification leaves satisfy the manuscript's total variable cap.
Width zero contributes no occurrences; width one uses distinctness of clauses. -/
theorem terminal_occurrenceAtMost {V : Type*} [DecidableEq V]
    (F : SAT.CNF V) (M k : ℕ) (hM : 2 ≤ M)
    (hWidth : SAT.WidthAtMost k F)
    (hTerminal : ∀ d, 2 ≤ d → d ≤ k →
      NonemptyCoreSunflowerFree (F.filter (fun C => C.card = d))
        (SparsificationConstants.z M d)) :
    SAT.OccurrenceAtMost (SparsificationConstants.occurrenceCap M k) F := by
  apply variable_occurrence_le_of_literal_bound F
    (∑ j ∈ range (k + 1), SparsificationConstants.L M j)
  intro x
  apply literal_total_occurrence_le F k (SparsificationConstants.L M) x hWidth
  intro j hj
  by_cases htwo : 2 ≤ j
  · rw [SparsificationConstants.L_eq_threshold_formula M j htwo]
    exact literal_occurrence_le F j (SparsificationConstants.z M j)
      (SparsificationConstants.threshold_ge_two M j hM htwo)
      (hTerminal j htwo hj) x
  · have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with rfl | rfl
    · have hempty : F.filter (fun s => s.card = 0 ∧ x ∈ s) = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨s, hs⟩
        obtain ⟨_, hzero, hx⟩ := mem_filter.mp hs
        rw [card_eq_zero.mp hzero] at hx
        exact Finset.notMem_empty x hx
      rw [hempty]
      simp
    · simpa only [SparsificationConstants.L_one] using unit_literal_occurrence_le F x

end SubexponentialSAT.Sunflower

end OAI.Algorithms
