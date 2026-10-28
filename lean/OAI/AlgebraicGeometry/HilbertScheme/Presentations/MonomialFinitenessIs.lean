import Mathlib.Order.WellFoundedSet
import Mathlib.Order.Minimal
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.WithBot
import Mathlib.Data.Fintype.List

/-! # Monomial Finiteness Is -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonomialFinitenessIs.MonomialFiniteness

noncomputable section

/-!
The order-theoretic finiteness underlying monomial-ideal boundedness.
Every lower subset of a finite power of the natural numbers is a finite
union of boxes with finite or infinite endpoints. Higman's lemma then
shows that these lower sets are well quasi-ordered by inclusion.
-/

variable {n : ℕ}

abbrev Exponent (n : ℕ) := Fin n → ℕ
abbrev Endpoint (n : ℕ) := Fin n → WithTop ℕ

def box (b : Endpoint n) : Set (Exponent n) :=
  {a | ∀ i, (a i : WithTop ℕ) < b i}

def boxes (L : List (Endpoint n)) : Set (Exponent n) :=
  {a | ∃ b ∈ L, a ∈ box b}

theorem box_mono {b c : Endpoint n} (h : b ≤ c) : box b ⊆ box c :=
  fun _ ha i => lt_of_lt_of_le (ha i) (h i)

theorem box_inf (b c : Endpoint n) : box (b ⊓ c) = box b ∩ box c := by
  ext a
  simp only [box, Set.mem_ofPred_eq, Pi.inf_apply, lt_inf_iff, Set.mem_inter_iff]
  exact forall_and

theorem boxes_inter (L M : List (Endpoint n)) :
    boxes (L.flatMap fun b => M.map fun c => b ⊓ c) = boxes L ∩ boxes M := by
  ext a
  constructor
  · rintro ⟨d, hd, had⟩
    obtain ⟨b, hb, hd⟩ := List.mem_flatMap.mp hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    rw [box_inf] at had
    exact ⟨⟨b, hb, had.1⟩, ⟨c, hc, had.2⟩⟩
  · rintro ⟨⟨b, hb, hab⟩, ⟨c, hc, hac⟩⟩
    refine ⟨b ⊓ c, List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr ⟨c, hc, rfl⟩⟩, ?_⟩
    rw [box_inf]
    exact ⟨hab, hac⟩

theorem exists_boxes_compl_cone (a : Exponent n) :
    ∃ L : List (Endpoint n), boxes L = {x | ¬ a ≤ x} := by
  classical
  refine ⟨(List.finRange n).map (fun i j => if j = i then (a i : WithTop ℕ) else ⊤), ?_⟩
  ext x
  simp only [boxes, Set.mem_ofPred_eq, List.mem_map, List.mem_finRange, true_and,
    exists_exists_eq_and]
  constructor
  · rintro ⟨i, hi⟩ hax
    have hx := hi i
    simp only [ite_true] at hx
    exact (WithTop.coe_lt_coe.mp hx).not_ge (hax i)
  · intro hx
    have hx' : ∃ i, x i < a i := by
      simpa only [Pi.le_def, not_forall, not_le] using hx
    obtain ⟨i, hi⟩ := hx'
    refine ⟨i, fun j => ?_⟩
    by_cases hji : j = i
    · subst j
      simpa only [ite_true] using WithTop.coe_lt_coe.mpr hi
    · simp only [ite_eq_right hji, WithTop.coe_lt_top]

theorem exists_boxes_avoid (G : Finset (Exponent n)) :
    ∃ L : List (Endpoint n), boxes L = {x | ∀ a ∈ G, ¬ a ≤ x} := by
  classical
  induction G using Finset.induction_on with
  | empty =>
      refine ⟨[⊤], ?_⟩
      ext x
      simp [boxes, box]
  | @insert a G ha ih =>
      obtain ⟨L, hL⟩ := exists_boxes_compl_cone a
      obtain ⟨M, hM⟩ := ih
      refine ⟨L.flatMap (fun b => M.map (fun c => b ⊓ c)), ?_⟩
      rw [boxes_inter, hL, hM]
      ext x
      simp

/-- Dickson's lemma gives finitely many generators of an upper exponent set. -/
theorem upper_set_finitely_generated (U : Set (Exponent n)) (hU : IsUpperSet U) :
    ∃ G : Finset (Exponent n), ∀ x, x ∈ U ↔ ∃ a ∈ G, a ≤ x := by
  classical
  let M := {a : Exponent n | Minimal (· ∈ U) a}
  have hM : IsAntichain (· ≤ ·) M := by
    intro a ha b hb hab hle
    exact hab (hb.eq_of_ge ha.prop hle).symm
  have hfin : M.Finite := hM.finite_of_wellQuasiOrdered wellQuasiOrdered_le
  refine ⟨hfin.toFinset, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨a, hax, ha⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ U) x hx
    exact ⟨a, hfin.mem_toFinset.mpr ha, hax⟩
  · rintro ⟨a, ha, hax⟩
    exact hU hax (hfin.mem_toFinset.mp ha).prop

theorem lower_set_is_boxes (D : Set (Exponent n)) (hD : IsLowerSet D) :
    ∃ L : List (Endpoint n), boxes L = D := by
  obtain ⟨G, hG⟩ := upper_set_finitely_generated Dᶜ hD.compl
  obtain ⟨L, hL⟩ := exists_boxes_avoid G
  refine ⟨L, hL.trans ?_⟩
  ext x
  have hx := (hG x).not
  simpa only [Set.mem_compl_iff, not_not, not_exists, not_and, Set.mem_ofPred_eq] using hx.symm

theorem boxes_mono_of_sublistForall₂ {L M : List (Endpoint n)}
    (h : List.SublistForall₂ (· ≤ ·) L M) : boxes L ⊆ boxes M := by
  induction h with
  | nil => simp [boxes]
  | @cons b c L M hbc h ih =>
      rintro a ⟨d, hd, had⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨c, List.mem_cons_self, box_mono hbc had⟩
      · obtain ⟨e, he, hae⟩ := ih ⟨d, hd, had⟩
        exact ⟨e, List.mem_cons_of_mem _ he, hae⟩
  | @cons_right c L M h ih =>
      intro a ha
      obtain ⟨e, he, hae⟩ := ih ha
      exact ⟨e, List.mem_cons_of_mem _ he, hae⟩

/-- Lower exponent sets, or complements of monomial ideals, are well
quasi-ordered by inclusion. This is the order-theoretic form of Maclagan's theorem. -/
theorem lower_sets_wellQuasiOrdered :
    WellQuasiOrdered (fun D E : {D : Set (Exponent n) // IsLowerSet D} => D.val ⊆ E.val) := by
  intro seq
  choose L hL using fun i => lower_set_is_boxes (seq i).val (seq i).property
  have hp : (Set.univ : Set (Endpoint n)).PartiallyWellOrderedOn (· ≤ ·) :=
    Set.partiallyWellOrderedOn_univ_iff.mpr wellQuasiOrdered_le
  have hlist := hp.partiallyWellOrderedOn_sublistForall₂ (· ≤ ·)
  obtain ⟨i, j, hij, hrel⟩ := hlist.exists_lt (f := L) (by simp)
  refine ⟨i, j, hij, ?_⟩
  change (seq i).val ⊆ (seq j).val
  rw [← hL i, ← hL j]
  exact boxes_mono_of_sublistForall₂ hrel

theorem upper_sets_reverse_wellQuasiOrdered :
    WellQuasiOrdered (fun U V : {U : Set (Exponent n) // IsUpperSet U} => V.val ⊆ U.val) := by
  intro seq
  obtain ⟨i, j, hij, h⟩ := lower_sets_wellQuasiOrdered
    (fun i => ⟨(seq i).valᶜ, (seq i).property.compl⟩)
  exact ⟨i, j, hij, Set.compl_subset_compl.mp h⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonomialFinitenessIs.MonomialFiniteness
