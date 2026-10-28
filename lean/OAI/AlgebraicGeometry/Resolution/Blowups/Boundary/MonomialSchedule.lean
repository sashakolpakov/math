import OAI.AlgebraicGeometry.Resolution.Blowups.MonomialTermination
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Monomial Schedule -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialSchedule.Construction

noncomputable section

/-! Finite common-center schedules for labelled monomials, independent of local coordinates. -/

universe u

def boundaryFaceWeight {ι : Type u} (a : ι → ℕ) (S : Finset ι) : ℕ :=
  ∑ j ∈ S, a j

def boundaryScheduleExponents {ι : Type u} (a : ι → ℕ) (b : ℕ) (C : Finset ι) :
    Option ι → ℕ
  | none => boundaryFaceWeight a C - b
  | some j => a j

def boundaryExceptionalFace {ι : Type u} [DecidableEq ι] (S : Finset ι) (i : ι) : Finset (Option ι) :=
  insert none ((S.erase i).map Function.Embedding.some)

def boundaryFaceBranches {ι : Type u} [DecidableEq ι] (C S : Finset ι) : List (Finset (Option ι)) :=
  if C ⊆ S then C.toList.map (boundaryExceptionalFace S)
    else [S.map Function.Embedding.some]

def boundaryScheduleFaces {ι : Type u} [DecidableEq ι] (C : Finset ι) (L : List (Finset ι)) :
    List (Finset (Option ι)) := L.flatMap (boundaryFaceBranches C)

def boundarySchedulePotential {ι : Type u} (d : ℕ) (a : ι → ℕ)
    (L : List (Finset ι)) : ℕ := (L.map (fun S => (d + 1) ^ boundaryFaceWeight a S)).sum

theorem boundaryExceptionalFace_card {ι : Type u} [DecidableEq ι] (S : Finset ι) (i : ι) (hi : i ∈ S) :
    (boundaryExceptionalFace S i).card = S.card := by
  classical
  have hn : none ∉ (S.erase i).map Function.Embedding.some := by simp
  rw [boundaryExceptionalFace, Finset.card_insert_of_notMem hn, Finset.card_map,
    Finset.card_erase_of_mem hi]
  have hpos := Finset.card_pos.mpr ⟨i, hi⟩
  omega

theorem boundaryExceptionalFace_weight_lt {ι : Type u} [DecidableEq ι]
    (a : ι → ℕ) (b : ℕ) (C S : Finset ι) (hC : MonomialTermination.Construction.MinimalMonomialCenter a b C)
    (hCS : C ⊆ S) (i : ι) (hi : i ∈ C) :
    boundaryFaceWeight (boundaryScheduleExponents a b C) (boundaryExceptionalFace S i) <
      boundaryFaceWeight a S := by
  classical
  have he := Finset.sum_erase_add S a (hCS hi)
  have hlt := MonomialTermination.Construction.monomial_exceptional_exponent_lt a b C hC i hi
  rw [boundaryFaceWeight, boundaryExceptionalFace, Finset.sum_insert (by simp), Finset.sum_map]
  simp only [Function.Embedding.some_apply, boundaryScheduleExponents]
  change (∑ j ∈ C, a j) - b + ∑ j ∈ S.erase i, a j < ∑ j ∈ S, a j
  omega

theorem boundaryFaceBranches_card_bound {ι : Type u} [DecidableEq ι] (C S : Finset ι) (d : ℕ)
    (hS : S.card ≤ d) : ∀ T ∈ boundaryFaceBranches C S, T.card ≤ d := by
  classical
  intro T hT
  by_cases hCS : C ⊆ S
  · simp only [boundaryFaceBranches, ite_eq_left hCS, List.mem_map, Finset.mem_toList] at hT
    obtain ⟨i, hi, rfl⟩ := hT
    rwa [boundaryExceptionalFace_card S i (hCS hi)]
  · simp only [boundaryFaceBranches, ite_eq_right hCS, List.mem_singleton] at hT
    subst T
    simpa only [Finset.card_map] using hS

theorem boundarySchedule_list_sum_map_le_mul_length {α : Type*} (L : List α) (f : α → ℕ)
    (n : ℕ) (h : ∀ x ∈ L, f x ≤ n) : (L.map f).sum ≤ L.length * n := by
  induction L with
  | nil => simp
  | cons x L ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      have hx := h x List.mem_cons_self
      have hL := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      omega

theorem boundaryFaceBranches_potential_lt {ι : Type u} [DecidableEq ι]
    (a : ι → ℕ) (b d : ℕ) (C S : Finset ι) (hC : MonomialTermination.Construction.MinimalMonomialCenter a b C)
    (hCS : C ⊆ S) (hS : S.card ≤ d) :
    boundarySchedulePotential d (boundaryScheduleExponents a b C) (boundaryFaceBranches C S) <
      (d + 1) ^ boundaryFaceWeight a S := by
  let n := boundaryFaceWeight a S
  obtain ⟨i, hi⟩ := hC.1
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _)
    (boundaryExceptionalFace_weight_lt a b C S hC hCS i hi)
  have hCd : C.card < d + 1 := Nat.lt_succ_of_le ((Finset.card_le_card hCS).trans hS)
  have hp : ∀ j ∈ C.toList,
      (d + 1) ^ boundaryFaceWeight (boundaryScheduleExponents a b C) (boundaryExceptionalFace S j) ≤
        (d + 1) ^ (n - 1) := by
    intro j hj
    have hj' := boundaryExceptionalFace_weight_lt a b C S hC hCS j (Finset.mem_toList.mp hj)
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hsum := boundarySchedule_list_sum_map_le_mul_length C.toList
    (fun j => (d + 1) ^ boundaryFaceWeight (boundaryScheduleExponents a b C)
      (boundaryExceptionalFace S j)) ((d + 1) ^ (n - 1)) hp
  have hstrict : C.card * (d + 1) ^ (n - 1) < (d + 1) ^ n := by
    have hpow : 0 < (d + 1) ^ (n - 1) := Nat.pow_pos (by omega)
    have hmul := Nat.mul_lt_mul_of_pos_right hCd hpow
    have hn' : n = (n - 1) + 1 := by omega
    conv_rhs => rw [hn', pow_succ]
    simpa only [Nat.mul_comm] using hmul
  rw [Finset.length_toList] at hsum
  rw [boundarySchedulePotential, boundaryFaceBranches, ite_eq_left hCS, List.map_map]
  change (C.toList.map (fun j => (d + 1) ^ boundaryFaceWeight
    (boundaryScheduleExponents a b C) (boundaryExceptionalFace S j))).sum < (d + 1) ^ n
  exact hsum.trans_lt hstrict

theorem boundaryFaceBranches_potential_le {ι : Type u} [DecidableEq ι]
    (a : ι → ℕ) (b d : ℕ) (C S : Finset ι) (hC : MonomialTermination.Construction.MinimalMonomialCenter a b C)
    (hS : S.card ≤ d) :
    boundarySchedulePotential d (boundaryScheduleExponents a b C) (boundaryFaceBranches C S) ≤
      (d + 1) ^ boundaryFaceWeight a S := by
  classical
  by_cases hCS : C ⊆ S
  · exact (boundaryFaceBranches_potential_lt a b d C S hC hCS hS).le
  · simp only [boundarySchedulePotential, boundaryFaceBranches, ite_eq_right hCS,
      List.map_singleton, List.sum_singleton, boundaryFaceWeight, Finset.sum_map,
      Function.Embedding.some_apply, boundaryScheduleExponents, le_refl]

theorem boundaryScheduleFaces_card_bound {ι : Type u} [DecidableEq ι] (C : Finset ι)
    (L : List (Finset ι)) (d : ℕ) (hL : ∀ S ∈ L, S.card ≤ d) :
    ∀ T ∈ boundaryScheduleFaces C L, T.card ≤ d := by
  intro T hT
  obtain ⟨S, hS, hT⟩ := List.mem_flatMap.mp hT
  exact boundaryFaceBranches_card_bound C S d (hL S hS) T hT

theorem boundaryScheduleFaces_potential_lt {ι : Type u} [DecidableEq ι]
    (a : ι → ℕ) (b d : ℕ) (C : Finset ι) (L : List (Finset ι))
    (hC : MonomialTermination.Construction.MinimalMonomialCenter a b C) (hL : ∀ S ∈ L, S.card ≤ d)
    (hex : ∃ S ∈ L, C ⊆ S) :
    boundarySchedulePotential d (boundaryScheduleExponents a b C) (boundaryScheduleFaces C L) <
      boundarySchedulePotential d a L := by
  have hweak (K : List (Finset ι)) (hK : ∀ S ∈ K, S.card ≤ d) :
      boundarySchedulePotential d (boundaryScheduleExponents a b C) (boundaryScheduleFaces C K) ≤
        boundarySchedulePotential d a K := by
    induction K with
    | nil => simp [boundarySchedulePotential, boundaryScheduleFaces]
    | cons S K ih =>
        have hS := boundaryFaceBranches_potential_le a b d C S hC (hK S List.mem_cons_self)
        have ht := ih (fun T hT => hK T (List.mem_cons_of_mem S hT))
        simpa only [boundaryScheduleFaces, List.flatMap_cons, boundarySchedulePotential,
          List.map_append, List.sum_append, List.map_cons, List.sum_cons] using Nat.add_le_add hS ht
  induction L with
  | nil => simp at hex
  | cons S L ih =>
      have hS := hL S List.mem_cons_self
      have ht : ∀ T ∈ L, T.card ≤ d := fun T hT => hL T (List.mem_cons_of_mem S hT)
      by_cases hCS : C ⊆ S
      · have hfirst := boundaryFaceBranches_potential_lt a b d C S hC hCS hS
        have hrest := hweak L ht
        simpa only [boundaryScheduleFaces, List.flatMap_cons, boundarySchedulePotential,
          List.map_append, List.sum_append, List.map_cons, List.sum_cons] using Nat.add_lt_add_of_lt_of_le hfirst hrest
      · have hfirst := boundaryFaceBranches_potential_le a b d C S hC hS
        have hrest := ih ht (by
          obtain ⟨T, hT, hCT⟩ := hex
          rcases List.mem_cons.mp hT with rfl | hT
          · exact False.elim (hCS hCT)
          · exact ⟨T, hT, hCT⟩)
        simpa only [boundaryScheduleFaces, List.flatMap_cons, boundarySchedulePotential,
          List.map_append, List.sum_append, List.map_cons, List.sum_cons] using Nat.add_lt_add_of_le_of_lt hfirst hrest

/-- One common list of label-intersection centers, used on every coordinate chart.
The faces record possible simultaneous boundary components; they need not all occur. -/
inductive BoundaryMonomialSchedule (b : ℕ) :
    (ι : Type u) → (ι → ℕ) → List (Finset ι) → Type (u + 1)
  | terminal {ι : Type u} {a : ι → ℕ} {L : List (Finset ι)}
      (h : ∀ S ∈ L, boundaryFaceWeight a S < b) : BoundaryMonomialSchedule b ι a L
  | step {ι : Type u} {a : ι → ℕ} {L : List (Finset ι)} [DecidableEq ι]
      (C : Finset ι) (hC : MonomialTermination.Construction.MinimalMonomialCenter a b C) (hface : ∃ S ∈ L, C ⊆ S)
      (rest : BoundaryMonomialSchedule b (Option ι) (boundaryScheduleExponents a b C)
        (boundaryScheduleFaces C L)) : BoundaryMonomialSchedule b ι a L

theorem exists_boundary_monomial_schedule (b : ℕ) (hb : 0 < b) (d : ℕ) :
    ∀ (ι : Type u) (a : ι → ℕ) (L : List (Finset ι)),
      (∀ S ∈ L, S.card ≤ d) → Nonempty (Construction.BoundaryMonomialSchedule b ι a L) := by
  classical
  have go (n : ℕ) : ∀ (ι : Type u) (a : ι → ℕ) (L : List (Finset ι)),
      (∀ S ∈ L, S.card ≤ d) → boundarySchedulePotential d a L ≤ n →
      Nonempty (Construction.BoundaryMonomialSchedule b ι a L) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro ι a L hL hn
        by_cases ht : ∀ S ∈ L, boundaryFaceWeight a S < b
        · exact ⟨.terminal ht⟩
        · push Not at ht
          obtain ⟨S, hS, hweight⟩ := ht
          obtain ⟨C, hCS, hC⟩ := MonomialTermination.Construction.exists_minimal_monomial_center a b hb S hweight
          have hface : ∃ S ∈ L, C ⊆ S := ⟨S, hS, hCS⟩
          have hdrop := boundaryScheduleFaces_potential_lt a b d C L hC hL hface
          obtain ⟨T⟩ := ih _ (hdrop.trans_le hn) (Option ι) (boundaryScheduleExponents a b C)
            (boundaryScheduleFaces C L) (boundaryScheduleFaces_card_bound C L d hL) le_rfl
          exact ⟨.step C hC hface T⟩
  intro ι a L hL
  exact go (boundarySchedulePotential d a L) ι a L hL le_rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialSchedule.Construction
