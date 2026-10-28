import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamily

open scoped BigOperators
open Finset

abbrev IndexTuple (m d : ℕ) := Fin d → Fin m
abbrev CoeffTuple (d : ℕ) := Fin d → ZMod 3
abbrev Candidate (m d : ℕ) := IndexTuple m d × CoeffTuple d

def eval {m d : ℕ} (h : Candidate m d) (v : Fin m → ZMod 3) : ZMod 3 :=
  ∑ j, h.2 j * v (h.1 j)

def supportCard {m : ℕ} (v : Fin m → ZMod 3) : ℕ :=
  (univ.filter fun i => v i ≠ 0).card

def detectingCard {m d : ℕ} (v : Fin m → ZMod 3) : ℕ :=
  (univ.filter fun h : Candidate m d => eval h v ≠ 0).card

/-- Repeated coordinate occurrences are combined in the ternary field. -/
def row {m d : ℕ} (h : Candidate m d) : Fin m → ZMod 3 := fun i =>
  ∑ j, if h.1 j = i then h.2 j else 0

theorem row_dot {m d : ℕ} (h : Candidate m d) (v : Fin m → ZMod 3) :
    (∑ i, row h i * v i) = eval h v := by
  simp only [row, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [ite_mul ]

theorem row_support_le {m d : ℕ} (h : Candidate m d) :
    supportCard (row h) ≤ d := by
  classical
  have sub : (univ.filter fun i => row h i ≠ 0) ⊆ univ.image h.1 := by
    intro i hi
    by_contra hn
    have he : ∀ j, h.1 j ≠ i := by
      intro j hj
      exact hn (mem_image.mpr ⟨j, mem_univ j, hj⟩)
    have hrow : row h i = 0 := by
      simp only [row]
      apply Finset.sum_eq_zero
      intro j _
      exact ite_eq_right (he j)
    exact (Finset.mem_filter.mp hi).2 hrow
  calc
    supportCard (row h) ≤ (univ.image h.1).card := card_le_card sub
    _ ≤ (univ : Finset (Fin d)).card := card_image_le
    _ = d := by simp

theorem candidate_card (m d : ℕ) :
    Fintype.card (Candidate m d) = (3 * m) ^ d := by
  simp [Candidate, IndexTuple, CoeffTuple, mul_pow, Nat.mul_comm]

private def coeffMap {m d : ℕ} (e : IndexTuple m d) (v : Fin m → ZMod 3) :
    CoeffTuple d →+ ZMod 3 where
  toFun c := ∑ j, c j * v (e j)
  map_zero' := by simp
  map_add' c c' := by simp [add_mul, Finset.sum_add_distrib]

private theorem coeffMap_surjective {m d : ℕ} (e : IndexTuple m d)
    (v : Fin m → ZMod 3) (hit : ∃ j, v (e j) ≠ 0) :
    Function.Surjective (coeffMap e v) := by
  obtain ⟨j, hj⟩ := hit
  intro a
  refine ⟨Pi.single j (a / v (e j)), ?_⟩
  simp [coeffMap, Pi.single_apply, hj]

theorem coeff_detection {m d : ℕ} (e : IndexTuple m d)
    (v : Fin m → ZMod 3) (hit : ∃ j, v (e j) ≠ 0) :
    3 * (univ.filter fun c : CoeffTuple d => eval (e, c) v ≠ 0).card =
      2 * Fintype.card (CoeffTuple d) := by
  classical
  let f := coeffMap e v
  have surj : Function.Surjective f := coeffMap_surjective e v hit
  have fiber (a : ZMod 3) :
      (univ.filter fun c => f c = a).card = (univ.filter fun c => f c = 0).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (surj a) (surj 0)
  have total : Fintype.card (CoeffTuple d) =
      3 * (univ.filter fun c => f c = 0).card := by
    calc
      _ = ∑ a : ZMod 3, (univ.filter fun c => f c = a).card := by
        simpa using (Finset.card_eq_sum_card_fiberwise
          (s := (univ : Finset (CoeffTuple d))) (t := (univ : Finset (ZMod 3)))
          (f := f) (by intro x hx; simp))
      _ = _ := by simp_rw [fiber]; simp
  have partition :
      (univ.filter fun c : CoeffTuple d => f c = 0).card +
        (univ.filter fun c : CoeffTuple d => f c ≠ 0).card =
          Fintype.card (CoeffTuple d) := by
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (CoeffTuple d))) (fun c => f c = 0))
  change 3 * (univ.filter fun c : CoeffTuple d => f c ≠ 0).card = _
  omega

private theorem pow_add_linear_lower (a b d : ℕ) :
    a ^ (d + 1) + (d + 1) * b * a ^ d ≤ (a + b) ^ (d + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := Nat.mul_le_mul_right (a + b) ih
    simp only [pow_succ] at h ⊢
    nlinarith [Nat.zero_le (d * b * b * a ^ d), Nat.zero_le (b * b * a ^ d)]

theorem miss_power_le_half {m w d : ℕ} (hm : 0 < m) (hw : w ≤ m)
    (hd : m ≤ d * w) : 2 * (m - w) ^ d ≤ m ^ d := by
  obtain ⟨d, rfl⟩ : ∃ e, d = e + 1 := by
    have : d ≠ 0 := by intro h; simp [h] at hd; omega
    exact ⟨d - 1, by omega⟩
  have h := pow_add_linear_lower (m - w) w d
  rw [Nat.sub_add_cancel hw] at h
  have hmul := Nat.mul_le_mul_right ((m - w) ^ d) hd
  have hmul' := Nat.mul_le_mul_right ((m - w) ^ d) (Nat.sub_le m w)
  rw [pow_succ] at h ⊢
  nlinarith

def hitCard {m d : ℕ} (v : Fin m → ZMod 3) : ℕ :=
  (univ.filter fun e : IndexTuple m d => ∃ j, v (e j) ≠ 0).card

theorem miss_card {m d : ℕ} (v : Fin m → ZMod 3) :
    (univ.filter fun e : IndexTuple m d => ∀ j, v (e j) = 0).card =
      (m - supportCard v) ^ d := by
  classical
  have hz : (univ.filter fun i => v i = 0).card = m - supportCard v := by
    have h : (univ.filter fun i => v i = 0).card + supportCard v = m := by
      simpa [supportCard] using
        (Finset.card_filter_add_card_filter_not
          (s := (univ : Finset (Fin m))) (fun i => v i = 0))
    omega
  have heq : (univ.filter fun e : IndexTuple m d => ∀ j, v (e j) = 0) =
      Fintype.piFinset (fun _ : Fin d => univ.filter fun i => v i = 0) := by
    ext e
    simp
  rw [heq, Fintype.card_piFinset_const, hz]

theorem hit_card_lower {m d : ℕ} (v : Fin m → ZMod 3) (hm : 0 < m)
    (heavy : m ≤ d * supportCard v) : m ^ d ≤ 2 * hitCard (d := d) v := by
  classical
  have hw : supportCard v ≤ m := by
    simpa [supportCard] using
      (Finset.card_filter_le (univ : Finset (Fin m)) (fun i => v i ≠ 0))
  have hp := miss_power_le_half hm hw heavy
  have partition := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (IndexTuple m d))) (fun e => ∃ j, v (e j) ≠ 0)
  simp only [not_exists, not_not] at partition
  rw [miss_card] at partition
  have hc : Fintype.card (IndexTuple m d) = m ^ d := by
    simp [IndexTuple ]
  simp only [Finset.card_univ, hc] at partition
  change hitCard v + (m - supportCard v) ^ d = m ^ d at partition
  omega

theorem detecting_card_sum {m d : ℕ} (v : Fin m → ZMod 3) :
    detectingCard (d := d) v =
      ∑ e : IndexTuple m d,
        (univ.filter fun c : CoeffTuple d => eval (e, c) v ≠ 0).card := by
  classical
  simp only [detectingCard, Finset.card_filter, Fintype.sum_prod_type]

theorem detecting_card_exact {m d : ℕ} (v : Fin m → ZMod 3) :
    3 * detectingCard (d := d) v =
      2 * Fintype.card (CoeffTuple d) * hitCard (d := d) v := by
  classical
  have per (e : IndexTuple m d) :
      3 * (univ.filter fun c : CoeffTuple d => eval (e, c) v ≠ 0).card =
        if ∃ j, v (e j) ≠ 0 then 2 * Fintype.card (CoeffTuple d) else 0 := by
    split_ifs with hit
    · exact coeff_detection e v hit
    · have hzero : ∀ j, v (e j) = 0 := by simpa using hit
      simp [eval, hzero]
  rw [detecting_card_sum, Finset.mul_sum]
  simp_rw [per]
  rw [← Finset.sum_filter]
  simp [hitCard, Nat.mul_comm]

/-- At least one third of the indexed sparse rows detect any vector whose
support times the tuple length is at least the ambient dimension. -/
theorem detecting_card_lower {m d : ℕ} (v : Fin m → ZMod 3) (hm : 0 < m)
    (heavy : m ≤ d * supportCard v) :
    Fintype.card (Candidate m d) ≤ 3 * detectingCard (d := d) v := by
  have h := Nat.mul_le_mul_right (Fintype.card (CoeffTuple d))
    (hit_card_lower v hm heavy)
  rw [detecting_card_exact]
  simpa [Candidate, IndexTuple, Fintype.card_fun, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using h

/-- The same detection estimate, stated using the actual combined row. -/
theorem sparse_row_detection {m d : ℕ} (v : Fin m → ZMod 3) (hm : 0 < m)
    (heavy : m ≤ d * supportCard v) :
    (3 * m) ^ d ≤
      3 * (univ.filter fun h : Candidate m d => (∑ i, row h i * v i) ≠ 0).card := by
  simpa only [row_dot, ← candidate_card, detectingCard] using
    detecting_card_lower v hm heavy

theorem candidate_card_pos {m d : ℕ} (hm : 0 < m) :
    0 < Fintype.card (Candidate m d) := by
  rw [candidate_card]
  exact pow_pos (by omega) d

end SubexponentialSAT.SqrtLog.HashFamily

end OAI.Algorithms
