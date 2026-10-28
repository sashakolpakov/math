import OAI.Analysis.Fourier.SquareFunction.Dyadic.Cover
import OAI.Analysis.Fourier.Wave.Basic

open OAI.Analysis.Fourier.Wave

/-! Actual dyadic boxes obtained by repeated bisection in every coordinate. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set BoxIntegral
open scoped ENNReal

noncomputable def dyadicBox {ι : Type*} (I : Box ι) : List (Set ι) → Box ι
  | [] => I
  | s :: l => dyadicBox (I.splitCenterBox s) l

theorem dyadicBox_le {ι : Type*} (I : Box ι) (l : List (Set ι)) : dyadicBox I l ≤ I := by
  induction l generalizing I with
  | nil => exact le_rfl
  | cons s l ih => exact (ih (I.splitCenterBox s)).trans (I.splitCenterBox_le s)

theorem dyadicBox_append {ι : Type*} (I : Box ι) (l m : List (Set ι)) :
    dyadicBox I (l ++ m) = dyadicBox (dyadicBox I l) m := by
  induction l generalizing I with
  | nil => rfl
  | cons s l ih => exact ih (I.splitCenterBox s)

/-- Any two descendants of the same box are nested or disjoint. -/
theorem dyadicBox_laminar {ι : Type*} (I : Box ι) (l m : List (Set ι)) :
    (dyadicBox I l : Set (ι → ℝ)) ⊆ dyadicBox I m ∨
      (dyadicBox I m : Set (ι → ℝ)) ⊆ dyadicBox I l ∨
        Disjoint (dyadicBox I l : Set (ι → ℝ)) (dyadicBox I m) := by
  induction l generalizing I m with
  | nil => exact Or.inr (Or.inl (dyadicBox_le I m))
  | cons s l ih =>
    cases m with
    | nil => exact Or.inl (dyadicBox_le I (s :: l))
    | cons t m =>
      by_cases h : s = t
      · subst t
        exact ih (I.splitCenterBox s) m
      · exact Or.inr (Or.inr ((I.disjoint_splitCenterBox h).mono
          (dyadicBox_le (I.splitCenterBox s) l) (dyadicBox_le (I.splitCenterBox t) m)))

noncomputable def dyadicFamily {ι : Type*} [Fintype ι] (I : Box ι) : ℕ → Finset (Set (ι → ℝ)) := by
  classical
  exact fun N => match N with
    | 0 => {(I : Set (ι → ℝ))}
    | N + 1 => insert (I : Set (ι → ℝ))
        (Finset.univ.biUnion fun s : Set ι => dyadicFamily (I.splitCenterBox s) N)

theorem exists_word_of_mem_dyadicFamily {ι : Type*} [Fintype ι]
    (I : Box ι) {N : ℕ} {A : Set (ι → ℝ)} (hA : A ∈ dyadicFamily I N) :
    ∃ l : List (Set ι), l.length ≤ N ∧ A = (dyadicBox I l : Set (ι → ℝ)) := by
  classical
  induction N generalizing I with
  | zero =>
    have h : A = (I : Set (ι → ℝ)) := by simpa [dyadicFamily] using hA
    exact ⟨[], by simp, h⟩
  | succ N ih =>
    simp only [dyadicFamily, Finset.mem_insert, Finset.mem_biUnion,
      Finset.mem_univ, true_and] at hA
    rcases hA with h | ⟨s, hs⟩
    · exact ⟨[], by simp, h⟩
    · obtain ⟨l, hl, rfl⟩ := ih (I.splitCenterBox s) hs
      exact ⟨s :: l, by simpa using Nat.succ_le_succ hl, rfl⟩

theorem dyadicBox_mem_dyadicFamily {ι : Type*} [Fintype ι]
    (I : Box ι) (l : List (Set ι)) {N : ℕ} (hl : l.length ≤ N) :
    (dyadicBox I l : Set (ι → ℝ)) ∈ dyadicFamily I N := by
  classical
  induction N generalizing I l with
  | zero =>
    have h : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
    subst l
    simp [dyadicBox, dyadicFamily]
  | succ N ih =>
    cases l with
    | nil => simp [dyadicBox, dyadicFamily]
    | cons s l =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      exact ⟨s, Finset.mem_univ s, ih (I.splitCenterBox s) l (Nat.succ_le_succ_iff.mp hl)⟩

theorem dyadicFamily_laminar {ι : Type*} [Fintype ι] (I : Box ι) (N : ℕ) :
    IsLaminar (dyadicFamily I N) := by
  intro A hA B hB
  obtain ⟨l, -, rfl⟩ := exists_word_of_mem_dyadicFamily I hA
  obtain ⟨m, -, rfl⟩ := exists_word_of_mem_dyadicFamily I hB
  exact dyadicBox_laminar I l m

theorem dyadicFamily_mono {ι : Type*} [Fintype ι] (I : Box ι) : Monotone (dyadicFamily I) := by
  intro N M hNM Q hQ
  obtain ⟨l, hl, rfl⟩ := exists_word_of_mem_dyadicFamily I hQ
  exact dyadicBox_mem_dyadicFamily I l (hl.trans hNM)

theorem dyadicFamily_measurable {ι : Type*} [Fintype ι] (I : Box ι) (N : ℕ)
    {A : Set (ι → ℝ)} (hA : A ∈ dyadicFamily I N) : MeasurableSet A := by
  obtain ⟨l, -, rfl⟩ := exists_word_of_mem_dyadicFamily I hA
  exact (dyadicBox I l).measurableSet_coe

/-- Exact dyadic parent/child volume ratio. -/
theorem volume_splitCenterBox {ι : Type*} [Fintype ι] (I : Box ι) (s : Set ι) :
    volume (I.splitCenterBox s : Set (ι → ℝ)) =
      ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι)⁻¹ * volume (I : Set (ι → ℝ)) := by
  simp only [Box.coe_eq_pi, Real.volume_pi_Ioc, Box.upper_sub_lower_splitCenterBox]
  simp_rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), div_eq_mul_inv]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, ← inv_pow]
  simp only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹),
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  exact mul_comm _ _

theorem volume_box_ne_zero {ι : Type*} [Fintype ι] (I : Box ι) :
    volume (I : Set (ι → ℝ)) ≠ 0 := by
  rw [Box.coe_eq_pi, Real.volume_pi_Ioc]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr (I.lower_lt_upper i))

theorem volume_parent_eq_mul_child {ι : Type*} [Fintype ι] (I : Box ι) (s : Set ι) :
    volume (I : Set (ι → ℝ)) = ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι) *
      volume (I.splitCenterBox s : Set (ι → ℝ)) := by
  rw [volume_splitCenterBox, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity :
    0 ≤ (2 : ℝ) ^ Fintype.card ι), mul_inv_cancel₀ (by positivity :
    (2 : ℝ) ^ Fintype.card ι ≠ 0), ENNReal.ofReal_one, one_mul]

theorem splitCenterBox_ssubset {ι : Type*} [Nonempty ι] (I : Box ι) (s : Set ι) :
    (I.splitCenterBox s : Set (ι → ℝ)) ⊂ (I : Set (ι → ℝ)) := by
  classical
  have hs : s ≠ sᶜ := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    by_cases hi : i ∈ s
    · exact (h ▸ hi : i ∈ sᶜ) hi
    · exact hi (h.symm ▸ (hi : i ∈ sᶜ))
  refine ⟨I.splitCenterBox_le s, ?_⟩
  intro hback
  obtain ⟨x, hx⟩ := (I.splitCenterBox sᶜ).nonempty_coe
  exact Set.disjoint_left.mp (I.disjoint_splitCenterBox hs)
    (hback (I.splitCenterBox_le sᶜ hx)) hx

/-- Every non-root member has a strict dyadic parent in the same finite family,
and the parent's volume is exactly `2^n` times the child's. -/
theorem dyadicFamily_parent {ι : Type*} [Fintype ι] [Nonempty ι]
    (I : Box ι) (N : ℕ) {Q : Set (ι → ℝ)} (hQ : Q ∈ dyadicFamily I N)
    (hroot : Q ≠ (I : Set (ι → ℝ))) :
    ∃ P ∈ dyadicFamily I N, Q ⊂ P ∧
      volume P = ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι) * volume Q := by
  obtain ⟨l, hl, rfl⟩ := exists_word_of_mem_dyadicFamily I hQ
  have hl0 : l ≠ [] := by
    intro h
    subst l
    exact hroot rfl
  have he : l = l.dropLast ++ [l.getLast hl0] := (List.dropLast_append_getLast hl0).symm
  have hb : dyadicBox I l = (dyadicBox I l.dropLast).splitCenterBox (l.getLast hl0) := by
    calc
      _ = dyadicBox I (l.dropLast ++ [l.getLast hl0]) := congrArg (dyadicBox I) he
      _ = _ := dyadicBox_append I l.dropLast [l.getLast hl0]
  refine ⟨(dyadicBox I l.dropLast : Set (ι → ℝ)),
    dyadicBox_mem_dyadicFamily I l.dropLast ?_, ?_, ?_⟩
  · simp only [List.length_dropLast]
    omega
  · rw [hb]
    exact splitCenterBox_ssubset (dyadicBox I l.dropLast) (l.getLast hl0)
  · rw [hb]
    exact volume_parent_eq_mul_child (dyadicBox I l.dropLast) (l.getLast hl0)

/-- The same coordinate box as a subset of the Euclidean Fourier space. -/
def euclideanBox {n : ℕ} (I : Box (Fin n)) : Set (Space n) :=
  WithLp.ofLp ⁻¹' (I : Set (Fin n → ℝ))

theorem measurable_euclideanBox {n : ℕ} (I : Box (Fin n)) : MeasurableSet (euclideanBox I) :=
  I.measurableSet_coe.preimage (PiLp.volume_preserving_ofLp (Fin n)).measurable

theorem volume_euclideanBox {n : ℕ} (I : Box (Fin n)) :
    volume (euclideanBox I) = volume (I : Set (Fin n → ℝ)) :=
  (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage I.measurableSet_coe.nullMeasurableSet

end OAI.Analysis.Fourier.SquareFunction
