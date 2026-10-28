import OAI.Analysis.PDE.Elliptic.LaminarCover
import Mathlib.Analysis.BoxIntegral.Box.SubboxInduction

open Set BoxIntegral
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*}

/-- A dyadic descendant is specified by its successive half-box choices. -/
def dyadicBox (B : Box ι) : List (Set ι) → Box ι
  | [] => B
  | s :: w => dyadicBox (B.splitCenterBox s) w

theorem dyadicBox_le (B : Box ι) (w : List (Set ι)) : dyadicBox B w ≤ B := by
  induction w generalizing B with
  | nil => exact le_rfl
  | cons s w ih => exact (ih _).trans (B.splitCenterBox_le s)

theorem dyadicBox_width (B : Box ι) (w : List (Set ι)) (i : ι) :
    (dyadicBox B w).upper i - (dyadicBox B w).lower i =
      (B.upper i - B.lower i) / 2 ^ w.length := by
  induction w generalizing B with
  | nil => simp [dyadicBox]
  | cons s w ih =>
    simp only [dyadicBox, ih, Box.upper_sub_lower_splitCenterBox, List.length_cons,
      pow_succ, div_div]
    rw [mul_comm (2 : ℝ)]

theorem not_le_splitCenterBox [Nonempty ι] (B : Box ι) (s : Set ι) :
    ¬B ≤ B.splitCenterBox s := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hl := (Box.le_iff_bounds.mp h).1 i
  have hu := (Box.le_iff_bounds.mp h).2 i
  have hw := B.upper_sub_lower_splitCenterBox s i
  have hp := B.lower_lt_upper i
  linarith

theorem dyadicBox_disjoint_of_first_ne (B : Box ι) {s t : Set ι}
    (hst : s ≠ t) (v w : List (Set ι)) :
    Disjoint (dyadicBox B (s :: v) : Set (ι → ℝ)) (dyadicBox B (t :: w)) :=
  (B.disjoint_splitCenterBox hst).mono (dyadicBox_le _ v) (dyadicBox_le _ w)

theorem dyadicBox_laminar (B : Box ι) (v w : List (Set ι)) :
    Disjoint (dyadicBox B v : Set (ι → ℝ)) (dyadicBox B w) ∨
      dyadicBox B v ≤ dyadicBox B w ∨ dyadicBox B w ≤ dyadicBox B v := by
  induction v generalizing B w with
  | nil => exact Or.inr (Or.inr (dyadicBox_le B w))
  | cons s v ih =>
    cases w with
    | nil => exact Or.inr (Or.inl (dyadicBox_le B (s :: v)))
    | cons t w =>
      by_cases hst : s = t
      · subst t
        exact ih (B.splitCenterBox s) w
      · exact Or.inl (dyadicBox_disjoint_of_first_ne B hst v w)

/-- Strict enlargement strictly lowers the dyadic generation. -/
theorem dyadicBox_subset_length_lt [Nonempty ι] (B : Box ι)
    (v w : List (Set ι)) (hsub : dyadicBox B v ≤ dyadicBox B w) (hne : w ≠ v) :
    w.length < v.length := by
  induction v generalizing B w with
  | nil =>
    cases w with
    | nil => exact (hne rfl).elim
    | cons t w =>
      exact (not_le_splitCenterBox B t (hsub.trans (dyadicBox_le _ w))).elim
  | cons s v ih =>
    cases w with
    | nil => simp
    | cons t w =>
      by_cases hst : s = t
      · subst t
        exact Nat.succ_lt_succ (ih (B.splitCenterBox s) w hsub
          (fun h ↦ hne (congrArg (List.cons s) h)))
      · have hd := dyadicBox_disjoint_of_first_ne B hst v w
        obtain ⟨x, hx⟩ := (dyadicBox B (s :: v)).nonempty_coe
        exact (Set.disjoint_left.mp hd hx (hsub hx)).elim

/-- On a finite dyadic branch starting at a good box and ending at a
bad one, there is a good parent with a bad child containing the leaf. -/
theorem exists_dyadic_good_parent (P : Box ι → Prop) (B : Box ι)
    (w : List (Set ι)) (hroot : P B) (hleaf : ¬P (dyadicBox B w)) :
    ∃ (v : List (Set ι)) (s : Set ι), P (dyadicBox B v) ∧
      ¬P ((dyadicBox B v).splitCenterBox s) ∧
      dyadicBox B w ≤ (dyadicBox B v).splitCenterBox s := by
  induction w generalizing B with
  | nil => exact (hleaf hroot).elim
  | cons s w ih =>
    by_cases hs : P (B.splitCenterBox s)
    · obtain ⟨v, t, hv, ht, hsub⟩ := ih (B.splitCenterBox s) hs hleaf
      exact ⟨s :: v, t, hv, ht, hsub⟩
    · exact ⟨[], s, hroot, hs, dyadicBox_le _ w⟩

end OAI.Analysis.PDE.Elliptic
