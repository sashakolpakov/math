import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramGrowth

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SupportProgram

def appendGrow (J : ℕ) (rows : List (List Bool)) : List (List Bool) :=
  (rows.flatMap fun xs => [xs ++ [false], xs ++ [true]]).filter (fun xs => decide (xs.count true < J))

def Correct (n J : ℕ) (rows : List (List Bool)) : Prop :=
  rows.Nodup ∧ ∀ xs, xs ∈ rows ↔ xs.length = n ∧ xs.count true < J

theorem masks_correct (n J : ℕ) : Correct n J (masks n J) :=
  ⟨masks_nodup n J, mem_masks n J⟩

theorem correct_reverse (n J : ℕ) (rows : List (List Bool)) (h : Correct n J rows) :
    Correct n J (rows.map List.reverse) := by
  refine ⟨h.1.map (by intro a b h; simpa using congrArg List.reverse h), ?_⟩
  intro xs
  constructor
  · rintro hx
    obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hx
    simpa using (h.2 ys).mp hys
  · rintro ⟨hl, hw⟩
    exact List.mem_map.mpr ⟨xs.reverse, (h.2 xs.reverse).mpr (by simpa using And.intro hl hw),
      List.reverse_reverse xs⟩

theorem grow_correct (n J : ℕ) (rows : List (List Bool)) (h : Correct n J rows) :
    Correct (n + 1) J (grow J rows) := by
  refine ⟨grow_nodup J rows h.1, ?_⟩
  intro xs
  rw [mem_grow]
  constructor
  · rintro ⟨b, ys, hys, rfl, hw⟩
    exact ⟨by simp [(h.2 ys).mp hys |>.1], hw⟩
  · rintro ⟨hl, hw⟩
    cases xs with
    | nil => simp at hl
    | cons b xs =>
        refine ⟨b, xs, (h.2 xs).mpr ⟨by simpa using hl, ?_⟩, rfl, hw⟩
        cases b <;> simp at hw ⊢ <;> omega

theorem reverse_filter (J : ℕ) (words : List (List Bool)) :
    (words.filter (fun xs => decide (xs.count true < J))).map List.reverse =
      (words.map List.reverse).filter (fun xs => decide (xs.count true < J)) := by
  induction words with
  | nil => rfl
  | cons w words ih =>
      by_cases h : w.count true < J <;> simp [h, ih]

theorem reverse_appendGrow (J : ℕ) (rows : List (List Bool)) :
    (appendGrow J rows).map List.reverse = grow J (rows.map List.reverse) := by
  rw [appendGrow, reverse_filter]
  simp [grow, List.map_flatMap, List.flatMap_map ]

theorem appendGrow_correct (n J : ℕ) (rows : List (List Bool)) (h : Correct n J rows) :
    Correct (n + 1) J (appendGrow J rows) := by
  have hr := grow_correct n J _ (correct_reverse n J rows h)
  rw [← reverse_appendGrow] at hr
  have hh := correct_reverse (n + 1) J _ hr
  simpa [List.map_map, Function.comp_def] using hh

theorem correct_perm_masks (n J : ℕ) (rows : List (List Bool)) (h : Correct n J rows) :
    rows.Perm (masks n J) := by
  apply (List.perm_ext_iff_of_nodup h.1 (masks_nodup n J)).mpr
  intro xs
  rw [h.2, mem_masks]

theorem correct_length (n J : ℕ) (rows : List (List Bool)) (h : Correct n J rows) :
    rows.length = count n J := by
  rw [(correct_perm_masks n J rows h).length_eq, masks_length]

end SubexponentialSAT.SqrtLog.SupportProgram

end OAI.Algorithms
