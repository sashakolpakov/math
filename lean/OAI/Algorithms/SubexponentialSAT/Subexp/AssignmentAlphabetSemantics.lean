import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.OneHotAlphabetProgram
import OAI.Algorithms.SubexponentialSAT.SubexpTupleRefinement
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan

namespace OAI.Algorithms

/-! The actual tuple-generator order is retained in the initializer alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

open OneHotAlphabetProgram MulticolorTypes

def oneHot {r : ℕ} (c : Fin r) : List Bool :=
  List.ofFn (fun j : Fin r => decide (c = j))

def hotAt (r i : ℕ) : List Bool := zeros i ++ true :: zeros (r - i - 1)

theorem oneHot_eq {r : ℕ} (c : Fin r) : oneHot c = hotAt r c.val := by
  apply List.ext_getElem
  · simp [oneHot, hotAt]
    omega
  · intro i hi hj
    have hir : i < r := by simpa [oneHot] using hi
    by_cases hlt : i < c.val
    · have hne : c.val ≠ i := by omega
      simp [oneHot, hotAt, hlt, Fin.ext_iff, hne]
    · by_cases he : i = c.val
      · subst i
        simp [oneHot, hotAt, Fin.ext_iff]
      · have hpos : 0 < i - c.val := by omega
        have hn : i - c.val ≠ 0 := by omega
        simp [oneHot, hotAt, List.getElem_append, hlt, Fin.ext_iff,
          Ne.symm he, List.getElem_cons, hn]

theorem rows_eq_range (i n : ℕ) :
    rows i n = (List.range' i n).reverse.map (hotAt (i + n)) := by
  induction n generalizing i with
  | zero => simp [rows]
  | succ n ih =>
      rw [rows, ih, List.range'_succ, List.reverse_cons, List.map_append, List.map_singleton]
      have he : i + 1 + n = i + (n + 1) := by omega
      rw [he]
      congr 1
      simp [word, hotAt]

theorem rows_eq_alphabet (r : ℕ) :
    rows 0 r = (List.finRange r).reverse.map oneHot := by
  rw [rows_eq_range]
  rw [Nat.zero_add, ← List.range_eq_range']
  rw [← List.map_coe_finRange r]
  simp only [List.map_reverse, List.map_map]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro c _
  exact (oneHot_eq c).symm

theorem oneHot_injective (r : ℕ) : Function.Injective (@oneHot r) := by
  intro a b h
  have he := congrFun (List.ofFn_injective h) a
  have hba : b = a := by simpa using he.symm
  exact hba.symm

def colorCode {r : ℕ} (hr : 0 < r) : StackEncoding.BlockCode (Fin r) where
  width := r
  width_pos := hr
  block := oneHot
  length_block _ := List.length_ofFn
  injective_block := oneHot_injective r

def wordBytes (r Q : ℕ) : List (List Bool) :=
  TupleProgram.powerRows (rows 0 r) Q [[]]

theorem encodeTuple_eq {r Q : ℕ} (hr : 0 < r) (w : Word r Q) :
    SubexpTupleRefinement.encodeTuple (colorCode hr) w = ReadPlan.encodeWord w := by
  rw [SubexpTupleRefinement.encodeTuple, StackEncoding.encodeDataStack_eq_flatMap]
  rw [List.flatMap_def, List.map_ofFn]
  rfl

theorem encodeWord_injective {r Q : ℕ} (hr : 0 < r) :
    Function.Injective (@ReadPlan.encodeWord r Q) := by
  intro a b h
  apply SubexpTupleRefinement.encodeTuple_injective (colorCode hr) Q
  simpa only [encodeTuple_eq hr] using h

theorem wordBytes_nodup {r : ℕ} (hr : 0 < r) (Q : ℕ) : (wordBytes r Q).Nodup := by
  rw [wordBytes, rows_eq_alphabet]
  exact SubexpTupleRefinement.powerRows_encoded_nodup (colorCode hr)
    (List.finRange r).reverse (List.nodup_reverse.mpr (List.nodup_finRange r)) Q

theorem wordBytes_encode_mem {r Q : ℕ} (hr : 0 < r) (w : Word r Q) :
    ReadPlan.encodeWord w ∈ wordBytes r Q := by
  rw [wordBytes, rows_eq_alphabet]
  rw [← encodeTuple_eq hr]
  exact SubexpTupleRefinement.encodeTuple_mem_powerRows (colorCode hr)
    (List.finRange r).reverse (by intro c; simp) Q w

theorem wordBytes_mem_encode {r Q : ℕ} (hr : 0 < r) (bits : List Bool)
    (h : bits ∈ wordBytes r Q) : ∃ w : Word r Q, ReadPlan.encodeWord w = bits := by
  rw [wordBytes, rows_eq_alphabet] at h
  obtain ⟨w, _, hw⟩ := (SubexpTupleRefinement.mem_powerRows_encoded (colorCode hr)
    (List.finRange r).reverse Q bits).mp h
  exact ⟨w, (encodeTuple_eq hr w).symm.trans hw⟩

private theorem list_lift {A B : Type*} (f : A → B) (bs : List B)
    (h : ∀ b ∈ bs, ∃ a, f a = b) : ∃ as : List A, as.map f = bs := by
  induction bs with
  | nil => exact ⟨[], rfl⟩
  | cons b bs ih =>
      obtain ⟨a, ha⟩ := h b (by simp)
      obtain ⟨as, has⟩ := ih (by intro c hc; exact h c (by simp [hc]))
      exact ⟨a :: as, by simp [ha, has]⟩

/-- The proof-only word list follows the actual emitted byte order. The
program never receives this list or any semantic function as input. -/
theorem wordBytes_order {r : ℕ} (hr : 0 < r) (Q : ℕ) :
    ∃ a : Word r Q, ∃ tail : List (Word r Q),
      (a :: tail).map ReadPlan.encodeWord = wordBytes r Q ∧
      (a :: tail).Nodup ∧ ∀ w, w ∈ a :: tail := by
  obtain ⟨ws, hws⟩ := list_lift ReadPlan.encodeWord (wordBytes r Q)
    (wordBytes_mem_encode hr)
  have hnodup : ws.Nodup := List.Nodup.of_map ReadPlan.encodeWord
    (by rw [hws]; exact wordBytes_nodup hr Q)
  have hfull : ∀ w : Word r Q, w ∈ ws := by
    intro w
    have hw := wordBytes_encode_mem hr w
    rw [← hws, List.mem_map] at hw
    obtain ⟨u, hu, he⟩ := hw
    exact (encodeWord_injective hr he) ▸ hu
  cases ws with
  | nil =>
      have h := hfull (fun _ => ⟨0, hr⟩)
      simp at h
  | cons a tail => exact ⟨a, tail, hws, hnodup, hfull⟩

@[simp] theorem wordBytes_length (r Q : ℕ) : (wordBytes r Q).length = r ^ Q := by
  rw [wordBytes, TupleProgram.generated_count, rows_eq_alphabet]
  simp

theorem wordBytes_width {r Q : ℕ} (hr : 0 < r) (bits : List Bool)
    (hb : bits ∈ wordBytes r Q) : bits.length = Q * r := by
  obtain ⟨w, rfl⟩ := wordBytes_mem_encode hr bits hb
  exact ReadPlan.encodeWord_length w

end SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

end OAI.Algorithms
