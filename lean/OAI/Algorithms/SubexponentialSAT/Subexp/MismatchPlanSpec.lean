import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan
import OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation

namespace OAI.Algorithms

/-! The physical mismatch filter on the exact one-hot word representation. -/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

open BitProgram StructuredCalls MulticolorTypes

def oneHot {r : ℕ} (a : Fin r) : List Bool :=
  List.ofFn (fun c : Fin r => decide (a = c))

theorem oneHot_injective {r : ℕ} : Function.Injective (@oneHot r) := by
  intro a b h
  have hh := congrFun (List.ofFn_inj.mp h) a
  have hb : b = a := by simpa [oneHot] using hh.symm
  exact hb.symm

def colorRows {r Q : ℕ} (w : MulticolorTypes.Word r Q) : List (List Bool) :=
  List.ofFn (fun i : Fin Q => oneHot (w i))

@[simp] theorem colorRows_length {r Q : ℕ} (w : MulticolorTypes.Word r Q) :
    (colorRows w).length = Q := by simp [colorRows]

theorem colorRows_width {r Q : ℕ} (w : MulticolorTypes.Word r Q) :
    ∀ row ∈ colorRows w, row.length = r := by
  intro row hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  simp [oneHot]

@[simp] theorem colorRows_getD {r Q : ℕ} (w : MulticolorTypes.Word r Q) (i : Fin Q) :
    (colorRows w).getD i.val [] = oneHot (w i) := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp [colorRows]

theorem colorRows_flatten {r Q : ℕ} (w : MulticolorTypes.Word r Q) :
    (colorRows w).flatten = ReadPlan.encodeWord w := rfl

def selectedPositions {r Q : ℕ} (left right : MulticolorTypes.Word r Q) : List ℕ :=
  ((List.finRange Q).filter (fun i => decide (left i ≠ right i))).map Fin.val

theorem mismatch_range {r Q : ℕ} (left right : MulticolorTypes.Word r Q) :
    mismatch (colorRows left) (colorRows right) (List.range Q) = selectedPositions left right := by
  rw [mismatch, ← List.map_coe_finRange, List.filter_map]
  unfold selectedPositions
  congr 1
  apply List.filter_congr
  intro i hi
  simp [colorRows, oneHot_injective.eq_iff]

theorem selectedPositions_nodup {r Q : ℕ} (left right : MulticolorTypes.Word r Q) :
    (selectedPositions left right).Nodup :=
  ((List.nodup_finRange Q).filter _).map Fin.val_injective

theorem selectedPositions_mem {r Q : ℕ} (left right : MulticolorTypes.Word r Q) (i : Fin Q) :
    i.val ∈ selectedPositions left right ↔ left i ≠ right i := by
  simp [selectedPositions, Fin.val_injective.eq_iff]

theorem selectedPositions_length {r Q : ℕ} (left right : MulticolorTypes.Word r Q) :
    (selectedPositions left right).length =
      (Finset.univ.filter (fun i : Fin Q => left i ≠ right i)).card := by
  rw [selectedPositions, List.length_map]
  have hnodup := (List.nodup_finRange Q).filter (fun i => decide (left i ≠ right i))
  rw [← List.toFinset_card_of_nodup hnodup]
  congr 1
  ext i
  simp

theorem word_program_runsIn {r Q : ℕ} (left right : MulticolorTypes.Word r Q) (regs : Regs) :
    ∃ rf : Regs, RunsIn program (sourceBound r (indexRecords (List.range Q)))
      ((state regs (ReadPlan.encodeWord left) (ReadPlan.encodeWord right)
        (List.replicate r true) (ProgramEncoding.encodeRecords (indexRecords (List.range Q)))
        [] [] []).withPC (some program.entry))
      ((state rf (ReadPlan.encodeWord left) (ReadPlan.encodeWord right)
        (List.replicate r true) [] [] []
        (ProgramEncoding.encodeRecords (indexRecords (selectedPositions left right)))).withPC none) := by
  obtain ⟨rf, ht⟩ := program_runsIn (colorRows left) (colorRows right) (List.replicate r true)
    (List.range Q) regs
    (by simpa using colorRows_width left) (by simpa using colorRows_width right)
    (by intro i hi; simpa using And.intro (List.mem_range.mp hi) (List.mem_range.mp hi))
  refine ⟨rf, ?_⟩
  simpa only [List.length_replicate, mismatch_range, colorRows_flatten] using ht

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
