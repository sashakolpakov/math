import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCacheLoop

namespace OAI.Algorithms

/-! Physical framing removal and width preparation for the cache kernel. -/

namespace SubexponentialSAT.SubexpFieldCachePreparation

open BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open SubexpCRTCofactorControl SubexpFieldCacheControl

attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem extend_agree {α β γ : Type*} (f : α ↪ β) (values : α → γ)
    (frame : β → γ) (h : ∀ i, frame (f i) = values i) :
    Function.extend f values frame = frame := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply, h]
  · exact Function.extend_apply' _ _ _ hj

private theorem flatten_data_update (ri rf : Fin 5 → Bool) (input output : List Bool) :
    (SubexpRecordFlatten.data rf output [] []).stacks =
      Function.update (SubexpRecordFlatten.data ri input [] []).stacks 0 output := by
  funext i
  fin_cases i <;> rfl

/-- The parser is invoked on the actual framed node stack, and its final
packed array replaces that stack. Other cache data is preserved. -/
theorem flatten_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (records : List (List Bool))
    (hs : frame 97 = ProgramEncoding.encodeRecords records)
    (hn : w.node = []) (hstream : w.stream = []) :
    ∃ n rf, n ≤ SubexpRecordFlatten.bound records ∧
      Eval SubexpFieldCacheControl.flatten n (state regs frame w)
        (state rf (Function.update frame 97 records.flatten) w) := by
  let ri : Fin 5 → Bool := fun i => regs (flattenRegisters i)
  let d := state regs frame w
  obtain ⟨rf, n, hbound, ht⟩ := SubexpRecordFlatten.program_run records ri
  have hi : ∀ i,
      d.stacks (flattenPorts i) =
        (SubexpRecordFlatten.data ri (ProgramEncoding.encodeRecords records) [] []).stacks i := by
    intro i
    fin_cases i <;> simp [d, flattenPorts, SubexpRecordFlatten.data, state,
      store, hs, hn, hstream]
  have hireg : Function.extend flattenRegisters ri d.regs = regs :=
    extend_agree flattenRegisters ri regs (fun _ => rfl)
  have histack : Function.extend flattenPorts
      (SubexpRecordFlatten.data ri (ProgramEncoding.encodeRecords records) [] []).stacks
      d.stacks = d.stacks := extend_agree flattenPorts _ _ hi
  have ho : Function.extend flattenPorts
      (SubexpRecordFlatten.data rf records.flatten [] []).stacks d.stacks =
      store (Function.update frame 97 records.flatten) w := by
    rw [flatten_data_update ri rf, ProgramLinking.extend_update flattenPorts.injective, histack]
    exact update_store_extra frame w 97 records.flatten (by left; rfl)
  have he := eval_call_lifted SubexpRecordFlatten.program flattenRegisters flattenPorts d
    flattenRegisters.injective flattenPorts.injective ht
  have hein : embedState flattenRegisters flattenPorts d
      (SubexpRecordFlatten.data ri (ProgramEncoding.encodeRecords records) [] []) = d := by
    apply state_ext
    · exact hireg
    · exact histack
  have heout : embedState flattenRegisters flattenPorts d
      (SubexpRecordFlatten.data rf records.flatten [] []) =
      state (Function.extend flattenRegisters rf regs) (Function.update frame 97 records.flatten) w := by
    apply state_ext
    · rfl
    · exact ho
  rw [hein, heout] at he
  refine ⟨n, Function.extend flattenRegisters rf regs, hbound, ?_⟩
  exact he

theorem copy_width_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (hw : w.blockWidth = []) :
    Eval (SubexpFieldCacheControl.copy 93 104) (7 * w.unit.length + 5)
      (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with blockWidth := w.unit}) := by
  have h := copy_eval (state regs frame w) 93 104 0 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have he : afterCopy (state regs frame w) 93 104 0 1 =
      state (readRegs regs 0 1 none) frame {w with blockWidth := w.unit} := by
    simp only [afterCopy, state, copyStacks, store_unit, store_blockWidth, hw,
      List.append_nil, SubexpCRTCofactorLoop.update_store_blockWidth]
  rw [he] at h
  simpa only [SubexpFieldCacheControl.copy, state, store_unit] using h

theorem clear_width_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) :
    Eval (clear 104) (2 * w.blockWidth.length + 3) (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with blockWidth := []}) := by
  have h := SubexpCRTCofactorLoop.clear_eval (state regs frame w) 104
  simpa only [state, store_blockWidth, SubexpCRTCofactorLoop.update_store_blockWidth] using h

end SubexponentialSAT.SubexpFieldCachePreparation

end OAI.Algorithms
