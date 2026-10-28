import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.StackRoutines
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Fixed stack and frame-reading routines used by the encoded matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSupport

open BitProgram StructuredCalls

variable {s : ℕ}

abbrev Data (s : ℕ) := StructuredProgram.State 8 s

theorem data_ext {a b : Data s} (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

def fieldPorts (src dst : Fin s) (h : src ≠ dst) : RecordPrograms.Ports 8 s where
  tag := 0
  present := 1
  found := 2
  source := src
  payload := dst
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := h

abbrev readFrame (src dst : Fin s) (h : src ≠ dst) : Cmd 8 s :=
  RecordPrograms.reader (fieldPorts src dst h)

theorem readFrame_eval (src dst : Fin s) (h : src ≠ dst)
    (d : Data s) (bits tail : List Bool)
    (hsource : d.stacks src = Encoding.frame bits ++ tail) (hempty : d.stacks dst = []) :
    ∃ e, Eval (readFrame src dst h) (6 * bits.length + 4) d e ∧
      e.stacks = Function.update (Function.update d.stacks src tail) dst bits.reverse := by
  let p := fieldPorts src dst h
  let e := RecordPrograms.state p d false true (d.regs 2) tail bits.reverse
  have hs : RecordPrograms.state p d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ tail) [] = d :=
    RecordPrograms.state_eq_self p d _ _ _ _ _ rfl rfl rfl hsource hempty
  have he := RecordPrograms.reader_eval p d bits tail [] (d.regs 0) (d.regs 1) (d.regs 2)
  rw [hs] at he
  refine ⟨e, ?_, rfl⟩
  simpa only [List.append_nil] using he

abbrev transfer (src dst : Fin s) : Cmd 8 s :=
  .call (StackRoutines.transferProgram src dst 0 1)

theorem transfer_eval (src dst : Fin s) (h : src ≠ dst) (d : Data s) :
    ∃ e, Eval (transfer src dst) (3 * (d.stacks src).length + 3) d e ∧
      e.stacks = StackRoutines.transferStacks src dst d.stacks := by
  let e : Data s := ⟨readRegs d.regs 0 1 none,
    StackRoutines.transferStacks src dst d.stacks⟩
  have ht := StackRoutines.transferProgram_trace src dst (0 : Fin 8) 1
    h (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 3 rfl rfl
  refine ⟨e, .call _ ?_, rfl⟩
  simpa [e, StackRoutines.transferResult, StructuredProgram.State.withPC,
    StackRoutines.transferProgram, Nat.add_assoc] using hh

abbrev move (src dst tmp : Fin s) : Cmd 8 s :=
  .seq (transfer src tmp) (transfer tmp dst)

theorem move_eval (src dst tmp : Fin s) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (htd : tmp ≠ dst) (d : Data s) (he : d.stacks dst = []) (ht : d.stacks tmp = []) :
    ∃ e, Eval (move src dst tmp) (6 * (d.stacks src).length + 6) d e ∧
      e.stacks = Function.update (Function.update d.stacks src []) dst (d.stacks src) := by
  obtain ⟨a, ha, hsa⟩ := transfer_eval src tmp hst d
  obtain ⟨b, hb, hsb⟩ := transfer_eval tmp dst htd a
  have hat : a.stacks tmp = (d.stacks src).reverse := by
    rw [hsa]
    simp [StackRoutines.transferStacks, ht]
  have hatlen : (a.stacks tmp).length = (d.stacks src).length := by
    rw [hat, List.length_reverse]
  refine ⟨b, ?_, ?_⟩
  · have hc := Eval.seq ha hb
    convert hc using 1
    omega
  · rw [hsb, hsa]
    funext j
    by_cases hjd : j = dst
    · subst j
      simp [StackRoutines.transferStacks, he, ht, Ne.symm hsd, Ne.symm htd]
    · by_cases hjs : j = src
      · subst j
        simp [StackRoutines.transferStacks, ht, hsd, hst, Ne.symm htd]
      · by_cases hjt : j = tmp
        · subst j
          simp [StackRoutines.transferStacks, he, ht, Ne.symm hsd,
            Ne.symm hst, htd, Ne.symm htd]
        · simp [StackRoutines.transferStacks, hjd, hjs, hjt]

abbrev readWord (src dst tmp : Fin s) (hst : src ≠ tmp) : Cmd 8 s :=
  .seq (readFrame src tmp hst) (transfer tmp dst)

/-- Decode one frame and restore its little-endian order. -/
theorem readWord_eval (src dst tmp : Fin s) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (htd : tmp ≠ dst) (d : Data s) (bits tail : List Bool)
    (hs : d.stacks src = Encoding.frame bits ++ tail)
    (hd : d.stacks dst = []) (ht : d.stacks tmp = []) :
    ∃ e, Eval (readWord src dst tmp hst) (9 * bits.length + 7) d e ∧
      e.stacks = Function.update (Function.update d.stacks src tail) dst bits := by
  obtain ⟨a, ha, hsa⟩ := readFrame_eval src tmp hst d bits tail hs ht
  obtain ⟨b, hb, hsb⟩ := transfer_eval tmp dst htd a
  have hat : a.stacks tmp = bits.reverse := by rw [hsa]; simp
  have hatlen : (a.stacks tmp).length = bits.length := by
    rw [hat, List.length_reverse]
  refine ⟨b, ?_, ?_⟩
  · have hc := Eval.seq ha hb
    convert hc using 1
    omega
  · rw [hsb, hsa]
    funext j
    by_cases hjd : j = dst
    · subst j
      simp [StackRoutines.transferStacks, hd, Ne.symm hsd, Ne.symm htd]
    · by_cases hjs : j = src
      · subst j
        simp [StackRoutines.transferStacks, hsd, hst, Ne.symm htd]
      · by_cases hjt : j = tmp
        · subst j
          simp [StackRoutines.transferStacks, hd, ht, Ne.symm hsd,
            Ne.symm hst, htd, Ne.symm htd]
        · simp [StackRoutines.transferStacks, hjd, hjs, hjt]

abbrev copy (src dst tmp : Fin s) : Cmd 8 s :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

theorem copy_eval (src dst tmp : Fin s) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (htd : tmp ≠ dst) (d : Data s) (ht : d.stacks tmp = []) :
    ∃ e, Eval (copy src dst tmp) (7 * (d.stacks src).length + 5) d e ∧
      e.stacks = StackRoutines.copyStacks src dst d.stacks := by
  let e : Data s := ⟨readRegs d.regs 0 1 none,
    StackRoutines.copyStacks src dst d.stacks⟩
  have hc := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 8) 1
    hsd hst htd (by decide) d.regs d.stacks ht
  have hh := StackRoutines.halt_after_trace _ hc 7 rfl rfl
  refine ⟨e, .call _ ?_, rfl⟩
  simpa [e, StackRoutines.copyResult, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, Nat.add_assoc] using hh

def words : List (List Bool) → List Bool
  | [] => []
  | x :: xs => Encoding.frame x ++ words xs

theorem words_append (xs ys : List (List Bool)) : words (xs ++ ys) = words xs ++ words ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [words, ih, List.append_assoc]

theorem words_length (xs : List (List Bool)) (B : ℕ) (h : ∀ x ∈ xs, x.length = B) :
    (words xs).length = xs.length * (2 * B + 1) := by
  induction xs with
  | nil => simp [words]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [words, List.length_append, Encoding.length_frame, hx, hs, List.length_cons]
    ring

abbrev emitFrame (src dst tmp : Fin s) (htd : tmp ≠ dst) : Cmd 8 s :=
  .seq (transfer src tmp)
    (.seq (TupleProgram.pushConst dst 0 false)
      (TupleProgram.escape (fieldPorts tmp dst htd)))

/-- Consume a raw word and prepend its complete frame, with every encoding
step performed by fixed instructions. -/
theorem emitFrame_eval (src dst tmp : Fin s) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (htd : tmp ≠ dst) (d : Data s) (ht : d.stacks tmp = []) :
    ∃ e, Eval (emitFrame src dst tmp htd) (8 * (d.stacks src).length + 8) d e ∧
      e.stacks = Function.update (Function.update d.stacks src []) dst
        (Encoding.frame (d.stacks src) ++ d.stacks dst) := by
  obtain ⟨a, ha, hsa⟩ := transfer_eval src tmp hst d
  let b := TupleProgram.pushedState dst 0 false a
  let e := TupleProgram.escapedState (fieldPorts tmp dst htd) b
  have hb := TupleProgram.pushConst_eval dst (0 : Fin 8) false a
  have he := TupleProgram.escape_eval_state (fieldPorts tmp dst htd) b
  have ht' : b.stacks tmp = (d.stacks src).reverse := by
    simp only [b, Function.update_apply, hsa]
    simp [ ht, htd]
  have htlen : (b.stacks (fieldPorts tmp dst htd).source).length =
      (d.stacks src).length := by
    simpa only [fieldPorts, List.length_reverse] using congrArg List.length ht'
  refine ⟨e, ?_, ?_⟩
  · have hh := Eval.seq ha (Eval.seq hb he)
    convert hh using 1
    omega
  · simp only [e, b, fieldPorts, hsa]
    funext j
    by_cases hjd : j = dst
    · subst j
      simp [StackRoutines.transferStacks, ht, Ne.symm hsd,
        htd, Ne.symm htd, TupleProgram.frame_eq_escaped,
        List.append_assoc]
    · by_cases hjs : j = src
      · subst j
        simp [StackRoutines.transferStacks, ht, hsd, hst, htd, Ne.symm htd]
      · by_cases hjt : j = tmp
        · subst j
          simp [StackRoutines.transferStacks, ht, Ne.symm hst,
            htd, Ne.symm htd]
        · simp [StackRoutines.transferStacks, hjd, hjs, hjt]

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
