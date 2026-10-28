import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrameSkip

namespace OAI.Algorithms

/-! Read one block's vertex from an actual serialized type bucket. -/

namespace SubexponentialSAT.Subexp.PackingBucketSelect

open BitProgram StructuredCalls MatrixProgramSupport

def state (regs : Fin 8 → Bool) (source key count vertex scratch : List Bool) : Data 5 :=
  ⟨regs, ![source, key, count, vertex, scratch]⟩

abbrev command : Cmd 8 5 :=
  .seq (readWord 0 1 4 (by decide))
    (.seq (PackingFrameSkip.command 2 0)
      (.seq (readWord 0 3 4 (by decide))
        (.call (StackRoutines.clearProgram 0 0 1))))

def program := compiled command 0 3

theorem words_append (xs ys : List (List Bool)) : words (xs ++ ys) = words xs ++ words ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [words, ih, List.append_assoc]

/-- The runtime unary block index is consumed by a real frame-skipping loop;
the residual bucket tail is physically cleared. -/
theorem command_eval (key vertex : List Bool) (pre rest : List (List Bool))
    (regs : Fin 8 → Bool) :
    ∃ n ≤ 20 * ((Encoding.frame key ++ words (pre ++ vertex :: rest)).length + 1),
      ∃ rf, Eval command n
        (state regs (Encoding.frame key ++ words (pre ++ vertex :: rest)) []
          (List.replicate pre.length true) [] [])
        (state rf [] key [] vertex []) := by
  let payload := words (pre ++ vertex :: rest)
  let suffix := Encoding.frame vertex ++ words rest
  obtain ⟨a, ha, hsa⟩ := readWord_eval (0 : Fin 5) 1 4
    (by decide) (by decide) (by decide)
    (state regs (Encoding.frame key ++ payload) [] (List.replicate pre.length true) [] [])
    key payload rfl rfl rfl
  have hea : a = state a.regs payload key (List.replicate pre.length true) [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsa]
    funext i
    fin_cases i <;> simp [state]
  rw [hea] at ha
  let a' := state a.regs payload key (List.replicate pre.length true) [] []
  have hs : a'.stacks 0 = words pre ++ suffix := by
    simp [a', state, payload, suffix, words_append, words]
  have hb := PackingFrameSkip.command_eval (2 : Fin 5) 0 (by decide) a' pre suffix
    (by simp [a', state]) hs
  let b := PackingFrameSkip.finalState 2 0 a' pre suffix
  have heb : b = state b.regs suffix key [] [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    funext i
    fin_cases i <;> simp [b, a', state, PackingFrameSkip.finalState]
  change Eval (PackingFrameSkip.command 2 0) (BlockZeroProgram.skipCost pre) a' b at hb
  rw [heb] at hb
  obtain ⟨c, hc, hsc⟩ := readWord_eval (0 : Fin 5) 3 4
    (by decide) (by decide) (by decide)
    (state b.regs suffix key [] [] []) vertex (words rest) rfl rfl rfl
  have hec : c = state c.regs (words rest) key [] vertex [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsc]
    funext i
    fin_cases i <;> simp [state]
  rw [hec] at hc
  let rf := readRegs c.regs 0 1 none
  have hd : Eval (.call (StackRoutines.clearProgram 0 0 1))
      (2 * (words rest).length + 3)
      (state c.regs (words rest) key [] vertex []) (state rf [] key [] vertex []) := by
    have h := TupleProgram.clear_eval (0 : Fin 5) (0 : Fin 8) 1
      (state c.regs (words rest) key [] vertex [])
    have he : (⟨rf, StackRoutines.clearStacks 0
        (state c.regs (words rest) key [] vertex []).stacks⟩ : Data 5) =
        state rf [] key [] vertex [] := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      funext i
      fin_cases i <;> rfl
    change Eval (.call (StackRoutines.clearProgram 0 0 1)) (2 * (words rest).length + 3)
      (state c.regs (words rest) key [] vertex [])
      (⟨rf, StackRoutines.clearStacks 0
        (state c.regs (words rest) key [] vertex []).stacks⟩ : Data 5) at h
    rw [he] at h
    exact h
  refine ⟨(9 * key.length + 7) + (BlockZeroProgram.skipCost pre +
    ((9 * vertex.length + 7) + (2 * (words rest).length + 3))), ?_, rf, ?_⟩
  · have h := PackingFrameSkip.cost_le pre
    simp only [words_append, words, List.length_append, Encoding.length_frame]
    omega
  · exact ha.seq (hb.seq (hc.seq hd))

theorem program_trace (key vertex : List Bool) (pre rest : List (List Bool))
    (regs : Fin 8 → Bool) :
    ∃ n ≤ 21 * ((Encoding.frame key ++ words (pre ++ vertex :: rest)).length + 1),
      ∃ rf, Trace program n
        ((state regs (Encoding.frame key ++ words (pre ++ vertex :: rest)) []
          (List.replicate pre.length true) [] []).withPC (some program.entry))
        ((state rf [] key [] vertex []).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval key vertex pre rest regs
  exact ⟨n + 1, by omega, rf, compiled_halt_trace he 0 3⟩

end SubexponentialSAT.Subexp.PackingBucketSelect

end OAI.Algorithms
