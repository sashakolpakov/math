import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateGroup

namespace OAI.Algorithms

/-! A fixed scan expands one color's actual increment banks into terms. -/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls SubexpScanPrimitives

def GroupWork (support factors : Word) (store : Store) : Prop :=
  store 207 = [] ∧ store 213 = [] ∧ store 218 = [] ∧ store 224 = [] ∧
    store 209 = support ∧ store 210 = factors

def termStore (support factors increment : Word) (store : Store) : Store :=
  Function.update store 215
    ((record (termBytes increment support factors)).reverse ++ store 215)

theorem termStore_work (support factors increment : Word) (store : Store)
    (h : GroupWork support factors store) : GroupWork support factors (termStore support factors increment store) := by
  simpa [GroupWork, termStore] using h

theorem termBody_scan (support factors increment : Word) (regs : Fin 16 → Bool)
    (store : Store) (rest : Word) (hw : GroupWork support factors store) :
    ∃ n rf, n ≤ termCost increment support factors ∧ Eval termBody n
      (inputState 206 regs store (Encoding.frame increment ++ rest))
      (inputState 206 rf (termStore support factors increment store) rest) := by
  let d := inputState 206 regs store (Encoding.frame increment ++ rest)
  have h := termBody_eval increment support factors rest d (by simp [d, inputState])
    (by simpa [d, inputState] using hw.1)
    (by simpa [d, inputState] using hw.2.1)
    (by simpa [d, inputState] using hw.2.2.1)
    (by simpa [d, inputState] using hw.2.2.2.1)
    (by simpa [d, inputState] using hw.2.2.2.2.1)
    (by simpa [d, inputState] using hw.2.2.2.2.2)
  have he : termResult increment support factors rest d =
      inputState 206 (afterFrameRegs regs) (termStore support factors increment store) rest := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi206 : i = 206
      · subst i; simp [termResult, termStore, inputState]
      by_cases hi215 : i = 215
      · subst i; simp [termResult, termStore, d, inputState]
      · simp [termResult, termStore, d, inputState, hi206, hi215]
  exact ⟨termCost increment support factors, afterFrameRegs regs, le_rfl, he ▸ h⟩

theorem fold_termStore (support factors : Word) (increments : List Word) (store : Store) :
    increments.foldl (fun s inc => termStore support factors inc s) store =
      Function.update store 215
        (increments.foldl (fun acc inc => (record (termBytes inc support factors)).reverse ++ acc)
          (store 215)) := by
  induction increments generalizing store with
  | nil =>
    funext i
    by_cases hi : i = 215 <;> simp [hi]
  | cons inc increments ih =>
    rw [List.foldl_cons, ih]
    funext i
    by_cases hi : i = 215 <;> simp [hi, termStore]

def groupCommand : Code :=
  .seq (scanBare 206 termBody) (.seq (pushBit 215 false) (transfer 215 216))

def groupCost (support factors : Word) (increments : List Word) : ℕ :=
  7 + scanBudget (fun inc => termCost inc support factors) increments +
    3 * (groupBytes support factors increments).length

/-- The increment list is consumed. The support and factor packet masters
are preserved and all term-building scratch is restored. -/
theorem group_eval (support factors : Word) (increments : List Word) (d : Data)
    (hsource : d.stacks 206 = Encoding.encodeList id increments)
    (hwork : GroupWork support factors d.stacks)
    (h215 : d.stacks 215 = []) (h216 : d.stacks 216 = []) :
    ∃ n e, n ≤ groupCost support factors increments ∧ Eval groupCommand n d e ∧
      e.stacks = Function.update (Function.update d.stacks 206 []) 216
        (groupBytes support factors increments) := by
  have hstart : inputState 206 d.regs d.stacks (Encoding.encodeList id increments ++ []) = d := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi : i = 206 <;> simp [inputState, hi, hsource]
  obtain ⟨n, rf, hn, he⟩ := scanBare_eval 206 termBody id
    (fun inc => termCost inc support factors) (termStore support factors)
    (GroupWork support factors)
    (fun inc regs store rest hw => termBody_scan support factors inc regs store rest hw)
    (termStore_work support factors) increments d.regs d.stacks [] hwork
  rw [hstart] at he
  let a := inputState 206 rf
    (increments.foldl (fun s inc => termStore support factors inc s) d.stacks) []
  have ha : a.stacks = Function.update
      (Function.update d.stacks 215
        ((recordBytes (fun inc => termBytes inc support factors) increments).reverse ++ d.stacks 215))
      206 [] := by
    simp only [a, inputState, fold_termStore, recordFold_eq]
  let b := pushed 215 false a
  have hb215 : b.stacks 215 = (groupBytes support factors increments).reverse := by
    simp [b, pushed, ha, h215, groupBytes, encodeList_eq_records, List.reverse_append]
  have hb216 : b.stacks 216 = [] := by simp [b, pushed, ha, h216]
  let e := afterTransfer b 215 216 0 1
  have ht : Eval (transfer 215 216)
      (3 * (groupBytes support factors increments).length + 3) b e := by
    simpa [hb215] using transfer_eval 215 216 (by decide) b
  refine ⟨n + (2 + (3 * (groupBytes support factors increments).length + 3)), e, ?_,
    he.seq ((pushBit_eval 215 false a).seq ht), ?_⟩
  · unfold groupCost
    omega
  · funext i
    by_cases hi216 : i = 216
    · subst i
      simp [e, afterTransfer, StackRoutines.transferStacks, hb215, hb216]
    by_cases hi215 : i = 215
    · subst i
      simp [e, afterTransfer, StackRoutines.transferStacks, h215]
    by_cases hi206 : i = 206
    · subst i
      simp [e, afterTransfer, StackRoutines.transferStacks, b, pushed, ha]
    · simp [e, afterTransfer, StackRoutines.transferStacks, b, pushed, ha,
        hi216, hi215, hi206]

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
