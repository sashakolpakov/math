import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateTraversal

namespace OAI.Algorithms

/-! Physically repeat the common groups for every actual outer bank. -/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls SubexpScanPrimitives

def blockBytes (base outside groups : Word) : Word :=
  Encoding.frame base ++ Encoding.frame outside ++ groups

def blocksBytes (outside groups : Word) (bases : List Word) : Word :=
  Encoding.encodeList (fun base => blockBytes base outside groups) bases

def blockBody : Code :=
  .seq (capture 205 207 (by decide))
    (.seq (appendFrame 207 217) (.seq (appendFrame 208 217)
      (.seq (appendBits 212 217) (.seq (clear 207) (.seq (transfer 217 224)
        (.seq (appendRecord 224 221) (clear 224)))))))

def blockCost (base outside groups : Word) : ℕ :=
  19 * base.length + 8 * outside.length + 10 * groups.length +
    13 * (blockBytes base outside groups).length + 47

def blockResult (base outside groups tail : Word) (d : Data) : Data :=
  ⟨afterFrameRegs d.regs,
    Function.update (Function.update d.stacks 205 tail) 221
      ((record (blockBytes base outside groups)).reverse ++ d.stacks 221)⟩

theorem blockBody_eval (base outside groups tail : Word) (d : Data)
    (hin : d.stacks 205 = Encoding.frame base ++ tail)
    (h207 : d.stacks 207 = []) (h217 : d.stacks 217 = [])
    (h218 : d.stacks 218 = []) (h224 : d.stacks 224 = [])
    (h208 : d.stacks 208 = outside) (h212 : d.stacks 212 = groups) :
    Eval blockBody (blockCost base outside groups) d
      (blockResult base outside groups tail d) := by
  let a := captured 205 207 base tail d
  let b := framed 207 217 a
  let c := framed 208 217 b
  let e := appended 212 217 c
  let f := cleared 207 e
  let g := afterTransfer f 217 224 0 1
  let h := recorded 224 221 g
  let j := cleared 224 h
  have ha := capture_eval 205 207 (by decide) (by decide) (by decide)
    base tail d hin h207 h218
  have hb : Eval (appendFrame 207 217) (8 * base.length + 7) a b := by
    have hv : a.stacks 207 = base := by simp [a, captured]
    have ht : Eval (appendFrame 207 217) (8 * (a.stacks 207).length + 7) a b :=
      appendFrame_eval 207 217 (by decide) (by decide) (by decide) a
        (by simp [a, captured, h218])
    simpa only [hv] using ht
  have hc : Eval (appendFrame 208 217) (8 * outside.length + 7) b c := by
    have hv : b.stacks 208 = outside := by simp [b, a, framed, captured, h208]
    have ht : Eval (appendFrame 208 217) (8 * (b.stacks 208).length + 7) b c :=
      appendFrame_eval 208 217 (by decide) (by decide) (by decide) b
        (by simp [b, a, framed, captured, h218])
    simpa only [hv] using ht
  have he : Eval (appendBits 212 217) (10 * groups.length + 8) c e := by
    have hv : c.stacks 212 = groups := by simp [c, b, a, framed, captured, h212]
    have ht : Eval (appendBits 212 217) (10 * (c.stacks 212).length + 8) c e :=
      appendBits_eval 212 217 (by decide) (by decide) (by decide) (by decide) c
        (by simp [c, b, a, framed, captured, h218])
        (by simp [c, b, a, framed, captured, h224])
    simpa only [hv] using ht
  have hf : Eval (clear 207) (2 * base.length + 3) e f := by
    have hv : e.stacks 207 = base := by simp [e, c, b, a, appended, framed, captured]
    have ht : Eval (clear 207) (2 * (e.stacks 207).length + 3) e f := clear_eval 207 e
    simpa only [hv] using ht
  have hf217 : f.stacks 217 = (blockBytes base outside groups).reverse := by
    simp [f, e, c, b, a, cleared, appended, framed, captured, h208, h212, h217,
      blockBytes, List.reverse_append, List.append_assoc]
  have hf224 : f.stacks 224 = [] := by
    simp [f, e, c, b, a, cleared, appended, framed, captured, h224]
  have hg : Eval (transfer 217 224)
      (3 * (blockBytes base outside groups).length + 3) f g := by
    have ht : Eval (transfer 217 224) (3 * (f.stacks 217).length + 3) f g :=
      transfer_eval 217 224 (by decide) f
    simpa only [hf217, List.length_reverse] using ht
  have hg224 : g.stacks 224 = blockBytes base outside groups := by
    simp [g, afterTransfer, StackRoutines.transferStacks, hf217, hf224]
  have hg218 : g.stacks 218 = [] := by
    simp [g, f, e, c, b, a, afterTransfer, StackRoutines.transferStacks,
      cleared, appended, framed, captured, h218]
  have hh : Eval (appendRecord 224 221)
      (8 * (blockBytes base outside groups).length + 9) g h := by
    have ht : Eval (appendRecord 224 221) (8 * (g.stacks 224).length + 9) g h :=
      appendRecord_eval 224 221 (by decide) (by decide) (by decide) g hg218
    simpa only [hg224] using ht
  have hj : Eval (clear 224) (2 * (blockBytes base outside groups).length + 3) h j := by
    have hv : h.stacks 224 = blockBytes base outside groups := by simp [h, recorded, hg224]
    have ht : Eval (clear 224) (2 * (h.stacks 224).length + 3) h j := clear_eval 224 h
    simpa only [hv] using ht
  have hg221 : g.stacks 221 = d.stacks 221 := by
    simp [g, f, e, c, b, a, afterTransfer, StackRoutines.transferStacks,
      cleared, appended, framed, captured]
  have hfinal : j = blockResult base outside groups tail d := by
    apply state_ext
    · funext i
      by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;>
        simp [j, h, g, f, e, c, b, a, cleared, recorded, afterTransfer, appended,
          framed, captured, blockResult, afterFrameRegs, readRegs, h0, h1, h2]
    · funext i
      by_cases hi205 : i = 205
      · subst i
        simp [j, h, g, f, e, c, b, a, cleared, recorded, afterTransfer, appended,
          framed, captured, blockResult, StackRoutines.transferStacks]
      by_cases hi207 : i = 207
      · subst i
        simp [j, h, g, f, cleared, recorded, afterTransfer, blockResult,
          StackRoutines.transferStacks, h207]
      by_cases hi217 : i = 217
      · subst i
        simp [j, h, g, cleared, recorded, afterTransfer, blockResult,
          StackRoutines.transferStacks, h217]
      by_cases hi224 : i = 224
      · subst i
        simp [j, cleared, blockResult, h224]
      by_cases hi221 : i = 221
      · subst i
        simp [j, h, recorded, cleared, hg224, hg221, blockResult]
      · simp [j, h, g, f, e, c, b, a, cleared, recorded, afterTransfer, appended,
          framed, captured, blockResult, StackRoutines.transferStacks,
          hi205, hi207, hi217, hi224, hi221]
  have ht := ha.seq (hb.seq (hc.seq (he.seq (hf.seq (hg.seq (hh.seq hj))))))
  rw [hfinal] at ht
  change Eval blockBody _ d (blockResult base outside groups tail d) at ht
  convert ht using 1
  unfold blockCost
  omega

def OuterWork (outside groups : Word) (store : Store) : Prop :=
  store 207 = [] ∧ store 217 = [] ∧ store 218 = [] ∧ store 224 = [] ∧
    store 208 = outside ∧ store 212 = groups

def blockStore (outside groups base : Word) (store : Store) : Store :=
  Function.update store 221 ((record (blockBytes base outside groups)).reverse ++ store 221)

theorem blockStore_work (outside groups base : Word) (store : Store)
    (h : OuterWork outside groups store) : OuterWork outside groups (blockStore outside groups base store) := by
  simpa [OuterWork, blockStore] using h

theorem blockBody_scan (outside groups base : Word) (regs : Fin 16 → Bool)
    (store : Store) (rest : Word) (hw : OuterWork outside groups store) :
    ∃ n rf, n ≤ blockCost base outside groups ∧ Eval blockBody n
      (inputState 205 regs store (Encoding.frame base ++ rest))
      (inputState 205 rf (blockStore outside groups base store) rest) := by
  let d := inputState 205 regs store (Encoding.frame base ++ rest)
  have h := blockBody_eval base outside groups rest d (by simp [d, inputState])
    (by simpa [d, inputState] using hw.1)
    (by simpa [d, inputState] using hw.2.1)
    (by simpa [d, inputState] using hw.2.2.1)
    (by simpa [d, inputState] using hw.2.2.2.1)
    (by simpa [d, inputState] using hw.2.2.2.2.1)
    (by simpa [d, inputState] using hw.2.2.2.2.2)
  have he : blockResult base outside groups rest d =
      inputState 205 (afterFrameRegs regs) (blockStore outside groups base store) rest := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi205 : i = 205
      · subst i; simp [blockResult, blockStore, inputState]
      by_cases hi221 : i = 221
      · subst i; simp [blockResult, blockStore, d, inputState]
      · simp [blockResult, blockStore, d, inputState, hi205, hi221]
  exact ⟨blockCost base outside groups, afterFrameRegs regs, le_rfl, he ▸ h⟩

theorem fold_blockStore (outside groups : Word) (bases : List Word) (store : Store) :
    bases.foldl (fun s base => blockStore outside groups base s) store =
      Function.update store 221
        (bases.foldl (fun acc base => (record (blockBytes base outside groups)).reverse ++ acc)
          (store 221)) := by
  induction bases generalizing store with
  | nil =>
    funext i
    by_cases hi : i = 221 <;> simp [hi]
  | cons base bases ih =>
    rw [List.foldl_cons, ih]
    funext i
    by_cases hi : i = 221 <;> simp [hi, blockStore]

def outerCommand : Code :=
  .seq (scanBare 205 blockBody) (.seq (pushBit 221 false) (transfer 221 15))

def outerCost (outside groups : Word) (bases : List Word) : ℕ :=
  7 + scanBudget (fun base => blockCost base outside groups) bases +
    3 * (blocksBytes outside groups bases).length

theorem outer_eval (outside groups : Word) (bases : List Word) (d : Data)
    (hsource : d.stacks 205 = Encoding.encodeList id bases)
    (hwork : OuterWork outside groups d.stacks)
    (h221 : d.stacks 221 = []) (h15 : d.stacks 15 = []) :
    ∃ n e, n ≤ outerCost outside groups bases ∧ Eval outerCommand n d e ∧
      e.stacks = Function.update (Function.update d.stacks 205 []) 15
        (blocksBytes outside groups bases) := by
  have hstart : inputState 205 d.regs d.stacks (Encoding.encodeList id bases ++ []) = d := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi : i = 205 <;> simp [inputState, hi, hsource]
  obtain ⟨n, rf, hn, he⟩ := scanBare_eval 205 blockBody id
    (fun base => blockCost base outside groups) (blockStore outside groups)
    (OuterWork outside groups)
    (fun base regs store rest hw => blockBody_scan outside groups base regs store rest hw)
    (blockStore_work outside groups) bases d.regs d.stacks [] hwork
  rw [hstart] at he
  let a := inputState 205 rf
    (bases.foldl (fun s base => blockStore outside groups base s) d.stacks) []
  have ha : a.stacks = Function.update
      (Function.update d.stacks 221
        ((recordBytes (fun base => blockBytes base outside groups) bases).reverse ++ d.stacks 221))
      205 [] := by
    simp only [a, inputState, fold_blockStore, recordFold_eq]
  let b := pushed 221 false a
  have hb221 : b.stacks 221 = (blocksBytes outside groups bases).reverse := by
    simp [b, pushed, ha, h221, blocksBytes, encodeList_eq_records, List.reverse_append]
  have hb15 : b.stacks 15 = [] := by simp [b, pushed, ha, h15]
  let e := afterTransfer b 221 15 0 1
  have ht : Eval (transfer 221 15)
      (3 * (blocksBytes outside groups bases).length + 3) b e := by
    simpa [hb221] using transfer_eval 221 15 (by decide) b
  refine ⟨n + (2 + (3 * (blocksBytes outside groups bases).length + 3)), e, ?_,
    he.seq ((pushBit_eval 221 false a).seq ht), ?_⟩
  · unfold outerCost
    omega
  · funext i
    by_cases hi15 : i = 15
    · subst i
      simp [e, afterTransfer, StackRoutines.transferStacks, hb221, hb15]
    by_cases hi221 : i = 221
    · subst i
      simp [e, afterTransfer, StackRoutines.transferStacks, h221]
    by_cases hi205 : i = 205
    · subst i
      simp [e, afterTransfer, StackRoutines.transferStacks, b, pushed, ha]
    · simp [e, afterTransfer, StackRoutines.transferStacks, b, pushed, ha,
        hi15, hi221, hi205]

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
