import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateContext

namespace OAI.Algorithms

/-! Measured initialization, list closure, and cleanup of the raw producer. -/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls SubexpScanPrimitives
open Subexp.ConstructivePacking

variable {D r Q Δ : ℕ}

def outsideCost
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ)) (t : Fin Q) : ℕ :=
  Subexp.SupportSelectionProgram.budget
    (Subexp.SupportSelectionProgram.metadataTable P).length D t.val r [] +
  (2 * (selectedSupport P t 0).length + 3) + 6 * (selectedOutside P).length + 6

theorem initializeOutside_eval
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (suffix : Word) (d : Data) (hm : Masters P t items suffix d.stacks)
    (hw : ColorWork d.stacks) (h208 : d.stacks 208 = []) (h219 : d.stacks 219 = []) :
    ∃ n e, n ≤ outsideCost P t ∧ Eval initializeOutside n d e ∧
      e.stacks = Function.update d.stacks 208 (selectedOutside P) := by
  obtain ⟨ns, a, hns, hs, _ha, ha⟩ := selectSupport_eval P t d hw.workspace
    hw.support hw.outside hm.dimension hm.node hm.colors hm.metadata
  rw [h219] at hns ha
  change a.stacks = Function.update
    (Function.update d.stacks 209 (selectedSupport P t 0)) 223 (selectedOutside P) at ha
  let b := cleared 209 a
  have ha209 : a.stacks 209 = selectedSupport P t 0 := by simp [ha]
  have hc : Eval (clear 209) (2 * (selectedSupport P t 0).length + 3) a b := by
    have he : Eval (clear 209) (2 * (a.stacks 209).length + 3) a b := clear_eval 209 a
    simpa only [ha209] using he
  let c := afterTransfer b 223 224 0 1
  have hb223 : b.stacks 223 = selectedOutside P := by simp [b, cleared, ha]
  have ht1 : Eval (transfer 223 224) (3 * (selectedOutside P).length + 3) b c := by
    have he : Eval (transfer 223 224) (3 * (b.stacks 223).length + 3) b c :=
      transfer_eval 223 224 (by decide) b
    simpa only [hb223] using he
  have hc224 : c.stacks 224 = (selectedOutside P).reverse := by
    simp [c, afterTransfer, StackRoutines.transferStacks, b, cleared, ha, hw.forward]
  let e := afterTransfer c 224 208 0 1
  have ht2 : Eval (transfer 224 208) (3 * (selectedOutside P).length + 3) c e := by
    have he : Eval (transfer 224 208) (3 * (c.stacks 224).length + 3) c e :=
      transfer_eval 224 208 (by decide) c
    simpa only [hc224, List.length_reverse] using he
  refine ⟨ns + ((2 * (selectedSupport P t 0).length + 3) +
    ((3 * (selectedOutside P).length + 3) + (3 * (selectedOutside P).length + 3))), e,
    ?_, hs.seq (hc.seq (ht1.seq ht2)), ?_⟩
  · unfold outsideCost
    omega
  · funext i
    by_cases hi208 : i = 208
    · subst i
      simp [e, afterTransfer, StackRoutines.transferStacks, c, b, cleared, ha, h208, hw.forward]
    by_cases h209 : i = 209
    · subst i
      simp [e, afterTransfer, StackRoutines.transferStacks, c, b, cleared, hw.support]
    by_cases h223 : i = 223
    · subst i
      simp [e, afterTransfer, StackRoutines.transferStacks, c, hw.outside]
    by_cases h224 : i = 224
    · subst i
      simp [e, afterTransfer, StackRoutines.transferStacks, hw.forward]
    · simp [e, afterTransfer, StackRoutines.transferStacks, c, b, cleared, ha,
        hi208, h209, h223, h224]

def closeCost (groups : List Word) (count : ℕ) : ℕ :=
  8 + 3 * (Encoding.encodeList id groups).length + 2 * (colorWord count).length

theorem closeGroups_eval (groups : List Word) (count : ℕ) (d : Data)
    (h211 : d.stacks 211 = (recordBytes id groups).reverse)
    (h212 : d.stacks 212 = []) (h219 : d.stacks 219 = colorWord count) :
    ∃ e, Eval closeGroups (closeCost groups count) d e ∧
      e.stacks = Function.update
        (Function.update (Function.update d.stacks 211 []) 212 (Encoding.encodeList id groups))
        219 [] := by
  let a := pushed 211 false d
  have ha211 : a.stacks 211 = (Encoding.encodeList id groups).reverse := by
    simp [a, pushed, h211, encodeList_eq_records, List.reverse_append]
  let b := afterTransfer a 211 212 0 1
  have ht : Eval (transfer 211 212) (3 * (Encoding.encodeList id groups).length + 3) a b := by
    have he : Eval (transfer 211 212) (3 * (a.stacks 211).length + 3) a b :=
      transfer_eval 211 212 (by decide) a
    simpa only [ha211, List.length_reverse] using he
  have hb219 : b.stacks 219 = colorWord count := by
    simp [b, afterTransfer, StackRoutines.transferStacks, a, pushed, h219]
  let e := cleared 219 b
  have hc : Eval (clear 219) (2 * (colorWord count).length + 3) b e := by
    have he : Eval (clear 219) (2 * (b.stacks 219).length + 3) b e := clear_eval 219 b
    simpa only [hb219] using he
  have he := (pushBit_eval 211 false d).seq (ht.seq hc)
  have hn : 2 + (3 * (Encoding.encodeList id groups).length + 3 +
      (2 * (colorWord count).length + 3)) = closeCost groups count := by
    unfold closeCost; omega
  rw [hn] at he
  refine ⟨e, he, ?_⟩
  funext i
  by_cases h211' : i = 211
  · subst i
    simp [e, cleared, b, afterTransfer, StackRoutines.transferStacks]
  by_cases h212' : i = 212
  · subst i
    simp [e, cleared, b, afterTransfer, StackRoutines.transferStacks, a, pushed, h212, h211,
      encodeList_eq_records]
  by_cases h219' : i = 219
  · subst i; simp [e, cleared]
  · simp [e, cleared, b, afterTransfer, StackRoutines.transferStacks, a, pushed,
      h211', h212', h219']

def cleanupCost (store : Store) : ℕ :=
  2 * (store 208).length + 2 * (store 212).length + 2 * (store 225).length +
    2 * (store 226).length + 2 * (store 227).length + 15

def cleanedStore (store : Store) : Store :=
  Function.update (Function.update (Function.update
    (Function.update (Function.update store 208 []) 212 []) 225 []) 226 []) 227 []

theorem cleanup_eval (d : Data) :
    ∃ e, Eval cleanup (cleanupCost d.stacks) d e ∧ e.stacks = cleanedStore d.stacks := by
  let a := cleared 208 d
  let b := cleared 212 a
  let c := cleared 225 b
  let f := cleared 226 c
  let e := cleared 227 f
  have h1 := clear_eval 208 d
  have h2 : Eval (clear 212) (2 * (d.stacks 212).length + 3) a b := by
    have hp : a.stacks 212 = d.stacks 212 := by simp [a, cleared]
    have he : Eval (clear 212) (2 * (a.stacks 212).length + 3) a b := clear_eval 212 a
    simpa only [hp] using he
  have h3 : Eval (clear 225) (2 * (d.stacks 225).length + 3) b c := by
    have hp : b.stacks 225 = d.stacks 225 := by simp [b, a, cleared]
    have he : Eval (clear 225) (2 * (b.stacks 225).length + 3) b c := clear_eval 225 b
    simpa only [hp] using he
  have h4 : Eval (clear 226) (2 * (d.stacks 226).length + 3) c f := by
    have hp : c.stacks 226 = d.stacks 226 := by simp [c, b, a, cleared]
    have he : Eval (clear 226) (2 * (c.stacks 226).length + 3) c f := clear_eval 226 c
    simpa only [hp] using he
  have h5 : Eval (clear 227) (2 * (d.stacks 227).length + 3) f e := by
    have hp : f.stacks 227 = d.stacks 227 := by simp [f, c, b, a, cleared]
    have he : Eval (clear 227) (2 * (f.stacks 227).length + 3) f e := clear_eval 227 f
    simpa only [hp] using he
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  have hn : (2 * (d.stacks 208).length + 3) + ((2 * (d.stacks 212).length + 3) +
    ((2 * (d.stacks 225).length + 3) + ((2 * (d.stacks 226).length + 3) +
      (2 * (d.stacks 227).length + 3)))) = cleanupCost d.stacks := by
    unfold cleanupCost; omega
  rw [hn] at he
  exact ⟨e, he, rfl⟩

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
