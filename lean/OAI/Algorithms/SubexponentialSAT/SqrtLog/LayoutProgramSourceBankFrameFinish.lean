import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankFrameEmitter

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def deltaWord (a : Data) : List Bool :=
  if a.stacks 23=a.stacks 24 then a.stacks 314 else a.stacks 313

theorem delta_eval (a : Data) (ht : a.stacks 319=[]) (he : a.stacks 274=[]) :
    let word := if a.regs 7 then a.stacks 314 else a.stacks 313
    ∃ b : Data, Eval delta (7*word.length+6) a b ∧
      b.stacks=Function.update a.stacks 274 word := by
  intro word
  cases hf : a.regs 7 with
  | false =>
      let b := Staging.actionResult 0 1 (.copy 313 274) a
      have h := Staging.action_eval 0 1 319 (by decide) (.copy 313 274) a (by decide) ht
      refine ⟨b,?_,?_⟩
      · simpa [delta,word,hf,Staging.actionCost] using
          (Eval.ite_false (yes:=Staging.action 0 1 319 (.copy 314 274)) hf h)
      · simp [b,word,hf,Staging.actionResult,StackRoutines.copyStacks,he]
  | true =>
      let b := Staging.actionResult 0 1 (.copy 314 274) a
      have h := Staging.action_eval 0 1 319 (by decide) (.copy 314 274) a (by decide) ht
      refine ⟨b,?_,?_⟩
      · simpa [delta,word,hf,Staging.actionCost] using
          (Eval.ite_true (no:=Staging.action 0 1 319 (.copy 313 274)) hf h)
      · simp [b,word,hf,Staging.actionResult,StackRoutines.copyStacks,he]

theorem clearedStacks_eq (a b : Data)
    (h : ∀ j,j∉cleanupPorts → b.stacks j=a.stacks j) : clearedStacks b=clearedStacks a := by
  funext j
  by_cases hj : j∈cleanupPorts <;> simp [clearedStacks,hj,h]

def sourceWord (tables : UniversalRowLoop.Tables) (positions : List ℕ) (a : Data) : List Bool :=
  UniversalRowProgram.rowCode (a.stacks 313) (a.stacks 314) (a.stacks 313++a.stacks 314)
    (UniversalRowDataProgram.row tables positions (deltaWord a) (a.stacks 47))

def finishBound (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool)
    (positions : List ℕ) (a : Data) (B : ℕ) : ℕ :=
  18*(a.stacks 23).length+9*(a.stacks 24).length+35+
    (7*B+6+(7*emitterSize a+50+
      UniversalRowSourceProgram.bound tables width rowWidth positions
        (deltaWord a) (a.stacks 47) (a.stacks 313) (a.stacks 314)+120*B+180))

theorem finish_universal_eval (a : Data) (ht : a.stacks 319=[]) (hclean : EmitterClean a)
    (h274 : a.stacks 274=[]) (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[])
    (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[])
    (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool) (positions : List ℕ)
    (valid : UniversalRowLoop.Valid tables width rowWidth positions)
    (hv : a.stacks 67=tables.values.flatten) (hi : a.stacks 308=tables.inverses.flatten)
    (hn : a.stacks 309=tables.negatives.flatten) (hr : a.stacks 310=tables.rows.flatten)
    (hp : a.stacks 71=UniversalRowTermProgram.indices positions)
    (hw : a.stacks 311=width) (hrw : a.stacks 312=rowWidth)
    (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∃ n ≤ finishBound tables width rowWidth positions a B,
      ∃ b : Data, Eval (.seq (.seq compareTypes (.seq delta (.seq stageEmitter emit))) cleanup) n a b ∧
        b.stacks=Function.update (clearedStacks a) 287 (sourceWord tables positions a) := by
  obtain ⟨nc,hnc,b,hc,hbs,h7⟩ := compareTypes_eval a h0 h1 h2 h3
  obtain ⟨c,hd,hcs⟩ := delta_eval b (by simpa [hbs] using ht) (by simpa [hbs] using h274)
  have hdw : (if b.regs 7 then b.stacks 314 else b.stacks 313)=deltaWord a := by
    simp [h7,hbs,deltaWord]
  rw [hdw] at hd hcs
  rw [hbs] at hcs
  have hcl : EmitterClean c := by
    intro j hj hk hne
    simpa [hcs,hne] using hclean j hj hk hne
  have hcb : ∀ j,(c.stacks j).length ≤ B := by
    intro j
    by_cases hj : j=274
    · subst j
      simp only [hcs,Function.update_same]
      unfold deltaWord
      split_ifs <;> apply hB
    · simpa [hcs,hj] using hB j
  have hclear : clearedStacks c=clearedStacks a := by
    apply clearedStacks_eq
    intro j hj
    have hne : j≠274 := by intro h; subst j; exact hj (by decide)
    simp [hcs,hne]
  obtain ⟨ne,hne,z,he,hzs⟩ := stage_emit_cleanup_eval c
    (by simpa [hcs] using ht) hcl tables width rowWidth positions valid
    (by simpa [hcs] using hv) (by simpa [hcs] using hi)
    (by simpa [hcs] using hn) (by simpa [hcs] using hr)
    (by simpa [hcs] using hp) (by simpa [hcs] using hw)
    (by simpa [hcs] using hrw) B hcb
  have hemit : emitterSize c=emitterSize a := by simp [emitterSize,hcs]
  have hdlen : (deltaWord a).length ≤ B := by
    unfold deltaWord
    split_ifs <;> apply hB
  refine ⟨nc+(7*(deltaWord a).length+6+ne),?_,z,prepend_cleanup hc (prepend_cleanup hd he),?_⟩
  · simp only [hcs,Function.update_same,Function.update_of_ne (by decide : (47:Fin 320)≠274),
      Function.update_of_ne (by decide : (313:Fin 320)≠274),
      Function.update_of_ne (by decide : (314:Fin 320)≠274),hemit] at hne
    unfold finishBound
    omega
  · simpa [hcs,hclear,sourceWord] using hzs

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
