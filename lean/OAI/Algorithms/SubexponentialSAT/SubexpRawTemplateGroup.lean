import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateTraversal

namespace OAI.Algorithms

/-! Actual construction of the common color groups in a raw template. -/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls SubexpScanPrimitives

def termBytes (increment support factors : Word) : Word :=
  Encoding.frame increment ++ Encoding.frame support ++ Encoding.frame factors

def groupBytes (support factors : Word) (increments : List Word) : Word :=
  Encoding.encodeList (fun inc => termBytes inc support factors) increments

def termBody : Code :=
  .seq (capture 206 207 (by decide))
    (.seq (appendFrame 207 213) (.seq (appendFrame 209 213)
      (.seq (appendFrame 210 213) (.seq (clear 207) (.seq (transfer 213 224)
        (.seq (appendRecord 224 215) (clear 224)))))))

def termCost (increment support factors : Word) : ℕ :=
  19 * increment.length + 8 * support.length + 8 * factors.length +
    13 * (termBytes increment support factors).length + 46

def termResult (increment support factors tail : Word) (d : Data) : Data :=
  ⟨afterFrameRegs d.regs,
    Function.update (Function.update d.stacks 206 tail) 215
      ((record (termBytes increment support factors)).reverse ++ d.stacks 215)⟩

theorem termBody_eval (increment support factors tail : Word) (d : Data)
    (hin : d.stacks 206 = Encoding.frame increment ++ tail)
    (h207 : d.stacks 207 = []) (h213 : d.stacks 213 = [])
    (h218 : d.stacks 218 = []) (h224 : d.stacks 224 = [])
    (h209 : d.stacks 209 = support) (h210 : d.stacks 210 = factors) :
    Eval termBody (termCost increment support factors) d
      (termResult increment support factors tail d) := by
  let a := captured 206 207 increment tail d
  let b := framed 207 213 a
  let c := framed 209 213 b
  let e := framed 210 213 c
  let f := cleared 207 e
  let g := afterTransfer f 213 224 0 1
  let h := recorded 224 215 g
  let j := cleared 224 h
  have ha := capture_eval 206 207 (by decide) (by decide) (by decide)
    increment tail d hin h207 h218
  have hb : Eval (appendFrame 207 213) (8 * increment.length + 7) a b := by
    have hv : a.stacks 207 = increment := by simp [a, captured]
    have ht : Eval (appendFrame 207 213) (8 * (a.stacks 207).length + 7) a b :=
      appendFrame_eval 207 213 (by decide) (by decide) (by decide) a
        (by simp [a, captured, h218])
    simpa only [hv] using ht
  have hc : Eval (appendFrame 209 213) (8 * support.length + 7) b c := by
    have hv : b.stacks 209 = support := by simp [b, a, framed, captured, h209]
    have ht : Eval (appendFrame 209 213) (8 * (b.stacks 209).length + 7) b c :=
      appendFrame_eval 209 213 (by decide) (by decide) (by decide) b
        (by simp [b, a, framed, captured, h218])
    simpa only [hv] using ht
  have he : Eval (appendFrame 210 213) (8 * factors.length + 7) c e := by
    have hv : c.stacks 210 = factors := by simp [c, b, a, framed, captured, h210]
    have ht : Eval (appendFrame 210 213) (8 * (c.stacks 210).length + 7) c e :=
      appendFrame_eval 210 213 (by decide) (by decide) (by decide) c
        (by simp [c, b, a, framed, captured, h218])
    simpa only [hv] using ht
  have hf : Eval (clear 207) (2 * increment.length + 3) e f := by
    have hv : e.stacks 207 = increment := by simp [e, c, b, a, framed, captured]
    have ht : Eval (clear 207) (2 * (e.stacks 207).length + 3) e f := clear_eval 207 e
    simpa only [hv] using ht
  have hf213 : f.stacks 213 = (termBytes increment support factors).reverse := by
    simp [f, e, c, b, a, cleared, framed, captured, h209, h210, h213,
      termBytes, List.reverse_append, List.append_assoc]
  have hf224 : f.stacks 224 = [] := by
    simp [f, e, c, b, a, cleared, framed, captured, h224]
  have hg : Eval (transfer 213 224)
      (3 * (termBytes increment support factors).length + 3) f g := by
    have ht : Eval (transfer 213 224) (3 * (f.stacks 213).length + 3) f g :=
      transfer_eval 213 224 (by decide) f
    simpa only [hf213, List.length_reverse] using ht
  have hg224 : g.stacks 224 = termBytes increment support factors := by
    simp [g, afterTransfer, StackRoutines.transferStacks, hf213, hf224]
  have hg218 : g.stacks 218 = [] := by
    simp [g, f, e, c, b, a, afterTransfer, StackRoutines.transferStacks,
      cleared, framed, captured, h218]
  have hh : Eval (appendRecord 224 215)
      (8 * (termBytes increment support factors).length + 9) g h := by
    have ht : Eval (appendRecord 224 215) (8 * (g.stacks 224).length + 9) g h :=
      appendRecord_eval 224 215 (by decide) (by decide) (by decide) g hg218
    simpa only [hg224] using ht
  have hj : Eval (clear 224) (2 * (termBytes increment support factors).length + 3) h j := by
    have hv : h.stacks 224 = termBytes increment support factors := by simp [h, recorded, hg224]
    have ht : Eval (clear 224) (2 * (h.stacks 224).length + 3) h j := clear_eval 224 h
    simpa only [hv] using ht
  have hg215 : g.stacks 215 = d.stacks 215 := by
    simp [g, f, e, c, b, a, afterTransfer, StackRoutines.transferStacks,
      cleared, framed, captured]
  have hfinal : j = termResult increment support factors tail d := by
    apply state_ext
    · funext i
      by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;>
        simp [j, h, g, f, e, c, b, a, cleared, recorded, afterTransfer, framed,
          captured, termResult, afterFrameRegs, readRegs, h0, h1, h2]
    · funext i
      by_cases hi206 : i = 206
      · subst i
        simp [j, h, g, f, e, c, b, a, cleared, recorded, afterTransfer, framed,
          captured, termResult, StackRoutines.transferStacks]
      by_cases hi207 : i = 207
      · subst i
        simp [j, h, g, f, cleared, recorded, afterTransfer, termResult,
          StackRoutines.transferStacks, h207]
      by_cases hi213 : i = 213
      · subst i
        simp [j, h, g, cleared, recorded, afterTransfer, termResult,
          StackRoutines.transferStacks, h213]
      by_cases hi224 : i = 224
      · subst i
        simp [j, cleared, termResult, h224]
      by_cases hi215 : i = 215
      · subst i
        simp [j, h, recorded, cleared, hg224, hg215, termResult]
      · simp [j, h, g, f, e, c, b, a, cleared, recorded, afterTransfer, framed,
          captured, termResult, StackRoutines.transferStacks,
          hi206, hi207, hi213, hi224, hi215]
  have ht := ha.seq (hb.seq (hc.seq (he.seq (hf.seq (hg.seq (hh.seq hj))))))
  rw [hfinal] at ht
  change Eval termBody _ d (termResult increment support factors tail d) at ht
  convert ht using 1
  unfold termCost
  omega

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
