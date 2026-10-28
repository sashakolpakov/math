import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramLess
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeIndexEncoding

namespace OAI.Algorithms

/-! Fixed primitive clipping for sparse keys. The key and both unary limits
are disposable inputs; all four local stacks are empty on return. Callers may
keep master copies outside these ports. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev clipField (budget : Fin 4) : Cmd 5 4 :=
  .seq (readNat 0 3) (lessClear 3 budget)

theorem clipField_eval (d : State 5 4) (budget : Fin 4)
    (h0 : budget ≠ 0) (h3 : budget ≠ 3) (u : ℕ) (rest : List Bool)
    (hin : d.stacks 0 = Encoding.encodeNat u ++ rest) (hb : d.stacks 3 = []) :
    ∃ time ≤ 10*u+2*(d.stacks budget).length+16, ∃ rf,
      Eval (clipField budget) time d
        (⟨rf,Function.update (Function.update (Function.update d.stacks 0 rest) 3 []) budget []⟩ : State 5 4) ∧
      rf 3 = decide (u < (d.stacks budget).length) ∧ rf 4 = d.regs 4 := by
  have hp := readNat_eval d 0 3 (by decide) u rest hin
  let a := afterNat d 0 3 u rest
  have ha3 : a.stacks 3 = List.replicate u true := by simp [a,afterNat,hb]
  have hab : a.stacks budget = d.stacks budget := by simp [a,afterNat,h0,h3]
  obtain ⟨time,ht,rf,h,hf,h4⟩ := lessClear_eval a 3 budget (Ne.symm h3)
  have hs : (⟨rf,Function.update (Function.update a.stacks 3 []) budget []⟩ : State 5 4) =
      (⟨rf,Function.update (Function.update (Function.update d.stacks 0 rest) 3 []) budget []⟩ : State 5 4) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    by_cases hi : i = budget <;> by_cases hj : i = 3 <;>
      simp_all [a,afterNat]
  rw [hs] at h
  refine ⟨(4*u+4)+time,?_,rf,hp.seq h,?_,?_⟩
  · rw [ha3,hab,List.length_replicate] at ht
    omega
  · simpa [ha3,hab] using hf
  · simpa [a,afterNat,readRegs] using h4

abbrev clipState (regs : Fin 5 → Bool) (source t J buffer : List Bool) : State 5 4 :=
  ⟨regs,![source,t,J,buffer]⟩

abbrev clipIndex : Cmd 5 4 :=
  .seq (clipField 1) (.seq (.base (.atom (.copy 4 3)))
    (.seq (clipField 2) (.seq (.base (.atom (.band 4 4 3))) (clearAt 0))))

def clipIndexProgram := compiled clipIndex 0 0

theorem clipIndex_eval (regs : Fin 5 → Bool) (u z : ℕ) (mask t J : List Bool) :
    ∃ time ≤ 10*(u+z)+2*(t.length+J.length)+2*mask.length+37, ∃ rf,
      Eval clipIndex time
        (clipState regs (Encoding.encodeNat u ++ Encoding.encodeNat z ++ mask) t J [])
        (clipState rf [] [] [] []) ∧
      rf 4 = decide (u < t.length ∧ z < J.length) := by
  let source := Encoding.encodeNat z ++ mask
  obtain ⟨n1,hn1,r1,h1,hf1,h41⟩ := clipField_eval
    (clipState regs (Encoding.encodeNat u ++ source) t J []) 1 (by decide) (by decide)
    u source rfl rfl
  have h1' : Eval (clipField 1) n1
      (clipState regs (Encoding.encodeNat u ++ source) t J [])
      (clipState r1 source [] J []) := by
    convert h1 using 1
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i; fin_cases i <;> simp []
  let r2 := Function.update r1 (4 : Fin 5) (r1 3)
  have hcopy : Eval (.base (.atom (.copy 4 3))) 1
      (clipState r1 source [] J []) (clipState r2 source [] J []) := by
    apply Eval.base
    convert StructuredProgram.Eval.atom (StructuredProgram.Atom.copy (4 : Fin 5) 3)
      (clipState r1 source [] J []) using 1
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨n2,hn2,r3,h2,hf2,h42⟩ := clipField_eval
    (clipState r2 source [] J []) 2 (by decide) (by decide) z mask rfl rfl
  have h2' : Eval (clipField 2) n2
      (clipState r2 source [] J []) (clipState r3 mask [] [] []) := by
    convert h2 using 1
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i; fin_cases i <;> simp []
  let r4 := Function.update r3 (4 : Fin 5) (r3 4 && r3 3)
  have hband : Eval (.base (.atom (.band 4 4 3))) 1
      (clipState r3 mask [] [] []) (clipState r4 mask [] [] []) := by
    apply Eval.base
    convert StructuredProgram.Eval.atom (StructuredProgram.Atom.band (4 : Fin 5) 4 3)
      (clipState r3 mask [] [] []) using 1
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · rfl
  let rf := readRegs r4 (0 : Fin 5) 1 none
  have hc := clearAt_eval (clipState r4 mask [] [] []) 0
  have hc' : Eval (clearAt 0) (2*mask.length+3)
      (clipState r4 mask [] [] []) (clipState rf [] [] [] []) := by
    convert hc using 1
    · simp []
    · apply congrArg₂ StructuredProgram.State.mk rfl
      funext i; fin_cases i <;> simp []
  refine ⟨n1+(1+(n2+(1+(2*mask.length+3)))),?_,rf,?_,?_⟩
  · simp [] at hn1 hn2
    omega
  · simpa [clipIndex,source,List.append_assoc] using h1'.seq (hcopy.seq (h2'.seq (hband.seq hc')))
  · simp [] at hf1 hf2 h42
    by_cases hu : u < t.length <;> by_cases hz : z < J.length <;>
      simp [rf,r4,r2,readRegs,h42,hf1,hf2,hu,hz]

/-- Actual machine clipping is exactly the semantic `Index.Kept` predicate. -/
theorem clipIndex_trace {n : ℕ} (a : Index (Fin n)) (t J : ℕ) (regs : Fin 5 → Bool) :
    ∃ time ≤ 10*(a.u+a.z)+2*(t+J)+2*n+38, ∃ rf,
      Trace clipIndexProgram time
        ((clipState regs (encodeIndex a) (List.replicate t true) (List.replicate J true) []).withPC
          (some clipIndexProgram.entry))
        ((clipState rf [] [] [] []).withPC none) ∧
      rf 4 = decide (a.Kept t J) := by
  obtain ⟨time,ht,rf,h,hf⟩ := clipIndex_eval regs a.u a.z (encodeMask a.vars)
    (List.replicate t true) (List.replicate J true)
  refine ⟨time+1,?_,rf,?_,?_⟩
  · simpa only [List.length_replicate,encodeMask_length] using (Nat.add_le_add_right ht 1)
  · simpa [clipIndexProgram,encodeIndex] using compiled_halt_trace h 0 0
  · simp only [List.length_replicate] at hf
    by_cases h : a.u < t ∧ a.z < J
    · simpa only [Index.Kept, h, decide_true] using hf
    · simpa only [Index.Kept, h, decide_false] using hf

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
