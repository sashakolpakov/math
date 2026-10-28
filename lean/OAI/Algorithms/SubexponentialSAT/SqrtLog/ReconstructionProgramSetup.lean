import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterFinish

namespace OAI.Algorithms

/-! Arbitrary-width physical CRT initialization. The computed ring-zero word
is passed on stack 280; all copying, width construction and unary-to-binary
conversion are charged by actual primitive traces. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def initializeCode : Code :=
  copy 280 104 ;; copy 280 261 ;; countDimension ;; buildJetWidth ;;
  copy 256 214 ;; copy 256 257 ;; copy 265 266

def initializationBudget (W J nodeBits jetBits : ℕ) : ℕ :=
  14 * W + SubexpFactorCountSetup.countBudget J + J * (7 * W + 14) +
    14 * nodeBits + 7 * jetBits + 37

def initializedStacks (d : Data) (D : ℕ) (exponent : List Bool) : Fin 320 → List Bool :=
  let zero := d.stacks 280
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update d.stacks
      104 zero) 261 zero) 268 exponent)
      277 (Subexp.BlockCopyProgram.copies D zero))
      214 (d.stacks 256)) 257 (d.stacks 256)) 266 (d.stacks 265)

theorem initialize_run (d : Data) (D : ℕ)
    (hd : d.stacks 243 = List.replicate D true)
    (hclean : ∀ j ∈ ([104,261,268,277,278,279,316,317,318,214,257,266] : List (Fin 320)),
      d.stacks j = []) :
    ∃ n ≤ initializationBudget (d.stacks 280).length D
        (d.stacks 256).length (d.stacks 265).length,
      ∃ (rf : Fin 16 → Bool) (exponent : List Bool),
        Eval initializeCode n d ⟨rf, initializedStacks d D exponent⟩ ∧
        BinaryArithmetic.toNat exponent = D ∧ exponent.length ≤ D := by
  have hz (j : Fin 320) (h : j ∈ ([104,261,268,277,278,279,316,317,318,214,257,266] :
      List (Fin 320))) : d.stacks j = [] := hclean j h
  have h1 := copy_run d 280 104 (by decide) (by decide) (by decide) (hz 318 (by simp))
  let d1 := afterCopy d 280 104 0 1
  have h2 := copy_run d1 280 261 (by decide) (by decide) (by decide)
    (by simpa [d1, afterCopy, StackRoutines.copyStacks] using hz 318 (by simp))
  let d2 := afterCopy d1 280 261 0 1
  obtain ⟨nc, hnc, rc, exponent, hc, he, hl⟩ := countDimension_run d2
    (by simpa [d2, d1, afterCopy, StackRoutines.copyStacks] using hz 268 (by simp))
    (by simpa [d2, d1, afterCopy, StackRoutines.copyStacks] using hz 316 (by simp))
    (by simpa [d2, d1, afterCopy, StackRoutines.copyStacks] using hz 317 (by simp))
  let d3 : Data := ⟨rc, Function.update d2.stacks 268 exponent⟩
  have h3 := buildJetWidth_run d3 D
    (by simpa [d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hd)
    (by simpa [d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hz 278 (by simp))
    (by simpa [d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hz 279 (by simp))
    (by simpa [d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hz 318 (by simp))
  let d4 := jetWidthState d3 D
  have h4 := copy_run d4 256 214 (by decide) (by decide) (by decide)
    (by simpa [d4, jetWidthState, d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hz 318 (by simp))
  let d5 := afterCopy d4 256 214 0 1
  have h5 := copy_run d5 256 257 (by decide) (by decide) (by decide)
    (by simpa [d5, afterCopy, StackRoutines.copyStacks, d4, jetWidthState,
      d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hz 318 (by simp))
  let d6 := afterCopy d5 256 257 0 1
  have h6 := copy_run d6 265 266 (by decide) (by decide) (by decide)
    (by simpa [d6, d5, afterCopy, StackRoutines.copyStacks, d4, jetWidthState,
      d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hz 318 (by simp))
  have hfinal : (afterCopy d6 265 266 0 1).stacks = initializedStacks d D exponent := by
    simp [d6, d5, afterCopy, StackRoutines.copyStacks, d4,
      d3, d2, d1, afterCopy, StackRoutines.copyStacks, initializedStacks,
      hz 104 (by simp), hz 261 (by simp), hz 214 (by simp), hz 257 (by simp), hz 266 (by simp), hz 277 (by simp)]
  have hexp : BinaryArithmetic.toNat exponent = D := by
    simpa [d2, d1, afterCopy, StackRoutines.copyStacks, hd] using he
  have hlength : exponent.length ≤ D := by
    simpa [d2, d1, afterCopy, StackRoutines.copyStacks, hd] using hl
  have hcBound : nc ≤ SubexpFactorCountSetup.countBudget D + 1 := by
    simpa [d2, d1, afterCopy, StackRoutines.copyStacks, hd] using hnc
  have hassoc {a b c : Code} {n : ℕ} {s t : Data}
      (h : Eval (.seq (.seq a b) c) n s t) : Eval (.seq a (.seq b c)) n s t := by
    cases h with
    | seq hab hc =>
      cases hab with
      | seq ha hb => simpa only [Nat.add_assoc] using ha.seq (hb.seq hc)
  have hrun' := h1.seq (h2.seq (hc.seq (h3.seq (h4.seq (h5.seq h6)))))
  have hresult : afterCopy d6 265 266 0 1 =
      (⟨(afterCopy d6 265 266 0 1).regs, initializedStacks d D exponent⟩ : Data) :=
    state_ext rfl hfinal
  change Eval initializeCode _ d _ at hrun'
  rw [hresult] at hrun'
  refine ⟨_, ?_, _, exponent, hrun', hexp, hlength⟩
  simp [d6, d5, afterCopy, StackRoutines.copyStacks, d4,
    d3, d2, d1, afterCopy, StackRoutines.copyStacks, initializationBudget, hz 104 (by simp)]
  nlinarith

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
