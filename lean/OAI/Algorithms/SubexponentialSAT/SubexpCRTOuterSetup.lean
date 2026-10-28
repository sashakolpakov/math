import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterControl

namespace OAI.Algorithms

/-! Actual initialization for the outer CRT tape controller. Widths and the
binary dimension are computed by fixed programs from the retained runtime
inputs. In particular, neither a binary exponent nor a jet-width word is
provided for free. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev moved (d : Data) (src dst : Fin 320) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks src []) dst (d.stacks src)⟩

theorem move_run (d : Data) (src dst : Fin 320)
    (hs : src ≠ 319) (hd : dst ≠ 319) (hsd : src ≠ dst)
    (ht : d.stacks 319 = []) (he : d.stacks dst = []) :
    Eval (move src dst) (6 * (d.stacks src).length + 6) d (moved d src dst) := by
  have h1 := transfer_eval d src 319 0 1 hs (by decide)
  let mid := afterTransfer d src 319 0 1
  have h2 := transfer_eval mid 319 dst 0 1 hd.symm (by decide)
  have hlen : (mid.stacks 319).length = (d.stacks src).length := by
    simp [mid, afterTransfer, StackRoutines.transferStacks, ht]
  have hfinal : afterTransfer mid 319 dst 0 1 = moved d src dst := by
    apply state_ext
    · simp [mid, afterTransfer, StackRoutines.readRegs_reset]
    · funext i
      by_cases hi : i = dst
      · subst i
        simp [mid, afterTransfer, StackRoutines.transferStacks, hd, hsd.symm, ht, he]
      · by_cases hj : i = src
        · subst i
          simp [mid, afterTransfer, StackRoutines.transferStacks, hs, hsd ]
        · by_cases hk : i = 319
          · subst i
            simp [mid, afterTransfer, StackRoutines.transferStacks, hi, hs.symm, ht]
          · simp [mid, afterTransfer, StackRoutines.transferStacks, hi, hj, hk]
  rw [hfinal] at h2
  have h := h1.seq h2
  simpa only [move, transfer, hlen,
    show 3 * (d.stacks src).length + 3 + (3 * (d.stacks src).length + 3) =
      6 * (d.stacks src).length + 6 by omega] using h

theorem countDimension_run (d : Data)
    (ho : d.stacks 268 = []) (hc : d.stacks 316 = []) (ht : d.stacks 317 = []) :
    ∃ n ≤ SubexpFactorCountSetup.countBudget (d.stacks 243).length + 1,
      ∃ (rf : Fin 16 → Bool) (exponent : List Bool),
        Eval countDimension n d ⟨rf, Function.update d.stacks 268 exponent⟩ ∧
        BinaryArithmetic.toNat exponent = (d.stacks 243).length ∧
        exponent.length ≤ (d.stacks 243).length := by
  let localIn := projectState registers countPorts d
  obtain ⟨rf, exponent, ⟨n, hn, htrace⟩, he, hl⟩ :=
    SubexpFactorCountSetup.count_program_runsIn localIn ho hc ht
  let localOut : State 8 13 := ⟨rf, Function.update localIn.stacks 2 exponent⟩
  have hrun := eval_call_from_state SubexpFactorCountSetup.countProgram registers countPorts d
    registers.injective countPorts.injective (b := localOut) htrace
  have hagree : Function.extend countPorts localIn.stacks d.stacks = d.stacks :=
    congrArg StructuredProgram.State.stacks
      (embedState_project registers countPorts d registers.injective countPorts.injective)
  have hfinal : embedState registers countPorts d localOut =
      (⟨Function.extend registers rf d.regs, Function.update d.stacks 268 exponent⟩ : Data) := by
    apply state_ext
    · rfl
    · change Function.extend countPorts (Function.update localIn.stacks 2 exponent) d.stacks = _
      rw [ProgramLinking.extend_update countPorts.injective, hagree]
      rfl
  refine ⟨n, hn, Function.extend registers rf d.regs, exponent, ?_, he, hl⟩
  simpa only [countDimension, hfinal] using hrun

abbrev threeReset (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false,
    d.stacks⟩

theorem resetThree_run (d : Data) : Eval resetThreeRegisters 3 d (threeReset d) := by
  have h0 := StructuredProgram.Eval.atom (.set (0 : Fin 16) false) d
  have h1 := StructuredProgram.Eval.atom (.set (1 : Fin 16) false)
    ((StructuredProgram.Atom.set 0 false).eval d)
  have h2 := StructuredProgram.Eval.atom (.set (2 : Fin 16) false)
    ((StructuredProgram.Atom.set 1 false).eval ((StructuredProgram.Atom.set 0 false).eval d))
  have h := Eval.base (h0.seq (h1.seq h2))
  simpa [resetThreeRegisters, threeReset, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h

theorem blockCopy_run (d : Data) (D : ℕ)
    (hr : ∀ i : Fin 3, d.regs (threeRegisters i) = false)
    (hc : d.stacks 279 = List.replicate D true) (ht : d.stacks 278 = []) :
    Eval (.call (ProgramLinking.liftProgram Subexp.BlockCopyProgram.program
      threeRegisters blockCopyPorts))
      (D * (7 * (d.stacks 104).length + 7) + 3) d
      ⟨d.regs, Function.update (Function.update d.stacks 277
        (Subexp.BlockCopyProgram.copies D (d.stacks 104) ++ d.stacks 277)) 279 []⟩ := by
  let localIn := Subexp.BlockCopyProgram.initialState D (d.stacks 104) (d.stacks 277)
  let localOut := Subexp.BlockCopyProgram.data false false (d.stacks 104)
    (Subexp.BlockCopyProgram.copies D (d.stacks 104) ++ d.stacks 277) []
  have hin : projectState threeRegisters blockCopyPorts d = localIn := by
    apply state_ext
    · funext i
      fin_cases i <;> simp [projectState, localIn, Subexp.BlockCopyProgram.initialState,
        Subexp.BlockCopyProgram.data, hr]
    · funext i
      fin_cases i <;> simp [projectState, blockCopyPorts, localIn,
        Subexp.BlockCopyProgram.initialState, Subexp.BlockCopyProgram.data, hc, ht]
  have htrace := Subexp.BlockCopyProgram.program_trace D (d.stacks 104) (d.stacks 277)
  have hrun := eval_call_from_state Subexp.BlockCopyProgram.program
    threeRegisters blockCopyPorts d threeRegisters.injective blockCopyPorts.injective
    (b := localOut) (by simpa only [hin] using htrace)
  have hlocalOut : localOut =
      {localIn with «stacks» := Function.update (Function.update localIn.stacks 1
        (Subexp.BlockCopyProgram.copies D (d.stacks 104) ++ d.stacks 277)) 3 []} := by
    apply state_ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [localOut, localIn, Subexp.BlockCopyProgram.data,
        Subexp.BlockCopyProgram.initialState]
  have hagree := embedState_project threeRegisters blockCopyPorts d
    threeRegisters.injective blockCopyPorts.injective
  rw [hin] at hagree
  have hfinal : embedState threeRegisters blockCopyPorts d localOut =
      (⟨d.regs, Function.update (Function.update d.stacks 277
        (Subexp.BlockCopyProgram.copies D (d.stacks 104) ++ d.stacks 277)) 279 []⟩ : Data) := by
    apply state_ext
    · change Function.extend threeRegisters localOut.regs d.regs = d.regs
      change Function.extend threeRegisters localIn.regs d.regs = d.regs
      exact congrArg StructuredProgram.State.regs hagree
    · have hstack := congrArg StructuredProgram.State.stacks hlocalOut
      have hsame := congrArg StructuredProgram.State.stacks hagree
      change Function.extend blockCopyPorts localIn.stacks d.stacks = d.stacks at hsame
      change Function.extend blockCopyPorts localOut.stacks d.stacks = _
      rw [hstack, ProgramLinking.extend_update blockCopyPorts.injective,
        ProgramLinking.extend_update blockCopyPorts.injective, hsame]
      rfl
  simpa only [hfinal] using hrun

abbrev jetWidthState (d : Data) (D : ℕ) : Data :=
  ⟨(threeReset (afterCopy d 243 279 0 1)).regs,
    Function.update d.stacks 277
      (Subexp.BlockCopyProgram.copies D (d.stacks 104) ++ d.stacks 277)⟩

theorem buildJetWidth_run (d : Data) (D : ℕ)
    (hd : d.stacks 243 = List.replicate D true)
    (ht : d.stacks 278 = []) (hc : d.stacks 279 = []) (hu : d.stacks 318 = []) :
    Eval buildJetWidth (D * (7 * (d.stacks 104).length + 14) + 11)
      d (jetWidthState d D) := by
  have hcopy := copy_run d 243 279 (by decide) (by decide) (by decide) hu
  let copied := afterCopy d 243 279 0 1
  let ready := threeReset copied
  have hreset := resetThree_run copied
  have hregs : ∀ i : Fin 3, ready.regs (threeRegisters i) = false := by
    intro i
    fin_cases i <;> simp [ready, threeRegisters]
  have hcounter : ready.stacks 279 = List.replicate D true := by
    simp [ready, copied, afterCopy, StackRoutines.copyStacks, hd, hc]
  have htmp : ready.stacks 278 = [] := by
    simpa [ready, copied, threeReset, afterCopy, StackRoutines.copyStacks] using ht
  have hrun := blockCopy_run ready D hregs hcounter htmp
  have hfinal : (⟨ready.regs, Function.update (Function.update ready.stacks 277
      (Subexp.BlockCopyProgram.copies D (ready.stacks 104) ++ ready.stacks 277)) 279 []⟩ : Data) =
      jetWidthState d D := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi : i = 279
      · subst i; simp [ hc]
      · by_cases hj : i = 277
        · subst i
          simp [ ready, copied, afterCopy,
            StackRoutines.copyStacks]
        · simp [ ready, copied, afterCopy,
            StackRoutines.copyStacks, hi, hj]
  rw [hfinal] at hrun
  have h := hcopy.seq (hreset.seq hrun)
  have h104 : ready.stacks 104 = d.stacks 104 := by
    simp [ready, copied, afterCopy, StackRoutines.copyStacks]
  convert h using 1
  · rfl
  · rw [h104, hd]
    simp only [List.length_replicate]
    ring

def zerosFromWidth (dst : Fin 320) : Code :=
  .seq (copy 202 278) (.call (zeroFillProgram 278 dst (0 : Fin 16) 1))

abbrev zeroWidthState (d : Data) (dst : Fin 320) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update d.stacks dst (List.replicate (4 * (d.stacks 202).length) false)⟩

theorem zerosFromWidth_run (d : Data) (dst : Fin 320)
    (hdst : dst ≠ 278) (hc : d.stacks 278 = [])
    (hz : d.stacks dst = []) (ht : d.stacks 318 = []) :
    Eval (zerosFromWidth dst) (14 * (d.stacks 202).length + 8) d
      (zeroWidthState d dst) := by
  have hcopy := copy_run d 202 278 (by decide) (by decide) (by decide) ht
  let copied := afterCopy d 202 278 0 1
  have hzfill := zeroFill_eval 278 dst (0 : Fin 16) 1 hdst.symm (by decide) copied
  have hlen : (copied.stacks 278).length = (d.stacks 202).length := by
    simp [copied, afterCopy, StackRoutines.copyStacks, hc]
  have hfinal : (⟨readRegs copied.regs 0 1 none,
      zeroFillStacks 278 dst (copied.stacks 278).length copied.stacks⟩ : Data) =
      zeroWidthState d dst := by
    apply state_ext
    · simp [copied, afterCopy, StackRoutines.readRegs_reset]
    · funext i
      by_cases hi : i = dst
      · subst i
        simp [ zeroFillStacks, copied, afterCopy,
          StackRoutines.copyStacks, hz, hdst, hc]
      · by_cases hj : i = 278
        · subst i
          simp [ zeroFillStacks, copied, afterCopy,
            StackRoutines.copyStacks, hi, hc]
        · simp [ zeroFillStacks, copied, afterCopy,
            StackRoutines.copyStacks, hi, hj]
  rw [hfinal] at hzfill
  have h := hcopy.seq hzfill
  simpa only [zerosFromWidth, hlen,
    show 7 * (d.stacks 202).length + 5 + (7 * (d.stacks 202).length + 3) =
      14 * (d.stacks 202).length + 8 by omega] using h

def initializationBudget (B D nodeBits jetBits : ℕ) : ℕ :=
  28 * B + SubexpFactorCountSetup.countBudget D + D * (28 * B + 14) +
    14 * nodeBits + 7 * jetBits + 43

/-- The exact stack result of initialization. All words here are outputs of
the concrete zero-fill, unary-count, repeated-copy, and preserving-copy calls. -/
abbrev initializedStacks (d : Data) (D : ℕ) (exponent : List Bool) : Fin 320 → List Bool :=
  let zero := List.replicate (4 * (d.stacks 202).length) false
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update d.stacks
      104 zero) 261 zero) 268 exponent)
      277 (Subexp.BlockCopyProgram.copies D zero))
      214 (d.stacks 256)) 257 (d.stacks 256)) 266 (d.stacks 265)

theorem initializeOuter_run (d : Data) (D : ℕ)
    (hd : d.stacks 243 = List.replicate D true)
    (hclean : ∀ j ∈ ([104,261,268,277,278,279,316,317,318,214,257,266] : List (Fin 320)),
      d.stacks j = []) :
    ∃ n ≤ initializationBudget (d.stacks 202).length D
        (d.stacks 256).length (d.stacks 265).length,
      ∃ (rf : Fin 16 → Bool) (exponent : List Bool),
        Eval initializeOuter n d ⟨rf, initializedStacks d D exponent⟩ ∧
        BinaryArithmetic.toNat exponent = D ∧ exponent.length ≤ D := by
  have hz (j : Fin 320) (h : j ∈ ([104,261,268,277,278,279,316,317,318,214,257,266] :
      List (Fin 320))) : d.stacks j = [] := hclean j h
  have h1 := zerosFromWidth_run d 104 (by decide) (hz 278 (by simp))
    (hz 104 (by simp)) (hz 318 (by simp))
  let d1 := zeroWidthState d 104
  have h2 := zerosFromWidth_run d1 261 (by decide)
    (by simpa [d1, zeroWidthState] using hz 278 (by simp))
    (by simpa [d1, zeroWidthState] using hz 261 (by simp))
    (by simpa [d1, zeroWidthState] using hz 318 (by simp))
  let d2 := zeroWidthState d1 261
  obtain ⟨nc, hnc, rc, exponent, hc, he, hl⟩ := countDimension_run d2
    (by simpa [d2, d1, zeroWidthState] using hz 268 (by simp))
    (by simpa [d2, d1, zeroWidthState] using hz 316 (by simp))
    (by simpa [d2, d1, zeroWidthState] using hz 317 (by simp))
  let d3 : Data := ⟨rc, Function.update d2.stacks 268 exponent⟩
  have h3 := buildJetWidth_run d3 D
    (by simpa [d3, d2, d1, zeroWidthState] using hd)
    (by simpa [d3, d2, d1, zeroWidthState] using hz 278 (by simp))
    (by simpa [d3, d2, d1, zeroWidthState] using hz 279 (by simp))
    (by simpa [d3, d2, d1, zeroWidthState] using hz 318 (by simp))
  let d4 := jetWidthState d3 D
  have h4 := copy_run d4 256 214 (by decide) (by decide) (by decide)
    (by simpa [d4, jetWidthState, d3, d2, d1, zeroWidthState] using hz 318 (by simp))
  let d5 := afterCopy d4 256 214 0 1
  have h5 := copy_run d5 256 257 (by decide) (by decide) (by decide)
    (by simpa [d5, afterCopy, StackRoutines.copyStacks, d4, jetWidthState,
      d3, d2, d1, zeroWidthState] using hz 318 (by simp))
  let d6 := afterCopy d5 256 257 0 1
  have h6 := copy_run d6 265 266 (by decide) (by decide) (by decide)
    (by simpa [d6, d5, afterCopy, StackRoutines.copyStacks, d4, jetWidthState,
      d3, d2, d1, zeroWidthState] using hz 318 (by simp))
  have hfinal : (afterCopy d6 265 266 0 1).stacks = initializedStacks d D exponent := by
    simp [d6, d5, afterCopy, StackRoutines.copyStacks, d4,
      d3, d2, d1, initializedStacks,
      hz 214 (by simp), hz 257 (by simp), hz 266 (by simp), hz 277 (by simp)]
  have hexp : BinaryArithmetic.toNat exponent = D := by
    simpa [d2, d1, zeroWidthState, hd] using he
  have hlength : exponent.length ≤ D := by
    simpa [d2, d1, zeroWidthState, hd] using hl
  have hcBound : nc ≤ SubexpFactorCountSetup.countBudget D + 1 := by
    simpa [d2, d1, zeroWidthState, hd] using hnc
  have hassoc {a b c : Code} {n : ℕ} {s t : Data}
      (h : Eval (.seq (.seq a b) c) n s t) : Eval (.seq a (.seq b c)) n s t := by
    cases h with
    | seq hab hc =>
      cases hab with
      | seq ha hb => simpa only [Nat.add_assoc] using ha.seq (hb.seq hc)
  have hrun' := hassoc (h1.seq (hassoc (h2.seq (hc.seq (h3.seq (h4.seq (h5.seq h6)))))))
  have hresult : afterCopy d6 265 266 0 1 =
      (⟨(afterCopy d6 265 266 0 1).regs, initializedStacks d D exponent⟩ : Data) :=
    state_ext rfl hfinal
  change Eval initializeOuter _ d _ at hrun'
  rw [hresult] at hrun'
  refine ⟨_, ?_, _, exponent, hrun', hexp, hlength⟩
  simp [d6, d5, afterCopy, StackRoutines.copyStacks, d4,
    d3, d2, d1, initializationBudget]
  nlinarith

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
