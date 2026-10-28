import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpJetInitProgram

namespace OAI.Algorithms

/-! Runtime construction of a padded linear polynomial. The low and high
coefficient cells occupy stacks 100 and 101. The unary dimension is on 109,
the base-word width is on 10, and the output array is on 102. -/

namespace SubexponentialSAT.SubexpLinearFactorProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 128
abbrev Code := Cmd 16 128

def initializeCell : Code :=
  .seq SubexpJetInitProgram.copyWidth SubexpJetInitProgram.zeroCell

def copyLow : Code := .call (StackRoutines.copyProgram 100 102 107 0 1)
def copyHigh : Code := .call (StackRoutines.copyProgram 101 102 107 0 1)
def popDimension : Code := .base (.atom (.pop 108 0 1))

def resetRegisters : Code :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 false))) (.base (.atom (.set 2 false))))

def longCase : Code :=
  .seq resetRegisters (.seq SubexpJetInitProgram.repeatCell (.seq copyHigh copyLow))

def fromCounter : Code :=
  .seq popDimension
    (.ite 1 (.seq popDimension (.ite 1 longCase copyLow)) (.base .skip))

def command : Code :=
  .seq initializeCell (.seq SubexpJetInitProgram.copyDimension fromCounter)

def program := compiled command 109 102

def paddedBits (B : ℕ) (low high : List Bool) : ℕ → List Bool
  | 0 => []
  | 1 => low
  | n + 2 => low ++ high ++ List.replicate (n * (4 * B)) false

abbrev cellInitialized (d : Data) (B : ℕ) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update d.stacks 104 (List.replicate (4 * B) false)⟩

theorem initializeCell_eval (d : Data) (B : ℕ)
    (hB : (d.stacks 10).length = B)
    (h104 : d.stacks 104 = []) (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) :
    Eval initializeCell (14 * B + 8) d (cellInitialized d B) := by
  let mid := afterCopy d 10 106 0 1
  have h₁ := copy_eval d 10 106 107 0 1 (by decide) (by decide) (by decide) (by decide) h107
  have h₂ := zeroFill_eval 106 104 0 1 (by decide) (by decide) mid
  have hlen : (mid.stacks 106).length = B := by
    simp [mid, afterCopy, StackRoutines.copyStacks, h106, hB]
  have hout :
      (⟨readRegs mid.regs 0 1 none, zeroFillStacks 106 104 (mid.stacks 106).length mid.stacks⟩ : Data) =
        cellInitialized d B := by
    apply state_ext
    · simp [mid, afterCopy, StackRoutines.readRegs_reset]
    · funext i
      by_cases h1 : i = 104
      · subst i
        simp [zeroFillStacks, mid, afterCopy, StackRoutines.copyStacks, h104, h106, hB]
      · by_cases h2 : i = 106
        · subst i
          simp [zeroFillStacks, mid, afterCopy, StackRoutines.copyStacks, h106]
        · simp [zeroFillStacks, mid, afterCopy, StackRoutines.copyStacks, h1, h2]
  rw [hout] at h₂
  have h := Eval.seq h₁ h₂
  convert h using 1
  simp [initializeCell, SubexpJetInitProgram.copyWidth, SubexpJetInitProgram.zeroCell ]
  omega

abbrev registersReset (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false, d.stacks⟩

theorem resetRegisters_eval (d : Data) :
    Eval resetRegisters 3 d (registersReset d) := by
  have h₁ := Eval.base (StructuredProgram.Eval.atom (.set 0 false) d)
  have h₂ := Eval.base (StructuredProgram.Eval.atom (.set 1 false)
    ((StructuredProgram.Atom.set 0 false).eval d))
  have h₃ := Eval.base (StructuredProgram.Eval.atom (.set 2 false)
    ((StructuredProgram.Atom.set 1 false).eval ((StructuredProgram.Atom.set 0 false).eval d)))
  exact h₁.seq (h₂.seq h₃)

abbrev dimensionPopped (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks 108).head?, Function.update d.stacks 108 (d.stacks 108).tail⟩

theorem popDimension_eval (d : Data) :
    Eval popDimension 1 d (dimensionPopped d) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop 108 0 1) d)
  exact h

def counterResult (d : Data) (D B : ℕ) (low high : List Bool)
    (regs : Fin 16 → Bool) : Data :=
  ⟨regs, Function.update (Function.update d.stacks 108 []) 102 (paddedBits B low high D)⟩

theorem fromCounter_eval (d : Data) (D B : ℕ) (low high : List Bool)
    (hlow : d.stacks 100 = low) (hhigh : d.stacks 101 = high)
    (hlength : low.length = 4 * B) (hhlength : high.length = 4 * B)
    (hcount : d.stacks 108 = List.replicate D true)
    (hcell : d.stacks 104 = List.replicate (4 * B) false)
    (hout : d.stacks 102 = []) (htmp : d.stacks 107 = []) :
    ∃ n ≤ 100 * (D + 1) * (B + 1), ∃ regs,
      Eval fromCounter n d (counterResult d D B low high regs) := by
  cases D with
  | zero =>
      have hp := popDimension_eval d
      have ht : (dimensionPopped d).regs 1 = false := by
        simp [ hcount, readRegs]
      have hh := hp.seq (Eval.ite_false (yes := .seq popDimension (.ite 1 longCase copyLow))
        ht (Eval.base (StructuredProgram.Eval.skip (dimensionPopped d))))
      have he : dimensionPopped d = counterResult d 0 B low high (dimensionPopped d).regs := by
        refine state_ext rfl ?_
        funext i
        by_cases hi : i = 102
        · subst i; simp [ counterResult, paddedBits, hout]
        · simp [ counterResult, paddedBits, hi, hcount]
      have hc : Eval fromCounter 2 d (dimensionPopped d) := by
        simpa only [fromCounter] using hh
      rw [he] at hc
      exact ⟨2, by omega, _, hc⟩
  | succ D =>
      cases D with
      | zero =>
          let d₁ := dimensionPopped d
          let d₂ := dimensionPopped d₁
          have hp₁ := popDimension_eval d
          have hp₂ := popDimension_eval d₁
          have ht₁ : d₁.regs 1 = true := by simp [d₁, hcount, readRegs]
          have ht₂ : d₂.regs 1 = false := by simp [d₂, d₁, hcount, readRegs]
          have hc := copy_eval d₂ 100 102 107 0 1 (by decide) (by decide) (by decide) (by decide)
            (by simp [d₂, d₁, htmp])
          let last := afterCopy d₂ 100 102 0 1
          have hh := hp₁.seq (Eval.ite_true (no := .base .skip) ht₁
            (hp₂.seq (Eval.ite_false (yes := longCase) ht₂ hc)))
          have he : last = counterResult d 1 B low high last.regs := by
            refine state_ext rfl ?_
            funext i
            by_cases hi : i = 102
            · subst i
              simp [last, d₂, d₁, afterCopy, StackRoutines.copyStacks,
                counterResult, paddedBits, hlow, hout]
            · simp [last, d₂, d₁, afterCopy, StackRoutines.copyStacks,
                counterResult, paddedBits, hi, hcount]
          refine ⟨7 * low.length + 9, ?_, last.regs, ?_⟩
          · rw [hlength]
            omega
          · have hc' : Eval fromCounter (7 * low.length + 9) d last := by
              convert hh using 1
              all_goals first
                | rfl
                | (simp [ d₂, d₁, hlow,
                    hlength]; omega)
            rw [he] at hc'
            exact hc'
      | succ n =>
          let d₁ := dimensionPopped d
          let d₂ := dimensionPopped d₁
          let dr := registersReset d₂
          let dz := SubexpJetInitProgram.repeatOut dr n (List.replicate (4 * B) false) []
          let dh := afterCopy dz 101 102 0 1
          let dl := afterCopy dh 100 102 0 1
          have hp₁ := popDimension_eval d
          have hp₂ := popDimension_eval d₁
          have ht₁ : d₁.regs 1 = true := by simp [d₁, hcount, readRegs]
          have ht₂ : d₂.regs 1 = true := by simp [d₂, d₁, hcount, readRegs]
          have hr := resetRegisters_eval d₂
          have hz := SubexpJetInitProgram.repeatCell_eval dr n (List.replicate (4 * B) false) []
            (by simp [dr ]) (by simp [dr ])
            (by simp [dr ])
            (by simp [dr, d₂, d₁, hcell])
            (by simp [dr, d₂, d₁, hout])
            (by simp [dr, d₂, d₁, htmp])
            (by simp [dr, d₂, d₁, hcount, List.replicate_succ])
          have hh := copy_eval dz 101 102 107 0 1 (by decide) (by decide) (by decide) (by decide)
            (by simp [dz, SubexpJetInitProgram.repeatOut, dr,
              d₂, d₁, htmp])
          have hl := copy_eval dh 100 102 107 0 1 (by decide) (by decide) (by decide) (by decide)
            (by simp [dh, afterCopy, StackRoutines.copyStacks, dz, SubexpJetInitProgram.repeatOut,
              dr, d₂, d₁, htmp])
          have hfull := hp₁.seq (Eval.ite_true (no := .base .skip) ht₁
            (hp₂.seq (Eval.ite_true (no := copyLow) ht₂ (hr.seq (hz.seq (hh.seq hl))))))
          have he : dl = counterResult d (n + 2) B low high dl.regs := by
            refine state_ext rfl ?_
            funext i
            by_cases hi : i = 102
            · subst i
              simp [dl, dh, dz, afterCopy, StackRoutines.copyStacks,
                SubexpJetInitProgram.repeatOut, dr, d₂, d₁,
                counterResult, paddedBits, hlow, hhigh, SubexpJetInitProgram.copies_zeroCell,
                List.append_assoc]
            · by_cases hj : i = 108
              · subst i
                simp [dl, dh, dz, afterCopy, StackRoutines.copyStacks,
                  SubexpJetInitProgram.repeatOut, counterResult]
              · simp [dl, dh, dz, afterCopy, StackRoutines.copyStacks,
                  SubexpJetInitProgram.repeatOut, dr, d₂, d₁,
                  counterResult, hi, hj]
          let cost := n * (28 * B + 7) + 7 * high.length + 7 * low.length + 20
          refine ⟨cost, ?_, dl.regs, ?_⟩
          · dsimp [cost]
            rw [hlength, hhlength]
            nlinarith only [Nat.zero_le n, Nat.zero_le B]
          · have hc : Eval fromCounter cost d dl := by
              have hdz101 : dz.stacks 101 = high := by
                simp [dz, SubexpJetInitProgram.repeatOut, dr,
                  d₂, d₁, hhigh]
              have hdh100 : dh.stacks 100 = low := by
                simp [dh, afterCopy, StackRoutines.copyStacks, dz,
                  SubexpJetInitProgram.repeatOut, dr,
                  d₂, d₁, hlow]
              convert hfull using 1
              · rfl
              · rw [hdz101, hdh100]
                simp only [List.length_replicate]
                dsimp [cost]
                rw [hlength, hhlength]
                ring
            rw [he] at hc
            exact hc

abbrev result (d : Data) (D B : ℕ) (low high : List Bool) (regs : Fin 16 → Bool) : Data :=
  ⟨regs, Function.update (Function.update d.stacks 104 (List.replicate (4 * B) false))
    102 (paddedBits B low high D)⟩

/-- Every output bit is built by fixed primitive loops and copies. -/
theorem command_eval (d : Data) (D B : ℕ) (low high : List Bool)
    (hlow : d.stacks 100 = low) (hhigh : d.stacks 101 = high)
    (hlength : low.length = 4 * B) (hhlength : high.length = 4 * B)
    (hD : d.stacks 109 = List.replicate D true) (hB : (d.stacks 10).length = B)
    (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    ∃ n ≤ 200 * (D + 1) * (B + 1), ∃ regs,
      Eval command n d (result d D B low high regs) := by
  let d₁ := cellInitialized d B
  let d₂ := afterCopy d₁ 109 108 0 1
  have h₁ := initializeCell_eval d B hB h104 h106 h107
  have h₂ := copy_eval d₁ 109 108 107 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [d₁, h107])
  obtain ⟨n, hn, regs, h₃⟩ := fromCounter_eval d₂ D B low high
    (by simp [d₂, d₁, afterCopy, StackRoutines.copyStacks, hlow])
    (by simp [d₂, d₁, afterCopy, StackRoutines.copyStacks, hhigh])
    hlength hhlength
    (by simp [d₂, d₁, afterCopy, StackRoutines.copyStacks, hD, h108])
    (by simp [d₂, d₁, afterCopy, StackRoutines.copyStacks ])
    (by simp [d₂, d₁, afterCopy, StackRoutines.copyStacks, h102])
    (by simp [d₂, d₁, afterCopy, StackRoutines.copyStacks, h107])
  have he : counterResult d₂ D B low high regs = result d D B low high regs := by
    refine state_ext rfl ?_
    funext i
    by_cases hi : i = 108
    · subst i
      simp [counterResult, d₂, d₁, afterCopy, StackRoutines.copyStacks, h108]
    · simp [counterResult, d₂, d₁, afterCopy, StackRoutines.copyStacks, Function.update_apply, hi]
  refine ⟨14 * B + 8 + (7 * D + 5 + n), ?_, regs, ?_⟩
  · nlinarith
  · have hh := h₁.seq (h₂.seq h₃)
    simpa [command, SubexpJetInitProgram.copyDimension, d₁, cellInitialized, hD, he]
      using hh

theorem paddedBits_length (D B : ℕ) (low high : List Bool)
    (hlow : low.length = 4 * B) (hhigh : high.length = 4 * B) :
    (paddedBits B low high D).length = D * (4 * B) := by
  cases D with
  | zero => simp [paddedBits]
  | succ D =>
      cases D with
      | zero => simpa [paddedBits] using hlow
      | succ n => simp [paddedBits, hlow, hhigh]; ring

theorem program_runs (d : Data) (D B : ℕ) (low high : List Bool)
    (hlow : d.stacks 100 = low) (hhigh : d.stacks 101 = high)
    (hlength : low.length = 4 * B) (hhlength : high.length = 4 * B)
    (hD : d.stacks 109 = List.replicate D true) (hB : (d.stacks 10).length = B)
    (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    ∃ regs, RunsIn program (201 * (D + 1) * (B + 1))
      (d.withPC (some program.entry)) ((result d D B low high regs).withPC none) := by
  obtain ⟨n, hn, regs, hrun⟩ := command_eval d D B low high hlow hhigh hlength hhlength
    hD hB h102 h104 h106 h107 h108
  refine ⟨regs, n + 1, ?_, compiled_halt_trace hrun 109 102⟩
  have hpos : 0 < (D + 1) * (B + 1) := Nat.mul_pos (by omega) (by omega)
  nlinarith

theorem primitive_execution (d : Data) (D B : ℕ) (low high : List Bool)
    (hlow : d.stacks 100 = low) (hhigh : d.stacks 101 = high)
    (hlength : low.length = 4 * B) (hhlength : high.length = 4 * B)
    (hD : d.stacks 109 = List.replicate D true) (hB : (d.stacks 10).length = B)
    (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    ∃ regs, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (201 * (D + 1) * (B + 1)))
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program ((result d D B low high regs).withPC none)) := by
  obtain ⟨regs, hrun⟩ := program_runs d D B low high hlow hhigh hlength hhlength
    hD hB h102 h104 h106 h107 h108
  exact ⟨regs, BitProgram.primitive_execution program hrun⟩

end SubexponentialSAT.SubexpLinearFactorProgram

end OAI.Algorithms
