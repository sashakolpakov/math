import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialConstructor

namespace OAI.Algorithms

/-! Width-generic padded constant and linear polynomial constructors. The
physical instruction table is unchanged; its zero-cell width and polynomial
length are runtime tapes. All output construction and cleanup is charged. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
namespace Counter
open SubexponentialSAT.SubexpLinearFactorProgram
private theorem copies_zero (n W : ℕ) :
    SubexponentialSAT.Subexp.BlockCopyProgram.copies n (List.replicate W false) =
      List.replicate (n * W) false := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [SubexponentialSAT.Subexp.BlockCopyProgram.copies_succ, ih, ← List.replicate_add]
      congr 1
      ring
def paddedBits (W : ℕ) (low high : List Bool) : ℕ → List Bool
  | 0 => []
  | 1 => low
  | n + 2 => low ++ high ++ List.replicate (n * W) false
def counterResult (d : Data) (D W : ℕ) (low high : List Bool)
    (regs : Fin 16 → Bool) : Data :=
  ⟨regs, Function.update (Function.update d.stacks 108 []) 102 (paddedBits W low high D)⟩

theorem fromCounter_eval (d : Data) (D W : ℕ) (low high : List Bool)
    (hlow : d.stacks 100 = low) (hhigh : d.stacks 101 = high)
    (hlength : low.length = W) (hhlength : high.length = W)
    (hcount : d.stacks 108 = List.replicate D true)
    (hcell : d.stacks 104 = List.replicate W false)
    (hout : d.stacks 102 = []) (htmp : d.stacks 107 = []) :
    ∃ n ≤ 100 * (D + 1) * (W + 1), ∃ regs,
      Eval fromCounter n d (counterResult d D W low high regs) := by
  cases D with
  | zero =>
      have hp := popDimension_eval d
      have ht : (dimensionPopped d).regs 1 = false := by
        simp [ hcount, readRegs]
      have hh := hp.seq (Eval.ite_false (yes := .seq popDimension (.ite 1 longCase copyLow))
        ht (Eval.base (StructuredProgram.Eval.skip (dimensionPopped d))))
      have he : dimensionPopped d = counterResult d 0 W low high (dimensionPopped d).regs := by
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
          have he : last = counterResult d 1 W low high last.regs := by
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
                | (simp [d₂, d₁, hlow, hlength]; omega)
            rw [he] at hc'
            exact hc'
      | succ n =>
          let d₁ := dimensionPopped d
          let d₂ := dimensionPopped d₁
          let dr := registersReset d₂
          let dz := SubexpJetInitProgram.repeatOut dr n (List.replicate W false) []
          let dh := afterCopy dz 101 102 0 1
          let dl := afterCopy dh 100 102 0 1
          have hp₁ := popDimension_eval d
          have hp₂ := popDimension_eval d₁
          have ht₁ : d₁.regs 1 = true := by simp [d₁, hcount, readRegs]
          have ht₂ : d₂.regs 1 = true := by simp [d₂, d₁, hcount, readRegs]
          have hr := resetRegisters_eval d₂
          have hz := SubexpJetInitProgram.repeatCell_eval dr n (List.replicate W false) []
            (by simp [dr]) (by simp [dr])
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
          have he : dl = counterResult d (n + 2) W low high dl.regs := by
            refine state_ext rfl ?_
            funext i
            by_cases hi : i = 102
            · subst i
              simp [dl, dh, dz, afterCopy, StackRoutines.copyStacks,
                SubexpJetInitProgram.repeatOut, dr, d₂, d₁,
                counterResult, paddedBits, hlow, hhigh, copies_zero,
                List.append_assoc]
            · by_cases hj : i = 108
              · subst i
                simp [dl, dh, dz, afterCopy, StackRoutines.copyStacks,
                  SubexpJetInitProgram.repeatOut, counterResult]
              · simp [dl, dh, dz, afterCopy, StackRoutines.copyStacks,
                  SubexpJetInitProgram.repeatOut, dr, d₂, d₁,
                  counterResult, hi, hj]
          let cost := n * (7 * W + 7) + 7 * high.length + 7 * low.length + 20
          refine ⟨cost, ?_, dl.regs, ?_⟩
          · dsimp [cost]
            rw [hlength, hhlength]
            nlinarith only [Nat.zero_le n, Nat.zero_le W]
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
theorem paddedBits_length (D W : ℕ) (low high : List Bool)
    (hlow : low.length = W) (hhigh : high.length = W) :
    (paddedBits W low high D).length = D * W := by
  cases D with
  | zero => simp [paddedBits]
  | succ D =>
      cases D with
      | zero => simpa [paddedBits] using hlow
      | succ n => simp [paddedBits, hlow, hhigh]; ring

end Counter
namespace Call
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpLinearFactorCall
theorem command_run (s : Store) (D W : ℕ) (low high : List Bool)
    (hlow : s 100 = low) (hhigh : s 101 = high)
    (hllen : low.length = W) (hhlen : high.length = W)
    (hD : s 108 = List.replicate D true)
    (hzero : s 104 = List.replicate W false)
    (hout : s 102 = []) (htmp : s 107 = []) :
    ExecutesIn command (101 * (D + 1) * (W + 1)) s
      (Function.update (Function.update s 108 []) 102
        (Counter.paddedBits W low high D)) := by
  intro regs
  let d : Data := ⟨regs, s⟩
  let nativeData := projectState id ports d
  obtain ⟨n, hn, rf, he⟩ := Counter.fromCounter_eval nativeData D W low high
    hlow hhigh hllen hhlen hD hzero hout htmp
  have hc := eval_liftCommand_from_state SubexpLinearFactorProgram.fromCounter
    108 102 id ports d Function.injective_id ports.injective he
  let last := embedState id ports d
    (Counter.counterResult nativeData D W low high rf)
  have hext : Function.extend ports (s ∘ ports) s = s := by
    have h := congrArg StructuredProgram.State.stacks
      (embedState_project id ports d Function.injective_id ports.injective)
    exact h
  have hs : last.stacks = Function.update (Function.update s 108 []) 102
      (Counter.paddedBits W low high D) := by
    change Function.extend ports
      (Function.update (Function.update (s ∘ ports) 108 []) 102
        (Counter.paddedBits W low high D)) s = _
    rw [ProgramLinking.extend_update ports.injective,
      ProgramLinking.extend_update ports.injective, hext]
    rfl
  have hlast : last =
      (⟨last.regs, Function.update (Function.update s 108 []) 102
        (Counter.paddedBits W low high D)⟩ : Data) := by
    exact SubexpScanPrimitives.state_ext rfl hs
  refine ⟨n + 1, last.regs, ?_, ?_⟩
  · have hp : 0 < (D + 1) * (W + 1) := Nat.mul_pos (by omega) (by omega)
    nlinarith
  · change Eval command (n + 1) d last at hc
    rw [hlast] at hc
    exact hc

end Call
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpPolynomialConstructor
theorem constructAtInputs_run (s : Store) (dst : Fin 256) (hdst : 205 ≤ dst.val)
    (hdtmp : dst ≠ 245) (D W : ℕ) (low high : List Bool)
    (hlow : s 100 = low) (hhigh : s 101 = high)
    (hllen : low.length = W) (hhlen : high.length = W)
    (hD : s 243 = List.replicate D true)
    (hzero : s 104 = List.replicate W false)
    (h102 : s 102 = []) (h107 : s 107 = []) (h108 : s 108 = [])
    (h120 : s 120 = []) (h245 : s 245 = []) (hout : s dst = []) :
    ExecutesIn (constructAtInputs dst) (150 * (D + 1) * (W + 1)) s
      (Function.update (Function.update (Function.update s 100 []) 101 []) dst
        (Counter.paddedBits W low high D)) := by
  have hsmall : ∀ i : Fin 256, i.val < 205 → i ≠ dst := by
    intro i hi he
    subst i
    omega
  have h100 := hsmall 100 (by decide)
  have h101 := hsmall 101 (by decide)
  have h102d := hsmall 102 (by decide)
  let bits := Counter.paddedBits W low high D
  let s₁ := Function.update s 108 (List.replicate D true)
  let s₂ := Function.update s 102 bits
  let s₃ := Function.update s₂ 100 []
  let s₄ := Function.update s₃ 101 []
  have h₁ : ExecutesIn (copy 243 108) (7 * D + 5) s s₁ := by
    simpa [s₁, hD, h108] using copy_run 243 108 s
      (by decide) (by decide) (by decide) h120
  have he₂ : Function.update (Function.update s₁ 108 []) 102 bits = s₂ := by
    funext j
    by_cases hj : j = 108 <;> simp [s₁, s₂, Function.update_apply, h108, hj]
  have h₂ : ExecutesIn SubexpLinearFactorCall.command
      (101 * (D + 1) * (W + 1)) s₁ s₂ := by
    have h := Call.command_run s₁ D W low high
      (by simp [s₁, hlow]) (by simp [s₁, hhigh]) hllen hhlen
      (by simp [s₁]) (by simp [s₁, hzero]) (by simp [s₁, h102]) (by simp [s₁, h107])
    rw [he₂] at h
    exact h
  have h₃ : ExecutesIn (clear 100) (2 * W + 3) s₂ s₃ := by
    simpa [s₂, s₃, hlow, hllen, ← Nat.mul_assoc] using clear_run 100 s₂
  have h₄ : ExecutesIn (clear 101) (2 * W + 3) s₃ s₄ := by
    simpa [s₂, s₃, s₄, hhigh, hhlen, ← Nat.mul_assoc] using clear_run 101 s₃
  have he₅ : Function.update (Function.update s₄ 102 []) dst (s₄ 102) =
      Function.update (Function.update (Function.update s 100 []) 101 []) dst bits := by
    funext j
    by_cases hj : j = 102 <;>
      simp [s₂, s₃, s₄, Function.update_apply, hj, h102, h102d ]
  have hbits : bits.length = D * W :=
    Counter.paddedBits_length D W low high hllen hhlen
  have h₅ : ExecutesIn (move 102 dst) (6 * D * W + 6) s₄
      (Function.update (Function.update (Function.update s 100 []) 101 []) dst bits) := by
    have h := move_run s₄ 102 dst (by decide) hdtmp h102d
      (by simp [s₄, s₃, s₂, h245])
      (by simp [s₄, s₃, s₂, Ne.symm h100, Ne.symm h101, Ne.symm h102d, hout])
    rw [he₅] at h
    convert h using 1
    simp [s₄, s₃, s₂, hbits]
    ring
  have h := h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))
  apply h.mono
  ring_nf
  omega

theorem construct_run (s : Store) (low high dst : Fin 256)
    (hl100 : low ≠ 100) (hl120 : low ≠ 120)
    (hh100 : high ≠ 100) (hh101 : high ≠ 101) (hh120 : high ≠ 120)
    (hdst : 205 ≤ dst.val) (hdtmp : dst ≠ 245) (D W : ℕ)
    (hllen : (s low).length = W) (hhlen : (s high).length = W)
    (hD : s 243 = List.replicate D true)
    (hzero : s 104 = List.replicate W false)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h107 : s 107 = []) (h108 : s 108 = []) (h120 : s 120 = [])
    (h245 : s 245 = []) (hout : s dst = []) :
    ExecutesIn (construct low high dst) (220 * (D + 1) * (W + 1)) s
      (Function.update s dst (Counter.paddedBits W (s low) (s high) D)) := by
  let s₁ := Function.update s 100 (s low)
  let s₂ := Function.update s₁ 101 (s high)
  have hd100 : dst ≠ 100 := by intro h; subst dst; norm_num [Fin.coe_ofNat_eq_mod] at hdst
  have hd101 : dst ≠ 101 := by intro h; subst dst; norm_num [Fin.coe_ofNat_eq_mod] at hdst
  have h₁ : ExecutesIn (copy low 100) (7 * (s low).length + 5) s s₁ := by
    simpa [s₁, h100] using copy_run low 100 s hl100 hl120 (by decide) h120
  have h₂ : ExecutesIn (copy high 101) (7 * (s high).length + 5) s₁ s₂ := by
    simpa [s₁, s₂, hh100, h101] using copy_run high 101 s₁ hh101 hh120
      (by decide) (by simp [s₁, h120])
  have h₃ := constructAtInputs_run s₂ dst hdst hdtmp D W (s low) (s high)
    (by simp [s₂, s₁]) (by simp [s₂]) hllen hhlen
    (by simp [s₂, s₁, hD]) (by simp [s₂, s₁, hzero])
    (by simp [s₂, s₁, h102]) (by simp [s₂, s₁, h107])
    (by simp [s₂, s₁, h108]) (by simp [s₂, s₁, h120])
    (by simp [s₂, s₁, h245]) (by simp [s₂, s₁, hd100, hd101, hout])
  have he : Function.update (Function.update (Function.update s₂ 100 []) 101 []) dst
      (Counter.paddedBits W (s low) (s high) D) =
      Function.update s dst (Counter.paddedBits W (s low) (s high) D) := by
    funext j
    by_cases h100' : j = 100 <;> by_cases h101' : j = 101 <;>
      simp [s₂, s₁, Function.update_apply, h100, h101, h100', h101']
  rw [he] at h₃
  apply (h₁.seq (h₂.seq h₃)).mono
  rw [hllen, hhlen]
  ring_nf
  omega

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

end OAI.Algorithms
