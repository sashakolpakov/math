import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchProgram

namespace OAI.Algorithms

/-! The first-success callback retains an unshifted copy, invokes the actual
coefficient checker, and clears the shifted work vector before returning. -/

namespace SubexponentialSAT.Subexp.CoefficientSearchProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod
attribute [local simp] MatrixProgramSupport.words

open BitProgram StructuredCalls SubexpScanPrimitives MatrixWordEncoding

variable (p : ℕ) [Fact p.Prime]

def cleared (d : Data) (src : Fin 32) : Data :=
  ⟨readRegs d.regs 11 12 none, Function.update d.stacks src []⟩

theorem clear_eval (d : Data) (src : Fin 32) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared d src) := by
  simpa only [clear, cleared, StackRoutines.clearStacks] using
    TupleProgram.clear_eval src (11 : Fin 14) 12 d

private theorem candidate_entry (A R : ℕ) (v : Fin R → ZMod p)
    (regs : Fin 8 → Bool) (g neg ok : Bool) (selected tail alphabet : List Bool) :
    let xs := List.ofFn v
    let bits := CoefficientSearchSemantics.encode p v
    let d₀ := wide (blank p R regs g neg ok) false true false selected tail bits.reverse
      alphabet (List.replicate A true)
    let d₁ := cleared d₀ 21
    let d₂ := afterTransfer d₁ 23 12 11 12
    let d₃ := afterCopy d₂ 12 21 11 12
    afterCopy d₃ 31 17 11 12 = wide
      (CoefficientCheckerProgram.ready p regs g neg ok xs (List.replicate A true) [])
      false false false bits tail [] alphabet (List.replicate A true) := by
  have hb := encode_eq_valueWords p v
  dsimp only
  apply state_ext
  · funext j
    fin_cases j <;> simp [cleared,afterCopy,afterTransfer,readRegs,wide,blank,
      CoefficientCheckerProgram.ready,CoefficientCheckerProgram.wide,
      CoefficientCheckerProgram.lowData,MatrixScalarProgram.state]
  · funext j
    fin_cases j <;> simp [cleared,afterCopy,afterTransfer,StackRoutines.copyStacks,
      StackRoutines.transferStacks,wide,blank,CoefficientCheckerProgram.ready,
      CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
      MatrixScalarProgram.state,MatrixScalarProgram.scalarStacks,
      CoefficientPascalProgram.valueWords,hb]

/-- A callback invocation performs all copies, the arithmetic checker, and
cleanup with no supplied execution premise. -/
theorem callback_eval (A R : ℕ) (v : Fin R → ZMod p) (regs : Fin 8 → Bool)
    (g neg ok : Bool) (selected tail alphabet : List Bool)
    (hselected : selected.length ≤ R * (2 * width p + 1)) :
    ∃ n ≤ callbackBudget A R (width p), ∃ regs',
      Eval callback n
        (wide (blank p R regs g neg ok) false true false selected tail
          (CoefficientSearchSemantics.encode p v).reverse alphabet (List.replicate A true))
        (wide (blank p R regs' false
          (CoefficientCheckerSemantics.advanceParity R
            (CoefficientCheckerSemantics.advanceParity A false))
          (CoefficientSearchSemantics.valueTest p A v))
          false true (CoefficientSearchSemantics.valueTest p A v)
          (CoefficientSearchSemantics.encode p v) tail [] alphabet (List.replicate A true)) := by
  let xs := List.ofFn v
  let bits := CoefficientSearchSemantics.encode p v
  have hx : xs.length = R := List.length_ofFn
  have hlen : bits.length = R * (2 * width p + 1) := CoefficientSearchSemantics.encode_length p v
  let d₀ := wide (blank p R regs g neg ok) false true false selected tail bits.reverse
    alphabet (List.replicate A true)
  let d₁ := cleared d₀ 21
  let d₂ := afterTransfer d₁ 23 12 11 12
  let d₃ := afterCopy d₂ 12 21 11 12
  let d₄ := afterCopy d₃ 31 17 11 12
  have e₁ : Eval (clear 21) (2 * selected.length + 3) d₀ d₁ := by
    have hL : (d₀.stacks 21).length = selected.length := by simp [d₀,wide]
    simpa only [hL] using clear_eval d₀ 21
  have e₂ : Eval (transfer 23 12) (3 * bits.length + 3) d₁ d₂ := by
    have hL : (d₁.stacks 23).length = bits.length := by simp [d₁,cleared,d₀,wide]
    simpa only [transfer,hL] using
      SubexpScanPrimitives.transfer_eval d₁ 23 12 11 12 (by decide) (by decide)
  have e₃ : Eval (copy 12 21) (7 * bits.length + 5) d₂ d₃ := by
    have he := SubexpScanPrimitives.copy_eval d₂ 12 21 24 11 12
      (by decide) (by decide) (by decide) (by decide)
      (by simp [d₂,afterTransfer,StackRoutines.transferStacks,d₁,cleared,d₀,wide])
    have hL : (d₂.stacks 12).length = bits.length := by
      simp [d₂,afterTransfer,StackRoutines.transferStacks,d₁,cleared,d₀,wide,
        blank,CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
        MatrixScalarProgram.state,MatrixScalarProgram.scalarStacks,CoefficientPascalProgram.valueWords]
    simpa only [copy,hL] using he
  have e₄ : Eval (copy 31 17) (7 * A + 5) d₃ d₄ := by
    have he := SubexpScanPrimitives.copy_eval d₃ 31 17 24 11 12
      (by decide) (by decide) (by decide) (by decide)
      (by simp [d₃,afterCopy,StackRoutines.copyStacks,d₂,afterTransfer,
        StackRoutines.transferStacks,d₁,cleared,d₀,wide])
    have hL : (d₃.stacks 31).length = A := by
      simp [d₃,afterCopy,StackRoutines.copyStacks,d₂,afterTransfer,
        StackRoutines.transferStacks,d₁,cleared,d₀,wide]
    simpa only [copy,hL] using he
  have hentry : d₄ = wide
      (CoefficientCheckerProgram.ready p regs g neg ok xs (List.replicate A true) [])
      false false false bits tail [] alphabet (List.replicate A true) := by
    exact candidate_entry p A R v regs g neg ok selected tail alphabet
  obtain ⟨nc,hc,rc,ec⟩ := checker_eval p A xs regs g neg ok false false false bits tail [] alphabet
  rw [← hentry] at ec
  let d₅ := wide (CoefficientCheckerProgram.outputState p A xs rc)
    false false false bits tail [] alphabet (List.replicate A true)
  let d₆ := (StructuredProgram.Atom.bor 13 10 10).eval d₅
  have e₆ : Eval (.base (.atom (.bor 13 10 10))) 1 d₅ d₆ := .base (.atom _ _)
  let d₇ := cleared d₆ 12
  have e₇ : Eval (clear 12) (2 * bits.length + 3) d₆ d₇ := by
    have hL : (d₆.stacks 12).length = bits.length := by
      simp [d₆,d₅,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        wide,CoefficientCheckerProgram.outputState,CoefficientCheckerProgram.ready,
        CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
        MatrixScalarProgram.state,MatrixScalarProgram.scalarStacks,
        CoefficientPascalProgram.valueWords_length,hx,hlen]
    simpa only [hL] using clear_eval d₆ 12
  let d₈ := (StructuredProgram.Atom.set 12 true).eval d₇
  have e₈ : Eval (.base (.atom (.set 12 true))) 1 d₇ d₈ := .base (.atom _ _)
  have htest : CoefficientCheckerProgram.accepted p A xs = CoefficientSearchSemantics.valueTest p A v := by
    simp only [CoefficientCheckerProgram.accepted,CoefficientSearchSemantics.valueTest,hx,xs]
  have hfinal : d₈ = wide (blank p R rc false
      (CoefficientCheckerSemantics.advanceParity R
        (CoefficientCheckerSemantics.advanceParity A false))
      (CoefficientSearchSemantics.valueTest p A v)) false true
      (CoefficientSearchSemantics.valueTest p A v) bits tail [] alphabet (List.replicate A true) := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [d₈,d₇,d₆,d₅,cleared,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr, readRegs, wide, blank,
        CoefficientCheckerProgram.outputState,CoefficientCheckerProgram.ready,
        CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
        MatrixScalarProgram.state,hx,htest]
    · funext j
      fin_cases j <;> simp [d₈,d₇,d₆,d₅,cleared,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr, wide, blank,
        CoefficientCheckerProgram.outputState,CoefficientCheckerProgram.ready,
        CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
        MatrixScalarProgram.state,MatrixScalarProgram.scalarStacks,
        CoefficientPascalProgram.valueWords,hx]
  have he := e₁.seq (e₂.seq (e₃.seq (e₄.seq (ec.seq (e₆.seq (e₇.seq e₈))))))
  rw [hfinal] at he
  refine ⟨(2 * selected.length + 3) + ((3 * bits.length + 3) + ((7 * bits.length + 5) +
    ((7 * A + 5) + (nc + (1 + ((2 * bits.length + 3) + 1)))))), ?_, rc, he⟩
  simp only [hx] at hc
  dsimp [callbackBudget]
  omega

end SubexponentialSAT.Subexp.CoefficientSearchProgram

end OAI.Algorithms
