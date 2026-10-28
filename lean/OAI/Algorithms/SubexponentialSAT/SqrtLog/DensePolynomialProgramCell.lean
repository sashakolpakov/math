import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramAdd
import OAI.Algorithms.SubexponentialSAT.SubexpJetCellProgram

namespace OAI.Algorithms

/-! A native update of one arbitrary-degree ring coefficient in a persistent
flat polynomial array. Every scan, copy, and scalar addition is paid. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
open SubexponentialSAT.SubexpJetCellProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Coeff := DensePolynomialProgram.Coeff

def addCall : Code := .call
  (SubexponentialSAT.ProgramLinking.liftProgram DensePolynomialProgram.addProgram regPorts scalarPorts)

def addBudget (degree B : ℕ) : ℕ := 7000 * (2 * degree + 1) * (B + 1)^2 + 1

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hB : 0 < baseWidth p t)
    {degree : ℕ} (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)

include cache hB hadd in
theorem addCall_eval (d : Data) (a b : Coeff (baseWidth p t) degree)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p t)
    (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
      (DensePolynomialLoop.ready (d.regs ∘ regPorts) M.bits
        (RingProgram.flat a) (RingProgram.flat b) width [] frame).stacks i) :
    ∃ n ≤ addBudget degree (baseWidth p t), ∃ regs',
      Eval addCall n d
        (addOut d regs' (RingProgram.flat (ops.addRun a b).1)) := by
  obtain ⟨n, hn, regs', ht⟩ := DensePolynomialProgram.add_trace p t M cache hB
    (d.regs ∘ regPorts) ops hadd [a] [b] width frame hwidth
  have htrace : Trace DensePolynomialProgram.addProgram n
      ((DensePolynomialLoop.ready (d.regs ∘ regPorts) M.bits
        (RingProgram.flat a) (RingProgram.flat b) width [] frame).withPC
          (some DensePolynomialProgram.addProgram.entry))
      ((DensePolynomialLoop.ready regs' M.bits
        (RingProgram.flat (ops.addRun a b).1) [] width [] frame).withPC none) := by
    simpa [DensePolynomialProgram.encode, SubexpDensePolynomial.addProgram] using ht
  have hcost : n ≤ addBudget degree (baseWidth p t) := by
    simpa [addBudget, Nat.mul_comm degree 2] using hn
  let left := DensePolynomialLoop.ready (d.regs ∘ regPorts) M.bits
    (RingProgram.flat a) (RingProgram.flat b) width [] frame
  let right := DensePolynomialLoop.ready regs' M.bits
    (RingProgram.flat (ops.addRun a b).1) [] width [] frame
  have hl : embedState regPorts scalarPorts d left = d := by
    apply embedState_eq _ _ regPorts_injective scalarPorts_injective
    · intros; rfl
    · exact hsmall
    · intros; rfl
    · intros; rfl
  have hr : embedState regPorts scalarPorts d right =
      addOut d regs' (RingProgram.flat (ops.addRun a b).1) := by
    apply embedState_eq _ _ regPorts_injective scalarPorts_injective
    · intro i
      simp [addOut, right, DensePolynomialLoop.ready, DensePolynomialLoop.state, regPorts]
    · intro i
      have hi := hsmall i
      fin_cases i <;>
        simp [addOut, right, scalarPorts, DensePolynomialLoop.ready, DensePolynomialLoop.state,
          DensePolynomialLoop.stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod] at hi ⊢ <;> exact hi
    · intro j
      refine Fin.addCases (m := 8) (n := 8) ?_ ?_ j
      · intro i hi
        exact False.elim (hi ⟨i, rfl⟩)
      · intro i _
        simp [addOut, Fin.addCases_right, -Fin.natAdd_eq_addNat]
    · intro j hj
      have h8 : j ≠ 8 := fun h => hj ⟨8, by simpa [scalarPorts] using h.symm⟩
      have h9 : j ≠ 9 := fun h => hj ⟨9, by simpa [scalarPorts] using h.symm⟩
      simp [addOut, h8, h9]
  have he := eval_call_lifted DensePolynomialProgram.addProgram regPorts scalarPorts d
    regPorts_injective scalarPorts_injective (a := left) (b := right) htrace
  exact ⟨n, hcost, regs', by simpa only [addCall, hl, hr] using he⟩

def updateCell : Code :=
  .seq copyIndex (.seq arrayRead (.seq (moveForward 112 9) (.seq addCall
    (.seq (moveForward 8 112) (.seq copyIndex (.seq arrayReplace (clear 112)))))))

abbrev program : Program 16 128 (StructuredCalls.size updateCell + 1) :=
  StructuredCalls.compiled updateCell 8 102

def eventBudget (degree B I : ℕ) : ℕ :=
  addBudget degree B + I * (28 * (degree * B) + 34) + 49 * (degree * B) + 62

include cache hB hadd in
/-- Exact stack endpoint: only the consumed contribution and selected jet
cell change. The persistent index and all other caller stacks are preserved. -/
theorem updateCell_eval (d : Data) (a b : Coeff (baseWidth p t) degree)
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (hs : d.stacks 102 = earlier.flatten ++ (RingProgram.flat b ++ rest))
    (hi : d.stacks 103 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hw : d.stacks 104 = widthWord) (hwLen : widthWord.length = degree * baseWidth p t)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hscalarWidth : scalarWidth.length = baseWidth p t)
    (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
      (DensePolynomialLoop.ready (d.regs ∘ regPorts) M.bits
        (RingProgram.flat a) [] scalarWidth [] frame).stacks i)
    (h112 : d.stacks 112 = []) (h113 : d.stacks 113 = [])
    (h114 : d.stacks 114 = []) (h115 : d.stacks 115 = [])
    (h116 : d.stacks 116 = []) (h117 : d.stacks 117 = []) (h118 : d.stacks 118 = []) :
    ∃ n ≤ eventBudget degree (baseWidth p t) indexWord.length, ∃ e : Data,
      Eval updateCell n d e ∧
      e.stacks = Function.update (Function.update d.stacks 8 []) 102
        (earlier.flatten ++
          (RingProgram.flat (ops.addRun a b).1 ++ rest)) ∧
      (∀ i : Fin 8, e.regs (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i)) := by
  let d₁ := afterCopy d 103 113 0 1
  have h₁ := copyIndex_eval d h114
  let d₂ := readOut d₁ (RingProgram.flat b)
  have h₂ := arrayRead_eval d₁ earlier (RingProgram.flat b) rest widthWord indexWord
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using hs)
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using hw)
    (by simp [d₁, afterCopy, StackRoutines.copyStacks, hi, h113]) hiLen hrows
    (by simp [hwLen])
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using h114)
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using h115)
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using h116)
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using h117)
  let d₃ := moveOut d₂ 112 9
  have h₃ := moveForward_eval d₂ 112 9 (by decide) (by decide) (by decide)
    (by simpa [d₂, d₁, readOut, afterCopy, StackRoutines.copyStacks] using h118)
  have hsmall₃ : ∀ i : Fin 20, d₃.stacks (scalarPorts i) =
      (DensePolynomialLoop.ready (d₃.regs ∘ regPorts) M.bits (RingProgram.flat a)
        (RingProgram.flat b) scalarWidth [] frame).stacks i := by
    intro i
    have h := hsmall i
    fin_cases i <;>
      simp [d₃, d₂, d₁, moveOut, readOut, afterCopy, StackRoutines.copyStacks,
        scalarPorts, DensePolynomialLoop.ready, DensePolynomialLoop.state, DensePolynomialLoop.stackArray,
        Fin.addCases, Fin.coe_ofNat_eq_mod, h112] at h ⊢ <;> simp [h]
  obtain ⟨m, hm, regs', h₄⟩ := addCall_eval p t M cache hB ops hadd d₃ a b scalarWidth frame hscalarWidth hsmall₃
  let result := (ops.addRun a b).1
  let d₄ := addOut d₃ regs' (RingProgram.flat result)
  let d₅ := moveOut d₄ 8 112
  have h₅ := moveForward_eval d₄ 8 112 (by decide) (by decide) (by decide)
    (by simpa [d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h118)
  let d₆ := afterCopy d₅ 103 113 0 1
  have h₆ := copyIndex_eval d₅
    (by simpa [d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h114)
  let d₇ := replaceOut d₆ earlier (RingProgram.flat result) rest
  have h₇ := arrayReplace_eval d₆ earlier (RingProgram.flat b)
    (RingProgram.flat result) rest widthWord indexWord
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using hs)
    (by simp [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks])
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using hw)
    (by simp [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks, hi]) hiLen hrows (by simp [hwLen]) (by simp [hwLen])
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h114)
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h115)
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h116)
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h117)
  let d₈ := clearOut d₇ 112
  have h₈ := clear_eval d₇ 112
  have ht : Eval updateCell _ d d₈ :=
    Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ (Eval.seq h₄ (Eval.seq h₅
      (Eval.seq h₆ (Eval.seq h₇ h₈))))))
  refine ⟨_, ?_, d₈, ht, ?_, ?_⟩
  · simp [eventBudget, d₇, d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut,
      replaceOut, afterCopy, StackRoutines.copyStacks, hi, h112, hwLen] at ⊢
    rw [hiLen]
    nlinarith [hm]
  · have h9 : d.stacks 9 = [] := by
      simpa [scalarPorts, DensePolynomialLoop.ready, DensePolynomialLoop.state, DensePolynomialLoop.stackArray,
        Fin.addCases, Fin.coe_ofNat_eq_mod]
        using hsmall 9
    exact updatedState_stacks d regs' (RingProgram.flat b)
      (RingProgram.flat result) earlier rest h9 h112 h113
  · exact updatedState_regs d regs' (RingProgram.flat b)
      (RingProgram.flat result) earlier rest


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell

end OAI.Algorithms
