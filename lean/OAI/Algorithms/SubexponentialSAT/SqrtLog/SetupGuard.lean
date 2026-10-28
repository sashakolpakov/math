import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupPrimitives
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.SubexpGuardProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Guard

open BitProgram StructuredCalls
open ArithmeticExpressionSupport (clearCmd clear_eval)

abbrev Data := StructuredProgram.State 8 12

def work : Fin 5 ↪ Fin 12 where
  toFun i := ⟨i.val + 6, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; simpa using this

def squarePorts : ArithmeticCalls.Ports 12 where
  left := 0
  right := 0
  out := 3
  work := work
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i h; have hval : i.val + 6 = 0 := congrArg Fin.val h; omega
  work_ne_right := by intro i h; have hval : i.val + 6 = 0 := congrArg Fin.val h; omega
  work_ne_out := by intro i h; have hval : i.val + 6 = 3 := congrArg Fin.val h; omega

def productPorts : ArithmeticCalls.Ports 12 where
  left := 3
  right := 1
  out := 4
  work := work
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i h; have hval : i.val + 6 = 3 := congrArg Fin.val h; omega
  work_ne_right := by intro i h; have hval : i.val + 6 = 1 := congrArg Fin.val h; omega
  work_ne_out := by intro i h; have hval : i.val + 6 = 4 := congrArg Fin.val h; omega

def comparePorts : Fin 2 → Fin 12 := ![5,4]

theorem comparePorts_injective : Function.Injective comparePorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [comparePorts]

abbrev command : Cmd 8 12 :=
  .seq (ArithmeticCalls.multiplyAt squarePorts)
    (.seq (ArithmeticCalls.multiplyAt productPorts)
      (.seq (clearCmd 3)
        (.seq (ArithmeticCalls.copyAt 2 5 11)
          (.seq (.call (ProgramLinking.liftProgram SubexpGuardProgram.Compare.program
            id comparePorts)) (.base (.atom (.bnot 0 0)))))))

/-- All arithmetic is performed by the existing finite multiplier and comparator.
The three source words are preserved and the nine scratch stacks are cleaned. -/
theorem command_eval (d : Data) (hempty : ∀ i : Fin 12, 3 ≤ i.val → d.stacks i = []) :
    ∃ t e, Eval command t d e ∧ e.stacks = d.stacks ∧
      (e.regs 0 = true ↔ BinaryArithmetic.toNat (d.stacks 0)^2 *
        BinaryArithmetic.toNat (d.stacks 1) ≤ BinaryArithmetic.toNat (d.stacks 2)) ∧
      t ≤ 10000 * ((d.stacks 0).length + (d.stacks 1).length +
        (d.stacks 2).length + 1)^2 := by
  have hwork (i : Fin 5) : 3 ≤ (work i).val := by
    change 3 ≤ i.val + 6
    omega
  have hv : ArithmeticCalls.Valid squarePorts d := by
    constructor
    · exact hempty 3 (by decide)
    · intro i; exact hempty (work i) (hwork i)
  obtain ⟨t1, r1, a, h1, ha, hla, ht1⟩ := ArithmeticCalls.multiplyAt_eval squarePorts d hv
  let d1 : Data := ⟨r1, Function.update d.stacks 3 a⟩
  change Eval _ t1 d d1 at h1
  have hv1 : ArithmeticCalls.Valid productPorts d1 := by
    constructor
    · simp [ productPorts, d1, hempty 4 (by decide)]
    · intro i
      have hi : work i ≠ (3 : Fin 12) := squarePorts.work_ne_out i
      change (Function.update d.stacks 3 a) (work i) = []
      rw [Function.update_noteq hi]
      exact hempty (work i) (hwork i)
  obtain ⟨t2, r2, b, h2, hb, hlb, ht2⟩ := ArithmeticCalls.multiplyAt_eval productPorts d1 hv1
  let d2 : Data := ⟨r2, Function.update d1.stacks 4 b⟩
  change Eval _ t2 d1 d2 at h2
  let d3 : Data := ⟨readRegs d2.regs 0 1 none, Function.update d2.stacks 3 []⟩
  have h3 : Eval (clearCmd 3) (2 * a.length + 3) d2 d3 := by
    simpa [d2, d1] using clear_eval 3 d2
  have hs3 : d3.stacks = Function.update d.stacks 4 b := by
    funext i
    by_cases hi : i = 3
    · subst i; simp [d3, d2, d1, hempty 3 (by decide)]
    · by_cases hi4 : i = 4
      · subst i; simp [d3,d2,d1]
      · simp [d3,d2,d1,hi,hi4]
  have h4 := ArithmeticCalls.copyAt_eval (2 : Fin 12) 5 11 d3
    (by decide) (by decide) (by decide)
    (by simp [hs3, hempty 5 (by decide)])
    (by simp [hs3, hempty 11 (by decide)])
  let d4 := ArithmeticCalls.afterCopy 2 5 d3
  change Eval _ _ d3 d4 at h4
  obtain ⟨d5, h5, hf, _, hs5, hz⟩ := SubexpGuardProgram.compare_call id comparePorts
    Function.injective_id comparePorts_injective d4
  let e := (StructuredProgram.Atom.bnot (0 : Fin 8) 0).eval d5
  have h6 : Eval (.base (.atom (.bnot 0 0))) 1 d5 e := .base (.atom _ _)
  refine ⟨t1 + (t2 + ((2 * a.length + 3) +
      ((7 * (d3.stacks 2).length + 5) +
      ((10 * max (d4.stacks (comparePorts 0)).length
        (d4.stacks (comparePorts 1)).length + 6) + 1)))), e,
    h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))), ?_, ?_, ?_⟩
  · funext i
    change d5.stacks i = d.stacks i
    by_cases hi5 : i = 5
    · subst i; simpa [comparePorts, hempty 5 (by decide)] using hz 0
    by_cases hi4 : i = 4
    · subst i; simpa [comparePorts, hempty 4 (by decide)] using hz 1
    have ho : ¬ ∃ j, comparePorts j = i := by
      rintro ⟨j,hj⟩; fin_cases j <;> simp_all [comparePorts]
    rw [hs5 i ho]
    simp [d4, ArithmeticCalls.afterCopy, hs3, hi4, hi5]
  · have ha' : BinaryArithmetic.toNat a = BinaryArithmetic.toNat (d.stacks 0)^2 := by
      simpa [squarePorts, pow_two] using ha
    have hb' : BinaryArithmetic.toNat b = BinaryArithmetic.toNat a *
        BinaryArithmetic.toNat (d.stacks 1) := by
      simpa [productPorts, d1] using hb
    have hf' : d5.regs 0 = true ↔ BinaryArithmetic.toNat (d.stacks 2) <
        BinaryArithmetic.toNat b := by
      simpa [comparePorts, d4, ArithmeticCalls.afterCopy, hs3] using hf
    change (!(d5.regs 0)) = true ↔ _
    rw [hb',ha'] at hf'
    cases hr : d5.regs 0 <;> simp [hr] at hf' ⊢ <;> omega
  · simp only [squarePorts] at hla ht1
    simp only [productPorts, d1, Function.update_same] at hlb ht2
    simp at hlb ht2
    simp [d4, ArithmeticCalls.afterCopy, hs3, comparePorts]
    have hm : max (d.stacks 2).length b.length ≤
        (d.stacks 2).length + b.length := by omega
    nlinarith

end SubexponentialSAT.SqrtLog.Setup.Guard

end OAI.Algorithms
