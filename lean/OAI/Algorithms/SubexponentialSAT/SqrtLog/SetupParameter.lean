import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupSearch

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Parameter

open BitProgram StructuredCalls
open CounterPrograms (value)
open ArithmeticExpressionSupport (clearCmd clear_eval)

abbrev Data := Search.Data

abbrev work : Fin 5 ↪ Fin 15 where
  toFun i := ⟨i.val+6, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; simpa using this

def squarePorts : ArithmeticCalls.Ports 15 where
  left := 1
  right := 1
  out := 3
  work := work
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by
    intro i h
    have hv := congrArg Fin.val h
    change i.val + 6 = 1 at hv
    omega
  work_ne_right := by
    intro i h
    have hv := congrArg Fin.val h
    change i.val + 6 = 1 at hv
    omega
  work_ne_out := by
    intro i h
    have hv := congrArg Fin.val h
    change i.val + 6 = 3 at hv
    omega

def quarticPorts : ArithmeticCalls.Ports 15 where
  left := 3
  right := 3
  out := 4
  work := work
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by
    intro i h
    have hv := congrArg Fin.val h
    change i.val + 6 = 3 at hv
    omega
  work_ne_right := by
    intro i h
    have hv := congrArg Fin.val h
    change i.val + 6 = 3 at hv
    omega
  work_ne_out := by
    intro i h
    have hv := congrArg Fin.val h
    change i.val + 6 = 4 at hv
    omega

abbrev prelude : Cmd 8 15 :=
  .seq (ArithmeticCalls.multiplyAt squarePorts)
    (.seq (ArithmeticCalls.multiplyAt quarticPorts)
      (.seq (clearCmd 1)
        (.seq (ArithmeticCalls.copyAt 4 1 11)
          (.seq (clearCmd 3)
            (.seq (clearCmd 4) (ArithmeticCalls.copyAt 2 13 11))))))

abbrev command : Cmd 8 15 := .seq prelude Search.command

/-- The prelude computes the fourth power with two checked multiplications,
then copies the logarithmic bound into the actual loop counter. -/
theorem prelude_eval (d : Data)
    (hempty : ∀ i : Fin 15, i ≠ 1 → i ≠ 2 → d.stacks i = []) :
    ∃ t e, Eval prelude t d e ∧
      value (e.stacks 1) = value (d.stacks 1)^4 ∧
      (e.stacks 1).length ≤ 4*(d.stacks 1).length+3 ∧
      e.stacks 13 = d.stacks 2 ∧ e.stacks 2 = d.stacks 2 ∧
      (∀ i : Fin 15, i ≠ 1 → i ≠ 2 → i ≠ 13 → e.stacks i = []) ∧
      t ≤ 20000*((d.stacks 1).length+(d.stacks 2).length+1)^2 := by
  have hv : ArithmeticCalls.Valid squarePorts d := by
    constructor
    · exact hempty 3 (by decide) (by decide)
    · intro i
      apply hempty
      · intro h
        have hv := congrArg Fin.val h
        change i.val + 6 = 1 at hv
        omega
      · intro h
        have hv := congrArg Fin.val h
        change i.val + 6 = 2 at hv
        omega
  obtain ⟨t1,r1,a,h1,ha,hla,ht1⟩ := ArithmeticCalls.multiplyAt_eval squarePorts d hv
  let d1 : Data := ⟨r1,Function.update d.stacks 3 a⟩
  change Eval _ t1 d d1 at h1
  have hv1 : ArithmeticCalls.Valid quarticPorts d1 := by
    constructor
    · simp [quarticPorts,d1,hempty 4 (by decide) (by decide)]
    · intro i
      have hi3 : work i ≠ (3 : Fin 15) := squarePorts.work_ne_out i
      have he : d.stacks (work i) = [] := by
        apply hempty
        · intro h
          have hv := congrArg Fin.val h
          change i.val + 6 = 1 at hv
          omega
        · intro h
          have hv := congrArg Fin.val h
          change i.val + 6 = 2 at hv
          omega
      simp [quarticPorts,d1,hi3,he]
  obtain ⟨t2,r2,b,h2,hb,hlb,ht2⟩ := ArithmeticCalls.multiplyAt_eval quarticPorts d1 hv1
  let d2 : Data := ⟨r2,Function.update d1.stacks 4 b⟩
  change Eval _ t2 d1 d2 at h2
  let d3 : Data := ⟨readRegs d2.regs 0 1 none,Function.update d2.stacks 1 []⟩
  have h3 : Eval (clearCmd 1) (2*(d.stacks 1).length+3) d2 d3 := by
    simpa [d2,d1] using clear_eval 1 d2
  have h4 := ArithmeticCalls.copyAt_eval (4 : Fin 15) 1 11 d3
    (by decide) (by decide) (by decide) (by simp [d3])
    (by simp [d3,d2,d1,hempty 11 (by decide) (by decide)])
  let d4 := ArithmeticCalls.afterCopy 4 1 d3
  change Eval _ _ d3 d4 at h4
  let d5 : Data := ⟨readRegs d4.regs 0 1 none,Function.update d4.stacks 3 []⟩
  have h5 : Eval (clearCmd 3) (2*a.length+3) d4 d5 := by
    simpa [d5,d4,ArithmeticCalls.afterCopy,d3,d2,d1] using clear_eval 3 d4
  let d6 : Data := ⟨readRegs d5.regs 0 1 none,Function.update d5.stacks 4 []⟩
  have h6 : Eval (clearCmd 4) (2*b.length+3) d5 d6 := by
    simpa [d6,d5,d4,ArithmeticCalls.afterCopy,d3,d2,d1] using clear_eval 4 d5
  have hs6 : d6.stacks = Function.update d.stacks 1 b := by
    funext i
    by_cases h3 : i=3
    · subst i; simp [d6,d5,d4,ArithmeticCalls.afterCopy,d3,d2,d1,hempty 3 (by decide) (by decide)]
    by_cases h4 : i=4
    · subst i; simp [d6,d5,d4,ArithmeticCalls.afterCopy,d3,d2,d1,hempty 4 (by decide) (by decide)]
    by_cases h1 : i=1
    · subst i; simp [d6,d5,d4,ArithmeticCalls.afterCopy,d3,d2,d1]
    · simp [d6,d5,d4,ArithmeticCalls.afterCopy,d3,d2,d1,h3,h4,h1]
  have h7 := ArithmeticCalls.copyAt_eval (2 : Fin 15) 13 11 d6
    (by decide) (by decide) (by decide)
    (by simp [hs6,hempty 13 (by decide) (by decide)])
    (by simp [hs6,hempty 11 (by decide) (by decide)])
  let e := ArithmeticCalls.afterCopy 2 13 d6
  have hse : e.stacks = Function.update (Function.update d.stacks 1 b) 13 (d.stacks 2) := by
    simp [e,ArithmeticCalls.afterCopy,hs6]
  have h4' : Eval (ArithmeticCalls.copyAt 4 1 11) (7*b.length+5) d3 d4 := by
    simpa [d3,d2,d1] using h4
  have h7' : Eval (ArithmeticCalls.copyAt 2 13 11) (7*(d.stacks 2).length+5) d6 e := by
    simpa [hs6] using h7
  refine ⟨t1+(t2+((2*(d.stacks 1).length+3)+((7*b.length+5)+
      ((2*a.length+3)+((2*b.length+3)+(7*(d.stacks 2).length+5)))))),e,
    h1.seq (h2.seq (h3.seq (h4'.seq (h5.seq (h6.seq h7'))))),?_,?_,?_,?_,?_,?_⟩
  · have ha' : BinaryArithmetic.toNat a = BinaryArithmetic.toNat (d.stacks 1)^2 := by
      simpa [squarePorts,pow_two] using ha
    have hb' : BinaryArithmetic.toNat b = BinaryArithmetic.toNat a^2 := by
      simpa [quarticPorts,d1,pow_two] using hb
    simp only [hse,Function.update_noteq (by decide : (1 : Fin 15) ≠ 13),Function.update_same]
    rw [SubexpParameterProgram.value_eq_toNat,SubexpParameterProgram.value_eq_toNat,hb',ha']
    ring
  · simp only [squarePorts] at hla
    simp [quarticPorts,d1] at hlb
    simpa [hse] using (show b.length ≤ 4*(d.stacks 1).length+3 by omega)
  · simp [hse]
  · simp [hse]
  · intro i hi1 hi2 hi13
    simp [hse,hi1,hi13,hempty i hi1 hi2]
  · simp only [squarePorts] at hla ht1
    simp [quarticPorts,d1] at hlb ht2
    nlinarith

end SubexponentialSAT.SqrtLog.Setup.Parameter

namespace SubexponentialSAT.SqrtLog.Setup.Parameter

open BitProgram StructuredCalls
open CounterPrograms (value)

def bound (L W B : ℕ) : ℕ :=
  20000*(W+B+1)^2 +
    L*(20000*(L+(4*W+3)+B+L+2)^2) + (L+1)*(16*B+16)

/-- The complete concrete parameter search, with all prefix arithmetic charged. -/
theorem command_eval (n : ℕ) (d : Data)
    (hw : value (d.stacks 1) = Asymptotic.w n)
    (hL : value (d.stacks 2) = Asymptotic.L n)
    (hempty : ∀ i : Fin 15, i ≠ 1 → i ≠ 2 → d.stacks i = []) :
    ∃ t e, Eval command t d e ∧ value (e.stacks 12) = Asymptotic.s n ∧
      (e.stacks 12).length ≤ Asymptotic.L n ∧
      t ≤ bound (Asymptotic.L n) (d.stacks 1).length (d.stacks 2).length := by
  obtain ⟨tp,a,hp,hc,hcl,hfuel,haL,haempty,hpt⟩ := prelude_eval d hempty
  obtain ⟨ts,e,hs,hv,hl,_,hst⟩ := Search.command_eval n a
    (by simpa [hw] using hc) (by simpa [haL] using hL)
    (by simpa [hfuel] using hL)
    (haempty 0 (by decide) (by decide) (by decide))
    (haempty 12 (by decide) (by decide) (by decide))
    (haempty 14 (by decide) (by decide) (by decide))
    (by
      intro i hi
      apply haempty
      · intro h
        have hv := congrArg Fin.val h
        change i.val = 1 at hv
        omega
      · intro h
        have hv := congrArg Fin.val h
        change i.val = 2 at hv
        omega
      · intro h
        have hv := congrArg Fin.val h
        change i.val = 13 at hv
        omega)
  refine ⟨tp+ts,e,hp.seq hs,hv,hl,?_⟩
  rw [Search.iterationBound,haL,hfuel] at hst
  have hb := Nat.pow_le_pow_left
    (show Asymptotic.L n + (a.stacks 1).length + (d.stacks 2).length + Asymptotic.L n + 2 ≤
      Asymptotic.L n + (4*(d.stacks 1).length+3) + (d.stacks 2).length + Asymptotic.L n + 2 by omega) 2
  have hm := Nat.mul_le_mul_left (Asymptotic.L n) (Nat.mul_le_mul_left 20000 hb)
  dsimp [bound]
  omega

/-- In particular the search cost is polynomial in the logarithmic loop bound
and the two actual input word lengths, including arbitrary zero padding. -/
theorem bound_cubic (L W B : ℕ) :
    bound L W B ≤ 400000*(L+W+B+2)^3 := by
  let X := L+W+B+2
  have hx : 1 ≤ X := by dsimp [X]; omega
  have h1 : W+B+1 ≤ X := by dsimp [X]; omega
  have h2 : L+(4*W+3)+B+L+2 ≤ 4*X := by dsimp [X]; omega
  have h3 : L+1 ≤ X := by dsimp [X]; omega
  have h4 : 16*B+16 ≤ 16*X := by dsimp [X]; omega
  have ha := Nat.pow_le_pow_left h1 2
  have hb := Nat.pow_le_pow_left h2 2
  have hc := Nat.mul_le_mul h3 h4
  have hd : L*(20000*(L+(4*W+3)+B+L+2)^2) ≤ X*(20000*(4*X)^2) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hb)
  have he : X^2 ≤ X^3 := by
    calc
      X^2 = X^2*1 := by simp
      _ ≤ X^2*X := Nat.mul_le_mul_left _ hx
      _ = X^3 := by ring
  dsimp [bound]
  change _ ≤ 400000*X^3
  nlinarith

end SubexponentialSAT.SqrtLog.Setup.Parameter

end OAI.Algorithms
