import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupCleanup

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.Setup.Wrapper

open BitProgram StructuredCalls
open CounterPrograms (value)

abbrev Data := StructuredProgram.State 8 18

def ports : Fin 15 ↪ Fin 18 where
  toFun i := i.castLE (by decide)
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 18 => x.val) h)

def work : List (Fin 18) := List.ofFn ports

abbrev call : Cmd 8 18 := liftCommand Parameter.command 1 12 id ports

abbrev command : Cmd 8 18 :=
  .seq (ArithmeticExpressionSupport.clearCmd 17)
    (.seq (ArithmeticCalls.copyAt 15 1 11)
      (.seq (ArithmeticCalls.copyAt 16 2 11)
        (.seq call
          (.seq (ArithmeticExpressionSupport.clearCmd 11)
            (.seq (ArithmeticCalls.copyAt 12 17 11) (Cleanup.clearMany work))))))

def bound (L W B O : ℕ) : ℕ := 1024*(Parameter.bound L W B + L + W + B + O + 1)

/-- Only the dedicated output changes among the three external ports.
The original L and w words are preserved literally, and every temporary word,
including the padded-zero loop counter, is physically cleared. -/
theorem command_eval (n : ℕ) (d : Data)
    (hw : value (d.stacks 15) = Asymptotic.w n)
    (hL : value (d.stacks 16) = Asymptotic.L n)
    (hempty : ∀ i : Fin 15, d.stacks (ports i) = []) :
    ∃ t e, Eval command t d e ∧
      value (e.stacks 17) = Asymptotic.s n ∧
      (e.stacks 17).length ≤ Asymptotic.L n ∧
      e.stacks 15 = d.stacks 15 ∧ e.stacks 16 = d.stacks 16 ∧
      (∀ i : Fin 15, e.stacks (ports i) = []) ∧
      t ≤ bound (Asymptotic.L n) (d.stacks 15).length (d.stacks 16).length
        (d.stacks 17).length := by
  let d0 : Data := ⟨readRegs d.regs 0 1 none,Function.update d.stacks 17 []⟩
  have h0 : Eval (ArithmeticExpressionSupport.clearCmd 17) (2*(d.stacks 17).length+3) d d0 :=
    ArithmeticExpressionSupport.clear_eval 17 d
  have hp1 : ports (1 : Fin 15) = (1 : Fin 18) := Fin.ext rfl
  have hp2 : ports (2 : Fin 15) = (2 : Fin 18) := Fin.ext rfl
  have hp11 : ports (11 : Fin 15) = (11 : Fin 18) := Fin.ext rfl
  have hp17 (i : Fin 15) : ports i ≠ (17 : Fin 18) := by
    intro h
    have hval := congrArg Fin.val h
    change i.val = 17 at hval
    omega
  have hp2ne1 : ports (2 : Fin 15) ≠ (1 : Fin 18) := by
    intro h
    have hval := congrArg Fin.val h
    change (2 : Nat) = 1 at hval
    omega
  have hp11ne1 : ports (11 : Fin 15) ≠ (1 : Fin 18) := by
    intro h
    have hval := congrArg Fin.val h
    change (11 : Nat) = 1 at hval
    omega
  have he1 : d0.stacks 1 = [] := by
    change Function.update d.stacks 17 [] 1 = []
    rw [← hp1, Function.update_noteq (hp17 1)]
    exact hempty 1
  have he11 : d0.stacks 11 = [] := by
    change Function.update d.stacks 17 [] 11 = []
    rw [← hp11, Function.update_noteq (hp17 11)]
    exact hempty 11
  have h1 := ArithmeticCalls.copyAt_eval (15 : Fin 18) 1 11 d0
    (by decide) (by decide) (by decide)
    he1 he11
  let d1 := ArithmeticCalls.afterCopy 15 1 d0
  change Eval _ _ d0 d1 at h1
  have he2 : d1.stacks 2 = [] := by
    change Function.update (Function.update d.stacks 17 []) 1 (d.stacks 15) 2 = []
    rw [← hp2, Function.update_noteq hp2ne1, Function.update_noteq (hp17 2)]
    exact hempty 2
  have he11' : d1.stacks 11 = [] := by
    change Function.update (Function.update d.stacks 17 []) 1 (d.stacks 15) 11 = []
    rw [← hp11, Function.update_noteq hp11ne1, Function.update_noteq (hp17 11)]
    exact hempty 11
  have h2 := ArithmeticCalls.copyAt_eval (16 : Fin 18) 2 11 d1
    (by decide) (by decide) (by decide)
    he2 he11'
  let d2 := ArithmeticCalls.afterCopy 16 2 d1
  change Eval _ _ d1 d2 at h2
  let a := projectState id ports d2
  have ha1 : a.stacks 1 = d.stacks 15 := by
    change d2.stacks (ports 1) = d.stacks 15
    rw [hp1]
    simp [d2, d1, ArithmeticCalls.afterCopy, d0]
  have ha2 : a.stacks 2 = d.stacks 16 := by
    change d2.stacks (ports 2) = d.stacks 16
    rw [hp2]
    simp [d2, d1, ArithmeticCalls.afterCopy, d0]
  have hae : ∀ i : Fin 15, i ≠ 1 → i ≠ 2 → a.stacks i = [] := by
    intro i hi1 hi2
    have hp1 : ports i ≠ (1 : Fin 18) := by
      intro h; apply hi1; apply Fin.ext; exact congrArg (fun j : Fin 18 => j.val) h
    have hp2 : ports i ≠ (2 : Fin 18) := by
      intro h; apply hi2; apply Fin.ext; exact congrArg (fun j : Fin 18 => j.val) h
    have hp17 : ports i ≠ (17 : Fin 18) := by
      intro h
      have hval := congrArg Fin.val h
      change i.val = 17 at hval
      omega
    simpa [a,projectState,d2,d1,ArithmeticCalls.afterCopy,d0,hp1,hp2,hp17] using hempty i
  obtain ⟨tc,b,hc,hbs,hbl,hct⟩ := Parameter.command_eval n a
    (by simpa [ha1] using hw) (by simpa [ha2] using hL) hae
  let d3 := embedState id ports d2 b
  have h3 : Eval call (tc+1) d2 d3 :=
    eval_liftCommand_from_state Parameter.command 1 12 id ports d2
      Function.injective_id ports.injective hc
  have h3local (i : Fin 15) : d3.stacks (ports i) = b.stacks i :=
    embedState_stack id ports d2 b ports.injective i
  have h3out (i : Fin 18) (hi : 15 ≤ i.val) : d3.stacks i = d2.stacks i := by
    apply embedState_stack_frame
    rintro ⟨j,hj⟩
    have hval := congrArg Fin.val hj
    change j.val = i.val at hval
    omega
  have h315 : d3.stacks 15 = d.stacks 15 := by rw [h3out 15 (by decide)]; simp [d2,d1,ArithmeticCalls.afterCopy,d0]
  have h316 : d3.stacks 16 = d.stacks 16 := by rw [h3out 16 (by decide)]; simp [d2,d1,ArithmeticCalls.afterCopy,d0]
  have h317 : d3.stacks 17 = [] := by rw [h3out 17 (by decide)]; simp [d2,d1,ArithmeticCalls.afterCopy,d0]
  have h312 : d3.stacks 12 = b.stacks 12 := h3local 12
  let D := 18*((d.stacks 15).length+(d.stacks 16).length) +
    Parameter.bound (Asymptotic.L n) (d.stacks 15).length (d.stacks 16).length + 1
  have haB : ∀ i, (a.stacks i).length ≤ (d.stacks 15).length+(d.stacks 16).length := by
    intro i
    by_cases hi1 : i=1
    · subst i; rw [ha1]; omega
    by_cases hi2 : i=2
    · subst i; rw [ha2]; omega
    rw [hae i hi1 hi2]; simp
  have haSum : BitProgram.stackBits a.stacks ≤
      15*((d.stacks 15).length+(d.stacks 16).length) := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => haB i)
    simpa [BitProgram.stackBits] using hh
  have hbD : ∀ i, (b.stacks i).length ≤ D := by
    intro i
    have hh := Cleanup.output_length_le Parameter.command 1 12 hc i
    rw [ha1,ha2] at hct
    dsimp [D]
    omega
  have hd3 : ∀ i, (d3.stacks i).length ≤ D := by
    intro i
    by_cases hi : i.val < 15
    · let j : Fin 15 := ⟨i.val,hi⟩
      have hj : ports j = i := Fin.ext rfl
      rw [← hj,h3local]
      exact hbD j
    · have hor : i=15 ∨ i=16 ∨ i=17 := by omega
      rcases hor with rfl | rfl | rfl
      · rw [h315]; dsimp [D]; omega
      · rw [h316]; dsimp [D]; omega
      · rw [h317]; simp
  let d4 : Data := ⟨readRegs d3.regs 0 1 none,Function.update d3.stacks 11 []⟩
  have h4 : Eval (ArithmeticExpressionSupport.clearCmd 11) (2*(d3.stacks 11).length+3) d3 d4 :=
    ArithmeticExpressionSupport.clear_eval 11 d3
  have h5 := ArithmeticCalls.copyAt_eval (12 : Fin 18) 17 11 d4
    (by decide) (by decide) (by decide) (by simp [d4,h317]) (by simp [d4])
  let d5 := ArithmeticCalls.afterCopy 12 17 d4
  change Eval _ _ d4 d5 at h5
  have hd5 : ∀ i, (d5.stacks i).length ≤ D+Asymptotic.L n := by
    intro i
    by_cases hi17 : i=17
    · subst i; simpa [d5,ArithmeticCalls.afterCopy,d4,h312] using hbl.trans (Nat.le_add_left _ _)
    by_cases hi11 : i=11
    · subst i; simp [d5,ArithmeticCalls.afterCopy,d4]
    · simpa [d5,ArithmeticCalls.afterCopy,d4,hi17,hi11] using
        (hd3 i).trans (Nat.le_add_right _ _)
  obtain ⟨te,e,he,hes,het⟩ := Cleanup.clearMany_eval work d5 (D+Asymptotic.L n) hd5
  have hmem (i : Fin 18) : i ∈ work ↔ i.val < 15 := by
    simp only [work,List.mem_ofFn]
    constructor
    · rintro ⟨j,rfl⟩; exact j.isLt
    · intro hi; exact ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
  refine ⟨_,e,h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq he))))),?_,?_,?_,?_,?_,?_⟩
  · rw [hes,ite_eq_right (by rw [hmem]; decide : ¬ (17 : Fin 18) ∈ work)]
    simpa [d5,ArithmeticCalls.afterCopy,d4,h312] using hbs
  · rw [hes,ite_eq_right (by rw [hmem]; decide : ¬ (17 : Fin 18) ∈ work)]
    simpa [d5,ArithmeticCalls.afterCopy,d4,h312] using hbl
  · rw [hes,ite_eq_right (by rw [hmem]; decide : ¬ (15 : Fin 18) ∈ work)]
    simp [d5,ArithmeticCalls.afterCopy,d4,h315]
  · rw [hes,ite_eq_right (by rw [hmem]; decide : ¬ (16 : Fin 18) ∈ work)]
    simp [d5,ArithmeticCalls.afterCopy,d4,h316]
  · intro i; rw [hes,ite_eq_left ((hmem _).2 i.isLt)]
  · have h11 := hd3 11
    have h12 : (d4.stacks 12).length ≤ Asymptotic.L n := by simpa [d4,h312] using hbl
    rw [ha1,ha2] at hct
    have hwlen : work.length = 15 := by simp [work]
    rw [hwlen] at het
    simp only [d1,d0,ArithmeticCalls.afterCopy,Function.update_of_ne (by decide : (15 : Fin 18) ≠ 17),
      Function.update_of_ne (by decide : (16 : Fin 18) ≠ 1),Function.update_of_ne (by decide : (16 : Fin 18) ≠ 17)]
    dsimp [D] at h11 het
    dsimp [bound]
    omega

end SubexponentialSAT.SqrtLog.Setup.Wrapper

namespace SubexponentialSAT.SqrtLog.Setup.Wrapper

/-- A plain cubic envelope, including the old output word being overwritten. -/
theorem bound_cubic (L W B O : ℕ) :
    bound L W B O ≤ 409601024*(L+W+B+O+2)^3 := by
  let X := L+W+B+O+2
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hp : Parameter.bound L W B ≤ 400000*X^3 :=
    (Parameter.bound_cubic L W B).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by dsimp [X]; omega) 3))
  have hs : L+W+B+O+1 ≤ X^3 := by
    apply (show L+W+B+O+1 ≤ X by dsimp [X]; omega).trans
    simpa only [pow_one] using Nat.pow_le_pow_right hX (by decide : 1 ≤ 3)
  change bound L W B O ≤ 409601024*X^3
  calc
    bound L W B O = 1024*(Parameter.bound L W B+(L+W+B+O+1)) := by unfold bound; ring
    _ ≤ 1024*(400000*X^3+X^3) := Nat.mul_le_mul_left _ (Nat.add_le_add hp hs)
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.Setup.Wrapper

end OAI.Algorithms
