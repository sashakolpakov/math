import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupGuard
import OAI.Algorithms.SubexponentialSAT.CeilingDivisionPrograms

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Search

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev Data := StructuredProgram.State 8 15

abbrev guardPorts : Fin 12 ↪ Fin 15 where
  toFun i := i.castLE (by decide)
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 15 => x.val) h)

abbrev guard : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram (compiled Guard.command 0 0) id guardPorts)

/-- The guard is an actual finite subroutine call; all caller stacks are framed. -/
theorem guard_eval (d : Data)
    (hempty : ∀ i : Fin 12, 3 ≤ i.val → d.stacks (guardPorts i) = []) :
    ∃ t e, Eval guard t d e ∧ e.stacks = d.stacks ∧
      (e.regs 0 = true ↔ value (d.stacks 0)^2 * value (d.stacks 1) ≤
        value (d.stacks 2)) ∧
      t ≤ 10001 * ((d.stacks 0).length + (d.stacks 1).length +
        (d.stacks 2).length + 1)^2 := by
  let a := projectState id guardPorts d
  obtain ⟨t,b,he,hs,hf,ht⟩ := Guard.command_eval a hempty
  let e := embedState id guardPorts d b
  have hh := eval_call_lifted (compiled Guard.command 0 0) id guardPorts d
    Function.injective_id guardPorts.injective (compiled_halt_trace he 0 0)
  rw [embedState_project id guardPorts d Function.injective_id guardPorts.injective] at hh
  refine ⟨t+1,e,hh,?_,?_,?_⟩
  · funext i
    by_cases hi : ∃ j, guardPorts j = i
    · obtain ⟨j,rfl⟩ := hi
      rw [show e.stacks (guardPorts j) = b.stacks j from
        embedState_stack id guardPorts d b guardPorts.injective j, hs]
      rfl
    · exact embedState_stack_frame id guardPorts d b i hi
  · change (embedState id guardPorts d b).regs 0 = true ↔ _
    rw [show (embedState id guardPorts d b).regs 0 = b.regs 0 from
      embedState_register id guardPorts d b Function.injective_id 0]
    change b.regs 0 = true ↔
      BinaryArithmetic.toNat (d.stacks (guardPorts 0))^2 *
        BinaryArithmetic.toNat (d.stacks (guardPorts 1)) ≤
          BinaryArithmetic.toNat (d.stacks (guardPorts 2)) at hf
    have h0 : guardPorts 0 = 0 := rfl
    have h1 : guardPorts 1 = 1 := rfl
    have h2 : guardPorts 2 = 2 := rfl
    simpa only [h0, h1, h2, SubexpParameterProgram.value_eq_toNat] using hf
  · change t ≤ 10000 * ((d.stacks 0).length + (d.stacks 1).length +
        (d.stacks 2).length + 1)^2 at ht
    have hp : 0 < ((d.stacks 0).length + (d.stacks 1).length +
        (d.stacks 2).length + 1)^2 := Nat.pow_pos (by omega)
    omega

abbrev incrementPorts : CounterForPrograms.Ports 8 15 :=
  ⟨CeilingDivisionPrograms.registers, 0, 11, by decide⟩

abbrev loopPorts : CounterForPrograms.Ports 8 15 :=
  ⟨CeilingDivisionPrograms.registers, 13, 14, by decide⟩

abbrev save : Cmd 8 15 :=
  .seq (ArithmeticExpressionSupport.clearCmd 12) (ArithmeticCalls.copyAt 0 12 11)

abbrev body : Cmd 8 15 :=
  .seq (CeilingDivisionPrograms.incrementCmd incrementPorts)
    (.seq guard (.ite 0 save (.base .skip)))

abbrev command : Cmd 8 15 := CounterForPrograms.forCmd loopPorts body

/-- Saving the current candidate overwrites only the answer port. -/
theorem save_eval (d : Data) (hs : d.stacks 11 = []) :
    ∃ e, Eval save (2*(d.stacks 12).length + 3 + (7*(d.stacks 0).length+5)) d e ∧
      e.stacks = Function.update d.stacks 12 (d.stacks 0) := by
  let a : Data := ⟨readRegs d.regs 0 1 none, Function.update d.stacks 12 []⟩
  have h1 := ArithmeticExpressionSupport.clear_eval 12 d
  change Eval _ _ d a at h1
  have h2 := ArithmeticCalls.copyAt_eval (0 : Fin 15) 12 11 a
    (by decide) (by decide) (by decide) (by simp [a]) (by simp [a,hs])
  refine ⟨ArithmeticCalls.afterCopy 0 12 a, h1.seq (by simpa [a] using h2), ?_⟩
  simp [ArithmeticCalls.afterCopy, a]

/-- One real callback performs one candidate test. -/
theorem body_eval (d : Data)
    (hempty : ∀ i : Fin 12, 3 ≤ i.val → d.stacks (guardPorts i) = []) :
    ∃ t e, Eval body t d e ∧
      e.stacks 0 = ripple true (d.stacks 0) ∧
      e.stacks 12 = (if (value (d.stacks 0)+1)^2 * value (d.stacks 1) ≤
        value (d.stacks 2) then ripple true (d.stacks 0) else d.stacks 12) ∧
      (∀ i : Fin 15, i ≠ 0 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      t ≤ 20000 * ((d.stacks 0).length + (d.stacks 1).length +
        (d.stacks 2).length + (d.stacks 12).length + 2)^2 := by
  have hs : d.stacks 11 = [] := hempty 11 (by decide)
  let a := CeilingDivisionPrograms.incrementResult incrementPorts d
  have h1 : Eval _ _ d a := CeilingDivisionPrograms.increment_eval incrementPorts d hs
  have ha : a.stacks 0 = ripple true (d.stacks 0) :=
    CeilingDivisionPrograms.increment_counter incrementPorts d
  have haf : ∀ i : Fin 15, i ≠ 0 → a.stacks i = d.stacks i := by
    intro i hi
    exact CeilingDivisionPrograms.increment_other incrementPorts d hs i hi
  have hea : ∀ i : Fin 12, 3 ≤ i.val → a.stacks (guardPorts i) = [] := by
    intro i hi
    rw [haf (guardPorts i) (by
      intro h
      have hv := congrArg Fin.val h
      change i.val = 0 at hv
      omega)]
    exact hempty i hi
  obtain ⟨tg,b,hg,hbs,hbf,hgt⟩ := guard_eval a hea
  have hb0 : b.stacks 0 = ripple true (d.stacks 0) := by rw [hbs,ha]
  have hb12 : b.stacks 12 = d.stacks 12 := by rw [hbs,haf 12 (by decide)]
  have hbf' : b.regs 0 = true ↔ (value (d.stacks 0)+1)^2 * value (d.stacks 1) ≤
      value (d.stacks 2) := by
    simpa [ha, haf 1 (by decide), haf 2 (by decide), CounterPrograms.value_increment] using hbf
  have hlen := CounterPrograms.ripple_length_le true (d.stacks 0)
  have hrip := CounterPrograms.rippleCost_le true (d.stacks 0)
  have hgt' : tg ≤ 10001 * ((ripple true (d.stacks 0)).length +
      (d.stacks 1).length + (d.stacks 2).length + 1)^2 := by
    simpa [ha, haf 1 (by decide), haf 2 (by decide)] using hgt
  set B := (d.stacks 0).length + (d.stacks 1).length +
    (d.stacks 2).length + (d.stacks 12).length + 2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hb2 : B ≤ B^2 := by nlinarith
  have hgtCommon : tg ≤ 10001*B^2 := by
    apply hgt'.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp [B]
    omega
  by_cases hc : (value (d.stacks 0)+1)^2 * value (d.stacks 1) ≤ value (d.stacks 2)
  · obtain ⟨e,he,hes⟩ := save_eval b (by rw [hbs,haf 11 (by decide)]; exact hs)
    refine ⟨_,e,h1.seq (hg.seq (.ite_true (hbf'.2 hc) he)),?_,?_,?_,?_⟩
    · simp [hes,hb0]
    · simp [hes,hb0,hc]
    · intro i hi0 hi12
      simp only [hes, Function.update_of_ne hi12, hbs]
      exact haf i hi0
    · simp only [hb0,hb12]
      omega
  · have hf : b.regs 0 = false := by
      cases h : b.regs 0 <;> simp_all
    refine ⟨_,b,h1.seq (hg.seq (.ite_false hf (.base (.skip _)))),hb0,?_,?_,?_⟩
    · simp [hc,hb12]
    · intro i hi0 _; rw [hbs]; exact haf i hi0
    · simp only []
      omega

end SubexponentialSAT.SqrtLog.Setup.Search

namespace SubexponentialSAT.SqrtLog.Setup.Search

open BitProgram StructuredCalls
open CounterPrograms (value)

def Invariant (n : ℕ) (initial : Data) (i : ℕ) (d : Data) : Prop :=
  value (d.stacks 0) = i ∧ value (d.stacks 12) = min i (Asymptotic.s n) ∧
  (d.stacks 0).length ≤ i ∧ (d.stacks 12).length ≤ i ∧
  ∀ j : Fin 15, j ≠ 0 → j ≠ 12 → j ≠ 13 → j ≠ 14 →
    d.stacks j = initial.stacks j

theorem invariant_stable (n : ℕ) (initial : Data) :
    CounterForPrograms.FrameStable loopPorts (Invariant n initial) := by
  intro i a b hab hi
  rcases hi with ⟨hv,hs,hl,hl',hf⟩
  have hb0 := hab 0 (by decide) (by decide)
  have hb12 := hab 12 (by decide) (by decide)
  refine ⟨by simpa [← hb0] using hv, by simpa [← hb12] using hs,
    by simpa [← hb0] using hl, by simpa [← hb12] using hl', ?_⟩
  intro j h0 h12 h13 h14
  rw [← hab j h13 h14]
  exact hf j h0 h12 h13 h14

def iterationBound (initial : Data) (i : ℕ) : ℕ :=
  20000 * (i + (initial.stacks 1).length + (initial.stacks 2).length + i + 2)^2

theorem body_spec (n : ℕ) (initial : Data)
    (hc : value (initial.stacks 1) = Asymptotic.w n^4)
    (hL : value (initial.stacks 2) = Asymptotic.L n)
    (hempty : ∀ i : Fin 12, 3 ≤ i.val → initial.stacks (guardPorts i) = []) :
    CounterForPrograms.BodySpec loopPorts body (Invariant n initial) (iterationBound initial) := by
  intro i d hi hscratch _
  rcases hi with ⟨hv,hs,hl,hl',hf⟩
  have hframe1 := hf 1 (by decide) (by decide) (by decide) (by decide)
  have hframe2 := hf 2 (by decide) (by decide) (by decide) (by decide)
  have hdempty : ∀ j : Fin 12, 3 ≤ j.val → d.stacks (guardPorts j) = [] := by
    intro j hj
    rw [hf (guardPorts j)]
    · exact hempty j hj
    · intro h
      have hh := congrArg Fin.val h
      change j.val = 0 at hh
      omega
    · intro h
      have hh := congrArg Fin.val h
      change j.val = 12 at hh
      omega
    · intro h
      have hh := congrArg Fin.val h
      change j.val = 13 at hh
      omega
    · intro h
      have hh := congrArg Fin.val h
      change j.val = 14 at hh
      omega
  obtain ⟨t,e,he,he0,he12,hef,ht⟩ := body_eval d hdempty
  refine ⟨t,e,?_,he,hef 13 (by decide) (by decide),?_,?_⟩
  · dsimp [iterationBound]
    rw [hframe1,hframe2] at ht
    have harg : (d.stacks 0).length + (initial.stacks 1).length +
        (initial.stacks 2).length + (d.stacks 12).length + 2 ≤
        i + (initial.stacks 1).length + (initial.stacks 2).length + i + 2 := by omega
    exact ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
  · exact (hef 14 (by decide) (by decide)).trans hscratch
  · refine ⟨by rw [he0,CounterPrograms.value_increment,hv],?_,?_,?_,?_⟩
    · rw [he12,hv,hframe1,hframe2,hc,hL]
      by_cases h : i+1 ≤ Asymptotic.s n
      · rw [ite_eq_left ((Asymptotic.le_s_iff n (i+1)).1 h)]
        rw [CounterPrograms.value_increment,hv,Nat.min_eq_left h]
      · rw [ite_eq_right (fun hh => h ((Asymptotic.le_s_iff n (i+1)).2 hh)),hs]
        omega
    · rw [he0]
      exact (CounterPrograms.ripple_length_le true (d.stacks 0)).trans (by omega)
    · rw [he12]
      split
      · exact (CounterPrograms.ripple_length_le true (d.stacks 0)).trans (by omega)
      · omega
    · intro j h0 h12 h13 h14
      exact (hef j h0 h12).trans (hf j h0 h12 h13 h14)

/-- Exact bounded-search schedule. The input data include the coefficient w^4,
L, and a second copy of L as loop fuel. Each callback is a genuine arithmetic
trace and every failed candidate is charged. -/
theorem command_eval (n : ℕ) (d : Data)
    (hc : value (d.stacks 1) = Asymptotic.w n^4)
    (hL : value (d.stacks 2) = Asymptotic.L n)
    (hfuel : value (d.stacks 13) = Asymptotic.L n)
    (hzero : d.stacks 0 = []) (hanswer : d.stacks 12 = [])
    (hscratch : d.stacks 14 = [])
    (hempty : ∀ i : Fin 12, 3 ≤ i.val → d.stacks (guardPorts i) = []) :
    ∃ t e, Eval command t d e ∧ value (e.stacks 12) = Asymptotic.s n ∧
      (e.stacks 12).length ≤ Asymptotic.L n ∧
      (∀ j : Fin 15, j ≠ 0 → j ≠ 12 → j ≠ 13 → j ≠ 14 → e.stacks j = d.stacks j) ∧
      t ≤ Asymptotic.L n * iterationBound d (Asymptotic.L n) +
        (Asymptotic.L n+1) * (16*(d.stacks 13).length+16) := by
  have hi : Invariant n d 0 d := by
    refine ⟨by simp [hzero ],by simp [hanswer],
      by simp [hzero],by simp [hanswer],?_⟩
    intro j _ _ _ _; rfl
  obtain ⟨t,e,he,hei,_,_,_,ht⟩ := CounterForPrograms.for_correct loopPorts body
    (Invariant n d) (iterationBound d) (invariant_stable n d)
    (body_spec n d hc hL hempty) d hscratch hi
  change Invariant n d (value (d.stacks 13)) e at hei
  rw [hfuel] at hei
  rcases hei with ⟨_,hse,_,hle,hframe⟩
  refine ⟨t,e,he,?_,hle,hframe,?_⟩
  · simpa [Nat.min_eq_right (Asymptotic.s_le_L n)] using hse
  · change t ≤ CounterForPrograms.budgetSum (iterationBound d) 0 (value (d.stacks 13)) +
      (value (d.stacks 13)+1)*(16*(d.stacks 13).length+16) at ht
    rw [hfuel] at ht
    apply ht.trans
    apply Nat.add_le_add_right
    apply CounterForPrograms.budgetSum_le
    intro i _ hil
    dsimp [iterationBound]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega

end SubexponentialSAT.SqrtLog.Setup.Search

end OAI.Algorithms
