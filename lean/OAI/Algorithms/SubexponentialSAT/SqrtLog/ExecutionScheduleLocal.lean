import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionSetupLocal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupWrapper

namespace OAI.Algorithms

/-! The complete new schedule on a fixed local stack machine. Runtime
quantities do not occur in the instruction-table definition. -/

namespace SubexponentialSAT.SqrtLog.Execution.ScheduleLocal

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 8 22

def lwPorts : Fin 6 → Fin 22 := ![18, 0, 1, 2, 19, 20]
def searchPorts : Fin 18 → Fin 22 :=
  ![3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 19, 21]

def workSlot (i : Fin 15) : Fin 22 := ⟨i.val+3, by omega⟩

theorem searchPorts_work (i : Fin 15) :
    searchPorts (Setup.Wrapper.ports i) = workSlot i := by
  fin_cases i <;> rfl

theorem lwPorts_injective : Function.Injective lwPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [lwPorts]

theorem searchPorts_injective : Function.Injective searchPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [searchPorts]

abbrev command : Cmd 8 22 :=
  .seq (liftCommand SetupLocal.command 0 5 id lwPorts)
    (liftCommand Setup.Wrapper.command 15 17 id searchPorts)

def Ready (d : Data) : Prop :=
  (∀ i : Fin 18, d.stacks (i.castLE (by decide)) = []) ∧
  d.stacks 19 = [] ∧ d.stacks 20 = []

def bound (N O : ℕ) : ℕ :=
  40010*(N+1)^2 +
    1024*(400000*((N+5)+(N+18)+(N+17)+2)^3+
      (N+5)+(N+18)+(N+17)+O+1)

theorem command_eval (d : Data) (ready : Ready d) :
    ∃ t e, Eval command t d e ∧
      CounterPrograms.value (e.stacks 19) = Asymptotic.L (CounterPrograms.value (d.stacks 18)) ∧
      CounterPrograms.value (e.stacks 20) = Asymptotic.w (CounterPrograms.value (d.stacks 18)) ∧
      CounterPrograms.value (e.stacks 21) = Asymptotic.s (CounterPrograms.value (d.stacks 18)) ∧
      e.stacks 18 = d.stacks 18 ∧
      (e.stacks 21).length ≤ Asymptotic.L (CounterPrograms.value (d.stacks 18)) ∧
      (∀ i : Fin 18, e.stacks (i.castLE (by decide)) = []) ∧
      t ≤ bound (d.stacks 18).length (d.stacks 21).length := by
  obtain ⟨l, w, t, hl, hw, hlen, hwlen, ht, he⟩ :=
    SetupLocal.command_eval (d.stacks 18) d.regs
  have hp : projectState id lwPorts d =
      ⟨d.regs, (SetupLocal.state (d.stacks 18) [] [] []).stacks⟩ := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i
    · rfl
    · exact ready.1 0
    · exact ready.1 1
    · exact ready.1 2
    · exact ready.2.1
    · exact ready.2.2
  let a := embedState id lwPorts d (SetupLocal.state (d.stacks 18) [] l w)
  have hfirst : Eval (liftCommand SetupLocal.command 0 5 id lwPorts) (t+1) d a := by
    apply eval_liftCommand_from_state _ _ _ _ _ _ Function.injective_id lwPorts_injective
    simpa only [hp] using he
  have hal : a.stacks 19 = l := embedState_stack _ _ _ _ lwPorts_injective 4
  have haw : a.stacks 20 = w := embedState_stack _ _ _ _ lwPorts_injective 5
  have han : a.stacks 18 = d.stacks 18 := embedState_stack _ _ _ _ lwPorts_injective 0
  have haf (i : Fin 22) (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2)
      (h18 : i ≠ 18) (h19 : i ≠ 19) (h20 : i ≠ 20) : a.stacks i = d.stacks i := by
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    fin_cases j <;> simp_all [lwPorts]
  let b := projectState id searchPorts a
  have hbs (i : Fin 18) : b.stacks i = a.stacks (searchPorts i) := rfl
  have hbempty (i : Fin 15) : b.stacks (Setup.Wrapper.ports i) = [] := by
    rw [hbs, searchPorts_work, haf]
    · exact ready.1 ⟨i.val+3, by omega⟩
    all_goals intro h; have hv := congrArg Fin.val h; dsimp [workSlot] at hv; omega
  obtain ⟨u, f, hf, hfs, hflen, hfw, hfl, hfempty, hu⟩ := Setup.Wrapper.command_eval
    (CounterPrograms.value (d.stacks 18)) b
    (by change CounterPrograms.value (a.stacks 20) = _; rw [haw]; exact hw)
    (by change CounterPrograms.value (a.stacks 19) = _; rw [hal]; exact hl) hbempty
  let e := embedState id searchPorts a f
  have hsecond : Eval (liftCommand Setup.Wrapper.command 15 17 id searchPorts) (u+1) a e :=
    eval_liftCommand_from_state _ _ _ _ _ _ Function.injective_id searchPorts_injective hf
  have hes (i : Fin 18) : e.stacks (searchPorts i) = f.stacks i :=
    embedState_stack _ _ _ _ searchPorts_injective i
  have hef (i : Fin 22) (hi : i.val < 3 ∨ i = 18) : e.stacks i = a.stacks i := by
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    fin_cases j <;> norm_num [searchPorts] at hv <;> rcases hi with hi | rfl <;> omega
  have hclean (i : Fin 18) : e.stacks (i.castLE (by decide)) = [] := by
    by_cases hi : i.val < 3
    · rw [hef _ (Or.inl hi)]
      fin_cases i
      all_goals norm_num at hi
      all_goals first
        | omega
        | exact embedState_stack _ _ _ _ lwPorts_injective 1
        | exact embedState_stack _ _ _ _ lwPorts_injective 2
        | exact embedState_stack _ _ _ _ lwPorts_injective 3
    · let j : Fin 15 := ⟨i.val-3, by omega⟩
      have hj : workSlot j = i.castLE (by decide) := by
        apply Fin.ext
        dsimp [workSlot, j]
        omega
      rw [← hj, ← searchPorts_work, hes]
      exact hfempty j
  have hbl : b.stacks 16 = l := hal
  have hbw : b.stacks 15 = w := haw
  have hbo : b.stacks 17 = d.stacks 21 := haf _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨(t+1)+(u+1), e, hfirst.seq hsecond, ?_, ?_, ?_, ?_, ?_, hclean, ?_⟩
  · change CounterPrograms.value (e.stacks (searchPorts 16)) = _
    rw [hes, hfl, hbl]; exact hl
  · change CounterPrograms.value (e.stacks (searchPorts 15)) = _
    rw [hes, hfw, hbw]; exact hw
  · exact (congrArg CounterPrograms.value (hes 17)).trans hfs
  · exact (hef 18 (Or.inr rfl)).trans han
  · exact (congrArg List.length (hes 17)).trans_le hflen
  · rw [hbl, hbw, hbo] at hu
    have hL := Setup.L_le_wordLength (d.stacks 18)
    have hc := Setup.Parameter.bound_cubic
      (Asymptotic.L (CounterPrograms.value (d.stacks 18))) w.length l.length
    have hm := Nat.pow_le_pow_left
      (show Asymptotic.L (CounterPrograms.value (d.stacks 18)) + w.length + l.length + 2 ≤
        ((d.stacks 18).length+5)+((d.stacks 18).length+18)+((d.stacks 18).length+17)+2 by omega) 3
    dsimp [bound, Setup.Wrapper.bound] at *
    nlinarith

end SubexponentialSAT.SqrtLog.Execution.ScheduleLocal

end OAI.Algorithms
