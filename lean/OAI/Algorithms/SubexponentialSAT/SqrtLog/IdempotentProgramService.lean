import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramRegisters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanServiceBasic

namespace OAI.Algorithms

/-! Lift the common 32-stack arithmetic ABI into the Newton machine and prove
that the source-preserving register wrapper has the exact specified effect. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls

/-- The nine added stacks hold four arrays, negative one, degree, copy scratch,
and the binary loop counter plus its scratch. -/
def servicePorts : Fin 32 → Fin 41 := Fin.castAdd 9

theorem servicePorts_injective : Function.Injective servicePorts := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 41 => x.val) h)

abbrev callService (command : Cmd 8 32) : Cmd 8 41 :=
  .call (ProgramLinking.liftProgram (compiled command 8 0) id servicePorts)

theorem callService_eval (command : Cmd 8 32) (a b : State 8 32)
    (d : RegisterData) (result : Fin 41 → List Bool) (n : ℕ)
    (hr : a.regs = d.regs)
    (ha : ∀ i, d.stacks (servicePorts i) = a.stacks i)
    (hb : ∀ i, result (servicePorts i) = b.stacks i)
    (hout : ∀ j, (¬∃ i, servicePorts i = j) → result j = d.stacks j)
    (run : Eval command n a b) :
    ∃ e, Eval (callService command) (n+1) d e ∧ e.stacks = result := by
  have he := eval_call_lifted (compiled command 8 0) id servicePorts d
    Function.injective_id servicePorts_injective (compiled_halt_trace run 8 0)
  have hin : embedState id servicePorts d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id servicePorts_injective
    · intro i; exact (congrFun hr i).symm
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · exact ha
    · intro i hi; rfl
  rw [hin] at he
  refine ⟨embedState id servicePorts d b, he, ?_⟩
  funext j
  by_cases hj : ∃ i, servicePorts i = j
  · obtain ⟨i,rfl⟩ := hj
    rw [embedState_stack _ _ _ _ servicePorts_injective]
    exact (hb i).symm
  · rw [embedState_stack_frame _ _ _ _ j hj]
    exact (hout j hj).symm

/-- The low workspace at rest. No arithmetic input or output is present. -/
def ServiceContext (d : RegisterData) (modulus width zero table : List Bool) : Prop :=
  ∀ i, d.stacks (servicePorts i) =
    (RingScan.serviceState d.regs modulus [] [] [] [] width zero table).stacks i

/-- Any proved native add/multiply service can be wrapped without assuming
free copies or unbounded register access. The exact result overwrites target. -/
theorem registerService_eval (command : Cmd 8 32) (d : RegisterData)
    (modulus width zero table degree leftWord rightWord result : List Bool)
    (target left right : Fin 41) (n : ℕ) (rf : Fin 8 → Bool)
    (context : ServiceContext d modulus width zero table)
    (hd : d.stacks 37 = degree) (hlword : d.stacks left = leftWord)
    (hrword : d.stacks right = rightWord) (hs : d.stacks 38 = [])
    (ht : 32 ≤ target.val) (hl : 32 ≤ left.val) (hr : 32 ≤ right.val)
    (ht38 : target ≠ 38) (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (run : Eval command n
      (RingScan.serviceState (preparedOperands d left right).regs
        modulus [] leftWord rightWord degree width zero table)
      (RingScan.serviceState rf modulus result [] [] [] width zero table)) :
    ∃ f, Eval (registerBinary (callService command) target left right)
      (n+1 + 7*leftWord.length + 7*rightWord.length + 7*degree.length +
        2*(d.stacks target).length + 9*result.length + 26) d f ∧
      f.stacks = Function.update d.stacks target result := by
  have hcontext : ∀ i : Fin 32, d.stacks (servicePorts i) =
      (RingScan.serviceState d.regs modulus [] [] [] [] width zero table).stacks i := context
  have h0 : d.stacks 0 = [] := hcontext 0
  have h8 : d.stacks 8 = [] := hcontext 8
  have h9 : d.stacks 9 = [] := hcontext 9
  have h11 : d.stacks 11 = [] := hcontext 11
  obtain ⟨e, he, hout⟩ := callService_eval command _ _ (preparedOperands d left right)
    (Function.update d.stacks 0 result) n rfl (by
      intro i
      rw [preparedOperands_stacks d left right hr]
      have hi := hcontext i
      fin_cases i <;>
        simp [servicePorts, hd, hlword, hrword,
          RingScan.serviceState, RingScan.serviceWorkState, RingScan.serviceTapes] at hi ⊢ <;>
        exact hi) (by
      intro i
      have hi := hcontext i
      fin_cases i <;>
        simp [servicePorts, RingScan.serviceState,
          RingScan.serviceWorkState, RingScan.serviceTapes] at hi ⊢ <;> exact hi) (by
      intro j hj
      have hlow : 32 ≤ j.val := by
        apply Nat.le_of_not_gt
        intro hjlt
        exact hj ⟨(⟨j.val, hjlt⟩ : Fin 32), Fin.ext rfl⟩
      have hj0 : j ≠ 0 := by intro h; have hv : j.val = 0 := congrArg Fin.val h; omega
      have hj8 : j ≠ 8 := by intro h; have hv : j.val = 8 := congrArg Fin.val h; omega
      have hj9 : j ≠ 9 := by intro h; have hv : j.val = 9 := congrArg Fin.val h; omega
      have hj11 : j ≠ 11 := by intro h; have hv : j.val = 11 := congrArg Fin.val h; omega
      rw [preparedOperands_stacks d left right hr]
      simp [hj0, hj8, hj9, hj11]) run
  obtain ⟨f, hf, hfs⟩ := registerBinary_eval (callService command) d e target left right result
    (n+1) ht hl hr ht38 hl38 hr38 h0 h8 h9 h11 hs he hout
  exact ⟨f, by simpa only [hlword, hrword, hd] using hf, hfs⟩

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
