import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupPrimitives
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms

namespace OAI.Algorithms

/-! A fixed native ceiling-logarithm controller. The positive runtime input
t is changed to t-1; a zero guard handles t=1, otherwise floor-log-plus-one
computes the exact Newton iteration count. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Log

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev Data := StructuredProgram.State 3 3
abbrev io := Setup.io

abbrev decrement : Cmd 3 3 :=
  .call (ProgramLinking.liftProgram (CounterPrograms.rippleProgram false)
    id Setup.incrementPorts)

theorem decrement_eval (xs : List Bool) :
    Eval decrement (CounterPrograms.rippleCost false xs + 1)
      (io xs) (io (ripple false xs)) := by
  have he := eval_call_lifted (CounterPrograms.rippleProgram false) id
    Setup.incrementPorts (io xs) Function.injective_id Setup.incrementPorts_injective
    (a := StructuredProgram.ioState (0 : Fin 2) xs)
    (b := StructuredProgram.ioState (0 : Fin 2) (ripple false xs))
    (CounterPrograms.ripple_terminal_trace false xs)
  have ha : embedState id Setup.incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) xs) = io xs := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id Setup.incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have hb : embedState id Setup.incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) (ripple false xs)) = io (ripple false xs) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id Setup.incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> simp_all [Setup.incrementPorts, io, Setup.io,
        StructuredProgram.ioState, Fin.exists_fin_succ]
  simpa only [ha, hb] using he

def zeroPorts : CounterForPrograms.Ports 3 3 where
  register := Function.Embedding.refl _
  counter := 0
  scratch := 1
  counter_ne_scratch := by decide

abbrev reset : Cmd 3 3 := .base (SubexpParameterProgram.atoms
  [.set 0 false, .set 1 false, .set 2 false])

theorem reset_eval (d : Data) : Eval reset 3 d ⟨fun _ => false, d.stacks⟩ := by
  have h := SubexpParameterProgram.atoms_eval
    ([.set 0 false, .set 1 false, .set 2 false] : List (StructuredProgram.Atom 3 3)) d
  convert Eval.base h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> rfl
  · rfl

abbrev command : Cmd 3 3 := .seq decrement
  (.seq (CounterForPrograms.zeroCmd zeroPorts)
    (.ite 2 reset (.seq reset Setup.logSucc)))

theorem clog_eq_log_pred (t : ℕ) (ht : 2 ≤ t) :
    Nat.clog 2 t = Nat.log2 (t-1) + 1 := by
  rw [Nat.log2_eq_log_two]
  apply Nat.le_antisymm
  · apply (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp
    have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (t-1)
    omega
  · have hp := Nat.pow_log_le_self 2 (show t-1 ≠ 0 by omega)
    have hlt : 2 ^ Nat.log 2 (t-1) < t := by omega
    have hh := (Nat.pow_lt_iff_lt_clog (by decide : 1 < 2)).mp hlt
    omega

theorem command_eval (xs : List Bool) (hx : 0 < value xs) :
    ∃ output n, value output = Nat.clog 2 (value xs) ∧
      output.length ≤ xs.length + 1 ∧ n ≤ 64*(xs.length+2)^2 ∧
      Eval command n (io xs) (io output) := by
  let ys := ripple false xs
  let z := CounterForPrograms.zeroResult zeroPorts (io ys)
  have hy : value ys = value xs - 1 := by
    have h := CounterPrograms.value_decrement hx
    dsimp [ys]
    omega
  have hlen : ys.length = xs.length := CounterPrograms.decrement_length hx
  have hz := CounterForPrograms.zero_eval zeroPorts (io ys) (by rfl)
  have hzs : z.stacks = (io ys).stacks := by
    exact CounterForPrograms.install_stacks_self zeroPorts (io ys) _ _ _ rfl
  have hzf : z.regs 2 = CounterPrograms.isZero ys := by
    exact CounterForPrograms.install_register zeroPorts (io ys) _ _ _ _ _ 2
  have hr : Eval reset 3 z (io ys) := by
    simpa only [hzs] using reset_eval z
  have hc := CounterPrograms.rippleCost_le false xs
  by_cases hzero : value ys = 0
  · have ht : value xs = 1 := by omega
    have hb : z.regs 2 = true := hzf.trans ((CounterPrograms.isZero_eq_true_iff ys).mpr hzero)
    refine ⟨ys, (CounterPrograms.rippleCost false xs+1)+((8*ys.length+6)+(3+1)), ?_, ?_, ?_, ?_⟩
    · simp [hzero, ht]
    · omega
    · clear hz hzs hzf hr hb
      rw [hlen]
      nlinarith
    · exact (decrement_eval xs).seq (hz.seq (Eval.ite_true hb hr))
  · obtain ⟨out,n,hv,hl,hn,he⟩ := Setup.logSucc_eval ys
    have hb : z.regs 2 = false := hzf.trans
      ((CounterPrograms.isZero_eq_false_iff ys).mpr (by omega))
    refine ⟨out,(CounterPrograms.rippleCost false xs+1)+((8*ys.length+6)+((3+n)+1)), ?_, ?_, ?_, ?_⟩
    · rw [hv, hy, clog_eq_log_pred _ (by omega)]
    · omega
    · clear hz hzs hzf hr hb he
      rw [hlen] at hn ⊢
      nlinarith
    · exact (decrement_eval xs).seq (hz.seq (Eval.ite_false hb (hr.seq he)))

abbrev program := compiled command 0 0

theorem program_runs (xs : List Bool) (hx : 0 < value xs) :
    ∃ output, value output = Nat.clog 2 (value xs) ∧
      output.length ≤ xs.length+1 ∧
      RunsIn program (65*(xs.length+2)^2)
        (initial program xs) (terminal program output) := by
  obtain ⟨out,n,hv,hl,hn,he⟩ := command_eval xs hx
  exact ⟨out,hv,hl,n+1,by nlinarith,compiled_io_trace 0 0 he⟩

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Log

end OAI.Algorithms
