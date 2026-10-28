import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixParityProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixNegationProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Apply the sign (-1)^A to a canonical scalar, where A is the length of
a runtime unary stack. The parity loop and modular negation are both actual
finite subprograms. -/

namespace SubexponentialSAT.Subexp.MatrixSignedWordProgram

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding

abbrev Data := State 9 10

def parityRegs : Fin 3 → Fin 9 := ![0, 1, 8]
def parityPorts : Fin 1 → Fin 10 := fun _ => 9
def negRegs : Fin 8 → Fin 9 := Fin.castAdd 1
def negPorts : Fin 9 → Fin 10 := Fin.castAdd 1

theorem parityRegs_injective : Function.Injective parityRegs := by decide
theorem parityPorts_injective : Function.Injective parityPorts := by decide
theorem negRegs_injective : Function.Injective negRegs := by
  intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 9 => k.val) h
theorem negPorts_injective : Function.Injective negPorts := by
  intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 10 => k.val) h

abbrev parity : Cmd 9 10 := .call
  (ProgramLinking.liftProgram MatrixParityProgram.program parityRegs parityPorts)
abbrev negate : Cmd 9 10 := .call
  (ProgramLinking.liftProgram MatrixNegationProgram.program negRegs negPorts)
abbrev command : Cmd 9 10 :=
  .seq (.base (.atom (.set 8 false))) (.seq parity (.ite 8 negate (.base .skip)))

variable (p : ℕ) [Fact p.Prime]

def state (regs : Fin 9 → Bool) (x : ZMod p) (count : List Bool) : Data :=
  ⟨regs, ![word p x, [], [], [], [], modulus p, [], [], [], count]⟩

def parityResultRegs (regs : Fin 9 → Bool) (b : Bool) : Fin 9 → Bool :=
  Function.update (Function.update (Function.update regs 0 false) 1 false) 8 b

omit [Fact p.Prime] in
theorem parity_eval (regs : Fin 9 → Bool) (x : ZMod p) (count : List Bool)
    (h8 : regs 8 = false) :
    Eval parity (3 * count.length + 3) (state p regs x count)
      (state p (parityResultRegs regs (MatrixParityProgram.toggle count.length false)) x []) := by
  let localRegs : Fin 3 → Bool := fun j => regs (parityRegs j)
  have ht := MatrixParityProgram.program_trace localRegs count
  have hstart : embedState parityRegs parityPorts (state p regs x count)
      ⟨localRegs, fun _ => count⟩ = state p regs x count := by
    apply embedState_eq_of_ports _ _ _ _ _ parityRegs_injective parityPorts_injective
    · intro j; rfl
    · intros; rfl
    · intro j; fin_cases j; rfl
    · intros; rfl
  have hfinish : embedState parityRegs parityPorts (state p regs x count)
      ⟨![false, false, MatrixParityProgram.toggle count.length (localRegs 2)], fun _ => []⟩ =
      state p (parityResultRegs regs (MatrixParityProgram.toggle count.length false)) x [] := by
    apply embedState_eq_of_ports _ _ _ _ _ parityRegs_injective parityPorts_injective
    · intro j
      fin_cases j <;> simp [state, parityResultRegs, parityRegs, localRegs, h8]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h8' : j ≠ 8 := fun h => hj ⟨2, h.symm⟩
      simp [state, parityResultRegs, h0, h1, h8']
    · intro j; fin_cases j; rfl
    · intro j hj
      have h9 : j ≠ 9 := fun h => hj ⟨0, h.symm⟩
      fin_cases j <;> simp_all [state]
  have he := eval_call_lifted MatrixParityProgram.program parityRegs parityPorts
    (state p regs x count) parityRegs_injective parityPorts_injective
    (a := ⟨localRegs, fun _ => count⟩)
    (b := ⟨![false, false, MatrixParityProgram.toggle count.length (localRegs 2)], fun _ => []⟩) ht
  rw [hstart, hfinish] at he
  exact he

def installRegs (old : Fin 9 → Bool) (new : Fin 8 → Bool) : Fin 9 → Bool :=
  fun j => if h : j.val < 8 then new ⟨j.val, h⟩ else old j

theorem negate_eval (regs : Fin 9 → Bool) (x : ZMod p) :
    ∃ n ≤ 6073 * (width p + 1)^2 + 1, ∃ out : Fin 9 → Bool,
      Eval negate n (state p regs x []) (state p out (-x) []) := by
  let localRegs : Fin 8 → Bool := fun j => regs (negRegs j)
  obtain ⟨r, n, hn, ht⟩ := MatrixNegationProgram.program_runsIn p localRegs x
  have hstart : embedState negRegs negPorts (state p regs x [])
      (MatrixNegationProgram.state p localRegs x) = state p regs x [] := by
    apply embedState_eq_of_ports _ _ _ _ _ negRegs_injective negPorts_injective
    · intro j; rfl
    · intros; rfl
    · intro j
      fin_cases j <;> simp [state, negPorts, MatrixNegationProgram.state,
        SubexpNegationProgram.state, SubexpNegationProgram.extendEight,
        ModularRingPrograms.extendSeven, ModularDivisionPrograms.resting,
        ModularDivisionPrograms.seven]
    · intro j hj
      have hge : 9 ≤ j.val := by
        by_contra h
        exact hj ⟨⟨j.val, by omega⟩, Fin.ext rfl⟩
      fin_cases j <;> norm_num [state] at *
  have hfinish : embedState negRegs negPorts (state p regs x [])
      (MatrixNegationProgram.state p r (-x)) = state p (installRegs regs r) (-x) [] := by
    apply embedState_eq_of_ports _ _ _ _ _ negRegs_injective negPorts_injective
    · intro j; simp [state, installRegs, negRegs, j.isLt, MatrixNegationProgram.state]
    · intro j hj
      have hge : ¬ j.val < 8 := by
        intro h
        exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [state, installRegs, hge]
    · intro j
      fin_cases j <;> simp [state, negPorts, MatrixNegationProgram.state,
        SubexpNegationProgram.state, SubexpNegationProgram.extendEight,
        ModularRingPrograms.extendSeven, ModularDivisionPrograms.resting,
        ModularDivisionPrograms.seven]
    · intro j hj
      have hge : 9 ≤ j.val := by
        by_contra h
        exact hj ⟨⟨j.val, by omega⟩, Fin.ext rfl⟩
      fin_cases j <;> norm_num [state] at *
  have he := eval_call_lifted MatrixNegationProgram.program negRegs negPorts
    (state p regs x []) negRegs_injective negPorts_injective ht
  rw [hstart, hfinish] at he
  exact ⟨n, hn, installRegs regs r, he⟩

theorem command_eval (regs : Fin 9 → Bool) (x : ZMod p) (count : List Bool) :
    ∃ n ≤ 6073 * (width p + 1)^2 + 3 * count.length + 6, ∃ out : Fin 9 → Bool,
      Eval command n (state p regs x count)
        (state p out ((-1 : ZMod p)^count.length * x) []) := by
  let r0 := Function.update regs 8 false
  have hset : Eval (.base (.atom (.set 8 false))) 1 (state p regs x count)
      (state p r0 x count) := .base (.atom _ _)
  have hp := parity_eval p r0 x count (by simp [r0])
  let r1 := parityResultRegs r0 (MatrixParityProgram.toggle count.length false)
  have hsign := MatrixParityProgram.false_sign_toggle (K := ZMod p) count.length
  cases hb : MatrixParityProgram.toggle count.length false with
  | false =>
      have hpow : (-1 : ZMod p)^count.length = 1 := by
        simpa [hb, MatrixParityProgram.sign] using hsign.symm
      have hg : (state p r1 x []).regs 8 = false := by simp [state, r1, parityResultRegs, hb]
      have he := hset.seq (hp.seq (Eval.ite_false (yes := negate) hg
        (Eval.base (StructuredProgram.Eval.skip _))))
      refine ⟨1 + (3 * count.length + 3 + 1), by omega, r1, ?_⟩
      simpa [command, hpow] using he
  | true =>
      have hpow : (-1 : ZMod p)^count.length = -1 := by
        simpa [hb, MatrixParityProgram.sign] using hsign.symm
      obtain ⟨nn, hnn, rn, hn⟩ := negate_eval p r1 x
      have hg : (state p r1 x []).regs 8 = true := by simp [state, r1, parityResultRegs, hb]
      have he := hset.seq (hp.seq (Eval.ite_true (no := .base .skip) hg hn))
      refine ⟨1 + (3 * count.length + 3 + (nn + 1)), by omega, rn, ?_⟩
      simpa [command, hpow] using he

def program := compiled command 0 0

theorem program_runsIn (regs : Fin 9 → Bool) (x : ZMod p) (count : List Bool) :
    ∃ out, RunsIn program (6073 * (width p + 1)^2 + 3 * count.length + 7)
      ((state p regs x count).withPC (some program.entry))
      ((state p out ((-1 : ZMod p)^count.length * x) []).withPC none) := by
  obtain ⟨n, hn, r, ht⟩ := command_eval p regs x count
  exact ⟨r, n + 1, by omega, compiled_halt_trace ht 0 0⟩

end SubexponentialSAT.Subexp.MatrixSignedWordProgram

end OAI.Algorithms
