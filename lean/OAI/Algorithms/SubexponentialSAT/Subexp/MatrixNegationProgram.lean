import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNegationSetup
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Canonical base-field negation using the actual runtime constant producer,
with its temporary constant cleared before returning to the caller. -/

namespace SubexponentialSAT.Subexp.MatrixNegationProgram

open BitProgram StructuredCalls StackRoutines BinaryArithmetic MatrixWordEncoding

abbrev Data := State 8 9

abbrev command : Cmd 8 9 :=
  .seq (.call SubexpNegationSetup.preparedNegationProgram)
    (.call (clearProgram 8 0 1))

variable (p : ℕ) [Fact p.Prime]

def state (regs : Fin 8 → Bool) (x : ZMod p) : Data :=
  ⟨regs, SubexpNegationProgram.state (word p x) (modulus p) []⟩

theorem command_eval (regs : Fin 8 → Bool) (x : ZMod p) :
    ∃ n ≤ 6073 * (width p + 1)^2, ∃ regs',
      Eval command n (state p regs x) (state p regs' (-x)) := by
  obtain ⟨r, out, c, ⟨n, hn, ht⟩, hl, hcl, hcv, hv⟩ :=
    SubexpNegationSetup.preparedNegation_value regs (word p x) (modulus p) (width p)
      (word_length p x) (by simp) (modulus_positive p)
      (by simpa only [modulus_value] using modulus_capacity p)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hc : BinaryArithmetic.toNat out < p := by
    rw [hv, modulus_value]
    exact Nat.mod_lt _ hp
  have hf : (BinaryArithmetic.toNat out : ZMod p) = -x := by
    rw [hv, modulus_value, ZMod.natCast_mod,
      Nat.cast_sub (Nat.mod_lt _ hp).le, ZMod.natCast_self,
      ZMod.natCast_mod, word_field_value, zero_sub]
  have hout := word_unique p (-x) out hl hc hf
  subst out
  let mid : Data := ⟨r, SubexpNegationProgram.state (word p (-x)) (modulus p) c⟩
  have hcall : Eval (.call SubexpNegationSetup.preparedNegationProgram) n
      (state p regs x) mid := .call _ ht
  have hclear := TupleProgram.clear_eval (8 : Fin 9) (0 : Fin 8) 1 mid
  have hfinish : (⟨readRegs mid.regs 0 1 none, clearStacks 8 mid.stacks⟩ : Data) =
      state p (readRegs r 0 1 none) (-x) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [ mid, SubexpNegationProgram.state,
        SubexpNegationProgram.extendEight, ModularRingPrograms.extendSeven,
        ModularDivisionPrograms.resting, ModularDivisionPrograms.seven, clearStacks]
  rw [hfinish] at hclear
  have hmidlen : (mid.stacks 8).length = width p := hcl
  refine ⟨n + (2 * width p + 3), ?_, readRegs r 0 1 none, ?_⟩
  · nlinarith only [hn, Nat.zero_le (width p)]
  · simpa only [command, hmidlen] using hcall.seq hclear

def program := compiled command 0 0

theorem program_runsIn (regs : Fin 8 → Bool) (x : ZMod p) :
    ∃ regs', RunsIn program (6073 * (width p + 1)^2 + 1)
      ((state p regs x).withPC (some program.entry))
      ((state p regs' (-x)).withPC none) := by
  obtain ⟨n, hn, r, ht⟩ := command_eval p regs x
  exact ⟨r, n + 1, by omega, compiled_halt_trace ht 0 0⟩

end SubexponentialSAT.Subexp.MatrixNegationProgram

end OAI.Algorithms
