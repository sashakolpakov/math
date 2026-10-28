import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticPowerCore
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatMul

namespace OAI.Algorithms

/-!
# Actual fixed-control quartic modular exponentiation

The exponent is a little-endian Boolean stack. Each iteration runs the actual
fixed-width quartic multiplication table, so intermediate operands always use
four words of the supplied coefficient width. The base, exponent, unit,
modulus, reduction cache, and width word are preserved byte for byte.

Ports 66, 73, and 74 hold the modulus, reduction quartet, and width word.
Ports 77, 78, and 79 hold the base, binary exponent, and encoded one.
Port 80 is the fresh output; ports 81 and 82 are empty countdown workspace.
Every remaining port in 0..76 is initially and finally empty.
-/

namespace SubexponentialSAT.SubexpQuarticPowerProgram

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing

abbrev Data := SubexpQuarticPowerCore.Data
abbrev Regs := SubexpQuarticPowerCore.Regs
abbrev native := SubexpQuarticPowerCore.native
abbrev cleanNative := SubexpQuarticPowerCore.cleanNative
abbrev initial := @SubexpQuarticPowerCore.initial
abbrev runtimeBound := SubexpQuarticPowerCore.runtimeBound

abbrev command : Cmd 8 83 :=
  SubexpQuarticPowerCore.command SubexpQuarticFlatMul.program

/-- This single finite table works for every prime, precision, and exponent. -/
abbrev program : Program 8 83 (size command + 1) :=
  SubexpQuarticPowerCore.program SubexpQuarticFlatMul.program

theorem program_labels : size command + 1 = 9038 := by
  rw [command, SubexpQuarticPowerCore.program_labels, SubexpQuarticFlatMul.program_size]

private theorem multiplication_spec :
    SubexpQuarticPowerCore.MulSpec SubexpQuarticFlatMul.program := by
  intro p μ hp M t a b width hw r
  exact SubexpQuarticFlatMul.program_run p μ M t a b width hw r

/-- A common input bound gives a cubic instruction bound. -/
theorem runtimeBound_le (B : ℕ) (exponent : List Bool) (W : ℕ)
    (hB : B ≤ W) (hE : exponent.length ≤ W)
    (hN : BinaryArithmetic.toNat exponent ≤ W) :
    runtimeBound B exponent ≤ 500000 * (W + 1)^3 :=
  SubexpQuarticPowerCore.runtimeBound_le B exponent W hB hE hN

/-- Caller-oriented exact frame theorem: the output stack is the only stack
changed by the complete exponentiation command. -/
theorem command_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t a unit : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (width : List Bool) (hw : width.length = baseWidth p μ) (d : Data)
    (hnative : ∀ i, d.stacks (native i) = cleanNative M.bits (SubexpQuarticFlatMul.flat t) width i)
    (ha : d.stacks 77 = SubexpQuarticFlatMul.flat a)
    (hunit : d.stacks 79 = SubexpQuarticFlatMul.flat unit)
    (h80 : d.stacks 80 = []) (h81 : d.stacks 81 = []) (h82 : d.stacks 82 = []) :
    ∃ n rf b, Eval command n d
        ⟨rf, Function.update d.stacks 80 (SubexpQuarticFlatMul.flat b)⟩ ∧
      quotientDenote c (b.map (wordValue p μ)) =
        quotientDenote c (a.map (wordValue p μ)) ^ BinaryArithmetic.toNat (d.stacks 78) ∧
      n + 1 ≤ runtimeBound (baseWidth p μ) (d.stacks 78) :=
  SubexpQuarticPowerCore.command_eval SubexpQuarticFlatMul.program multiplication_spec
    p μ M c t a unit ht hu width hw d hnative ha hunit h80 h81 h82

/-- Complete finite-program trace with exactly four fixed-width output words. -/
theorem run_value (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t a unit : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (width exponent : List Bool) (hw : width.length = baseWidth p μ) (r : Regs) :
    ∃ rf b, quotientDenote c (b.map (wordValue p μ)) =
        quotientDenote c (a.map (wordValue p μ)) ^ BinaryArithmetic.toNat exponent ∧
      (SubexpQuarticFlatMul.flat b).length = 4 * baseWidth p μ ∧
      RunsIn program (runtimeBound (baseWidth p μ) exponent)
        ((initial r M.bits width exponent t a unit).withPC (some program.entry))
        ((⟨rf, Function.update (initial r M.bits width exponent t a unit).stacks
          80 (SubexpQuarticFlatMul.flat b)⟩ : Data).withPC none) := by
  obtain ⟨rf, b, hv, hr⟩ := SubexpQuarticPowerCore.run_value
    SubexpQuarticFlatMul.program multiplication_spec p μ M c t a unit ht hu width exponent hw r
  exact ⟨rf, b, hv, SubexpQuarticFlatMul.flat_length b, hr⟩

abbrev callAt {S : ℕ} (port : Fin 83 ↪ Fin S) : Cmd 8 S :=
  SubexpQuarticPowerCore.callAt SubexpQuarticFlatMul.program port

/-- The complete power program can be placed in any larger fixed stack bank.
Every stack except the assigned output port is preserved, including the frame
outside the 83 ports. -/
theorem callAt_eval {S : ℕ} (port : Fin 83 ↪ Fin S)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t a unit : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (d : StructuredProgram.State 8 S)
    (hnative : ∀ i, d.stacks (port (native i)) =
      cleanNative M.bits (SubexpQuarticFlatMul.flat t) width i)
    (ha : d.stacks (port 77) = SubexpQuarticFlatMul.flat a)
    (hunit : d.stacks (port 79) = SubexpQuarticFlatMul.flat unit)
    (h80 : d.stacks (port 80) = []) (h81 : d.stacks (port 81) = [])
    (h82 : d.stacks (port 82) = []) :
    ∃ n rf b, Eval (callAt port) n d
        ⟨rf, Function.update d.stacks (port 80) (SubexpQuarticFlatMul.flat b)⟩ ∧
      quotientDenote c (b.map (wordValue p μ)) =
        quotientDenote c (a.map (wordValue p μ)) ^ BinaryArithmetic.toNat (d.stacks (port 78)) ∧
      n ≤ runtimeBound (baseWidth p μ) (d.stacks (port 78)) :=
  SubexpQuarticPowerCore.callAt_eval SubexpQuarticFlatMul.program multiplication_spec port
    p μ M c t a unit ht hu width hw d hnative ha hunit h80 h81 h82

end SubexponentialSAT.SubexpQuarticPowerProgram

end OAI.Algorithms
