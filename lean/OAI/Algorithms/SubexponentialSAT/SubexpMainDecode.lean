import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram
import OAI.Algorithms.SubexponentialSAT.SubexpFlatCount

namespace OAI.Algorithms

/-! The concrete flat-coefficient decoder installed in the main caller ABI. -/

namespace SubexponentialSAT.SubexpMainDecode

open StructuredCalls SubexpMainProgram

/-- Decoder scratch is in the low workspace. Its polynomial/answer, modulus,
and width occupy the agreed persistent ports. -/
def scratch (es : ℕ) (i : Fin 8) : Fin (totalStacks es) :=
  ⟨i.val, by have := i.isLt; dsimp [totalStacks, workStacks]; omega⟩

def stackMap (es : ℕ) : Fin 8 → Fin (totalStacks es) :=
  ![persistent es 10, scratch es 1, scratch es 2, scratch es 3,
    scratch es 4, persistent es 12, scratch es 6, persistent es 13]

theorem stackMap_injective (es : ℕ) : Function.Injective (stackMap es) := by
  intro a b h
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> try rfl
  all_goals norm_num [stackMap, scratch, persistent, workStacks] at hv

def procedure (er es : ℕ) : Procedure er es where
  registers := 8
  stackCount := 8
  labels := size SubexpFlatCount.command + 1
  program := SubexpFlatCount.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro a b h
    have hv := congrArg Fin.val h
    exact Fin.ext hv⟩
  stack := ⟨stackMap es, stackMap_injective es⟩

def localResult (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    StructuredProgram.State 8 8 :=
  ⟨regs, SubexpFlatCount.store (SubexpFlatCount.output modulus word) modulus [] width⟩

/-- The exposed bit is produced by the actual remainder/positivity decoder. -/
theorem installed_head {er es : ℕ} (a : MainState er es) (regs : Fin 8 → Bool)
    (modulus width word : List Bool) :
    (((procedure er es).install a (localResult regs modulus width word)).stacks
      (persistent es 10)).head? = some (SubexpDecodeProgram.answer modulus word) := by
  have h := embedState_stack (procedure er es).registerMap (procedure er es).stack
    a (localResult regs modulus width word) (procedure er es).stack.injective (0 : Fin 8)
  change ((embedState (procedure er es).registerMap (procedure er es).stack a
    (localResult regs modulus width word)).stacks ((procedure er es).stack (0 : Fin 8))).head? = _
  rw [h]
  rfl

theorem installed_frame {er es : ℕ} (a : MainState er es)
    (result : StructuredProgram.State 8 8) (j : Fin 32)
    (hj10 : j ≠ 10) (hj12 : j ≠ 12) (hj13 : j ≠ 13) :
    ((procedure er es).install a result).stacks (persistent es j) =
      a.stacks (persistent es j) := by
  have h10 : j.val ≠ 10 := fun h => hj10 (Fin.ext h)
  have h12 : j.val ≠ 12 := fun h => hj12 (Fin.ext h)
  have h13 : j.val ≠ 13 := fun h => hj13 (Fin.ext h)
  apply embedState_stack_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  fin_cases i
  · change 128 + es + 10 = 128 + es + j.val at hv
    apply hj10
    apply Fin.ext
    omega
  · change 1 = 128 + es + j.val at hv
    omega
  · change 2 = 128 + es + j.val at hv
    omega
  · change 3 = 128 + es + j.val at hv
    omega
  · change 4 = 128 + es + j.val at hv
    omega
  · change 128 + es + 12 = 128 + es + j.val at hv
    apply hj12
    apply Fin.ext
    omega
  · change 6 = 128 + es + j.val at hv
    omega
  · change 128 + es + 13 = 128 + es + j.val at hv
    apply hj13
    apply Fin.ext
    omega

/-- The caller supplies the concrete encoded flat polynomial, modulus, width,
and empty local work ports. The theorem supplies the exact lifted execution;
it has no premise postulating a decoder algorithm or its cost. -/
theorem execution {er es B : ℕ} (hB : 0 < B)
    (P : List (SubexpFlatCount.Code B)) (a : MainState er es)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B)
    (ready : (procedure er es).project a =
      SubexpFlatCount.start regs modulus width (SubexpFlatCount.flatPolynomial P)) :
    ∃ (n : ℕ) (finalRegs : Fin 8 → Bool),
      n ≤ SubexpFlatCount.budget B modulus (SubexpFlatCount.flatPolynomial P) ∧
      Eval (procedure er es).invoke n a
        ((procedure er es).install a
          (localResult finalRegs modulus width (SubexpFlatCount.firstWord P))) := by
  obtain ⟨finalRegs, n, hn, ht⟩ := SubexpFlatCount.run hB P regs modulus width hwidth
  refine ⟨n, finalRegs, hn, ?_⟩
  apply Procedure.invoke_trace
  rw [ready]
  exact ht

end SubexponentialSAT.SubexpMainDecode

end OAI.Algorithms
