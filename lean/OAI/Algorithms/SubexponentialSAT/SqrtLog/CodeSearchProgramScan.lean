import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramCompare
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Framed support and unary comparison as framed subroutine calls. The port
maps are fixed finite maps; the lengths being scanned occur only on tapes. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev ScanState := State 8 18

def scanRegisters : Fin 4 → Fin 8 := Fin.castAdd 4
def scanStacks (input output : Fin 18) : Fin 2 → Fin 18 := ![input,output]

theorem scanRegisters_injective : Function.Injective scanRegisters :=
  Fin.castAdd_injective _ _

theorem scanStacks_injective (input output : Fin 18) (h : input ≠ output) :
    Function.Injective (scanStacks input output) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [scanStacks]

abbrev supportAt (input output : Fin 18) : Cmd 8 18 :=
  .call (ProgramLinking.liftProgram framedSupportProgram scanRegisters
    (scanStacks input output))

abbrev lessAt (left right : Fin 18) : Cmd 8 18 :=
  .call (ProgramLinking.liftProgram unaryLessProgram scanRegisters (scanStacks left right))

theorem supportAt_eval (input output : Fin 18) (hne : input ≠ output)
    (cells : List (Bool × Bool)) (base : ScanState)
    (hin : base.stacks input = framedCellStream cells)
    (hout : base.stacks output = []) :
    ∃ (n : ℕ) (next : ScanState), n ≤ 10 * cells.length + 3 ∧
      Eval (supportAt input output) n base next ∧
      next.stacks input = [] ∧
      next.stacks output = List.replicate (cellWeight cells) true ∧
      (∀ i : Fin 8, 4 ≤ i.val → next.regs i = base.regs i) ∧
      (∀ j, j ≠ input → j ≠ output → next.stacks j = base.stacks j) := by
  obtain ⟨rf, ht⟩ := framedSupport_trace cells (base.regs ∘ scanRegisters) []
  let a : State 4 2 := ⟨base.regs ∘ scanRegisters, ![framedCellStream cells, []]⟩
  let b : State 4 2 := ⟨rf, ![[], List.replicate (cellWeight cells) true]⟩
  have ha : embedState scanRegisters (scanStacks input output) base a = base := by
    apply SubexpScanPrimitives.embedState_eq _ _ scanRegisters_injective
      (scanStacks_injective _ _ hne)
    · intro i; rfl
    · intro i; fin_cases i <;> simpa [a, scanStacks] using (by assumption)
    · intros; rfl
    · intros; rfl
  have htrace : Trace framedSupportProgram (framedCellCost cells)
      (a.withPC (some framedSupportProgram.entry)) (b.withPC none) := by
    simpa [a, b, framedSupportCfg] using ht
  have he := eval_call_lifted framedSupportProgram scanRegisters (scanStacks input output)
    base scanRegisters_injective (scanStacks_injective _ _ hne) htrace
  rw [ha] at he
  refine ⟨framedCellCost cells, _, framedCellCost_le cells, he, ?_, ?_, ?_, ?_⟩
  · exact embedState_stack _ _ base b (scanStacks_injective _ _ hne) 0
  · exact embedState_stack _ _ base b (scanStacks_injective _ _ hne) 1
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hval := congrArg Fin.val hj
    simp [scanRegisters] at hval
    omega
  · intro j hi ho
    apply embedState_stack_frame
    rintro ⟨i, hij⟩
    fin_cases i <;> simp_all [scanStacks]

theorem lessAt_eval (left right : Fin 18) (hne : left ≠ right)
    (base : ScanState) :
    ∃ (n : ℕ) (next : ScanState), n ≤ 4 * (base.stacks left).length + 6 ∧
      Eval (lessAt left right) n base next ∧
      next.regs 3 = decide ((base.stacks left).length < (base.stacks right).length) ∧
      (∀ i : Fin 8, 4 ≤ i.val → next.regs i = base.regs i) ∧
      (∀ j, j ≠ left → j ≠ right → next.stacks j = base.stacks j) := by
  obtain ⟨n, rf, l, r, hn, ht, hf⟩ :=
    unaryLess_trace (base.stacks left) (base.stacks right) (base.regs ∘ scanRegisters)
  let a : State 4 2 := ⟨base.regs ∘ scanRegisters, ![base.stacks left, base.stacks right]⟩
  let b : State 4 2 := ⟨rf, ![l,r]⟩
  have ha : embedState scanRegisters (scanStacks left right) base a = base := by
    apply SubexpScanPrimitives.embedState_eq _ _ scanRegisters_injective
      (scanStacks_injective _ _ hne)
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have htrace : Trace unaryLessProgram n (a.withPC (some unaryLessProgram.entry))
      (b.withPC none) := by simpa [a, b, unaryLessCfg] using ht
  have he := eval_call_lifted unaryLessProgram scanRegisters (scanStacks left right)
    base scanRegisters_injective (scanStacks_injective _ _ hne) htrace
  rw [ha] at he
  refine ⟨n, _, hn, he, ?_, ?_, ?_⟩
  · exact (embedState_register _ _ base b scanRegisters_injective 3).trans hf
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hval := congrArg Fin.val hj
    simp [scanRegisters] at hval
    omega
  · intro j hi ho
    apply embedState_stack_frame
    rintro ⟨i, hij⟩
    fin_cases i <;> simp_all [scanStacks]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
