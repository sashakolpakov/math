import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeFilter
import OAI.Algorithms.SubexponentialSAT.SubexpMachineNodeOrder
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation

namespace OAI.Algorithms

/-!
# One fixed program for generating the nonzero quartic-node word table

The input is the explicit framed scalar alphabet. Eight real instructions
install the constant depth four. The tuple generator builds all four-word
records, and the verified record filter removes exactly the zero record.
No tuple array or node list is supplied as an input to this program.
-/

namespace SubexponentialSAT.SubexpNodeGeneration

open BitProgram StructuredCalls Subexp.TupleProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)

abbrev filterRegisters (i : Fin 6) : Fin 10 := ⟨i.val, by omega⟩
abbrev filterStacks : Fin 5 → Fin 9 := ![0, 2, 3, 4, 5]

theorem filterRegisters_injective : Function.Injective filterRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 10 => x.val) h)

theorem filterStacks_injective : Function.Injective filterStacks := by decide

abbrev generateFilter : Cmd 10 9 :=
  .seq (.call Subexp.TupleProgram.generateProgram)
    (.call (ProgramLinking.liftProgram SubexpNodeFilter.program
      filterRegisters filterStacks))

theorem generateFilter_eval (alphabet : List (List Bool)) (depth : List Bool)
    (guard : Bool) (a : State 10 9) (ha : outerInvariant alphabet depth guard a)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h5 : a.stacks 5 = []) :
    ∃ n next, n ≤ powerCost alphabet depth.length [[]] +
        SubexpNodeFilter.budget (powerRows alphabet depth.length [[]]) + 10 ∧
      next.stacks 5 = ProgramEncoding.encodeRecords
        (((powerRows alphabet depth.length [[]]).filter PositiveWordProgram.positive).reverse) ∧
      Eval generateFilter n a next := by
  obtain ⟨b, hb, n1, hn1, ht1⟩ :=
    generateProgram_runsIn alphabet depth guard a ha h0 h2 h5
  let small := restrictState filterRegisters filterStacks b
  have hi : SubexpNodeFilter.invariant small := by
    constructor
    · simpa [small, restrictState, filterStacks] using hb.1.2.1
    · simpa [small, restrictState, filterStacks] using hb.1.2.2.1
  have hsmall0 : small.stacks 0 =
      ProgramEncoding.encodeRecords (powerRows alphabet depth.length [[]]) := by
    simpa [small, restrictState, filterStacks] using hb.2.1
  have hsmall1 : small.stacks 1 = [] := by
    simpa [small, restrictState, filterStacks] using hb.2.2.1
  have hsmall4 : small.stacks 4 = ProgramEncoding.encodeRecords [] := by
    simpa [small, restrictState, filterStacks, ProgramEncoding.encodeRecords,
      Encoding.encodeList] using hb.2.2.2
  obtain ⟨c, _, _, _, hout, hrun⟩ := SubexpNodeFilter.program_runsIn
    (powerRows alphabet depth.length [[]]) [] small hi hsmall0 hsmall1 hsmall4
  obtain ⟨n2, hn2, ht2⟩ := lifted_call SubexpNodeFilter.program filterRegisters filterStacks
    filterRegisters_injective filterStacks_injective b c _ hrun
  refine ⟨n1 + n2, embedState filterRegisters filterStacks b c, by omega, ?_, ?_⟩
  · have hs := embedState_stack filterRegisters filterStacks b c filterStacks_injective 4
    change (embedState filterRegisters filterStacks b c).stacks 5 = c.stacks 4 at hs
    exact hs.trans (by simpa using hout)
  · exact (Eval.call _ ht1).seq ht2

abbrev depthFour : Cmd 10 9 :=
  .seq (pushConst 8 6 false) (.seq (pushConst 8 6 false)
    (.seq (pushConst 8 6 false) (pushConst 8 6 false)))

def inputState (alphabet : List (List Bool)) : State 10 9 :=
  ⟨fun _ => false, fun i => if i = 1 then ProgramEncoding.encodeRecords alphabet else []⟩

def depthState (alphabet : List (List Bool)) : State 10 9 :=
  ⟨fun _ => false, fun i => if i = 1 then ProgramEncoding.encodeRecords alphabet
    else if i = 8 then [false, false, false, false] else []⟩

theorem depthFour_eval (alphabet : List (List Bool)) :
    Eval depthFour 8 (inputState alphabet) (depthState alphabet) := by
  let a := inputState alphabet
  let b := pushedState 8 6 false a
  let c := pushedState 8 6 false b
  let d := pushedState 8 6 false c
  let e := pushedState 8 6 false d
  have he : e = depthState alphabet := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [d, c, b, a, inputState]
    · funext i
      fin_cases i <;> simp [d, c, b, a, inputState]
  rw [← he]
  exact (pushConst_eval 8 6 false a).seq ((pushConst_eval 8 6 false b).seq
    ((pushConst_eval 8 6 false c).seq (pushConst_eval 8 6 false d)))

abbrev cmd : Cmd 10 9 := .seq depthFour generateFilter
def program := StructuredCalls.compiled cmd 1 5

def generatedWords (alphabet : List (List Bool)) : List (List Bool) :=
  ((powerRows alphabet 4 [[]]).filter PositiveWordProgram.positive).reverse

def cost (alphabet : List (List Bool)) : ℕ :=
  powerCost alphabet 4 [[]] + SubexpNodeFilter.budget (powerRows alphabet 4 [[]]) + 19

/-- The complete finite program starts with only the supplied scalar alphabet. -/
theorem program_runsIn (alphabet : List (List Bool)) :
    ∃ next : State 10 9, next.stacks 5 = ProgramEncoding.encodeRecords (generatedWords alphabet) ∧
      RunsIn program (cost alphabet)
        (initial program (ProgramEncoding.encodeRecords alphabet)) (next.withPC none) := by
  have hi : outerInvariant alphabet [false, false, false, false] false (depthState alphabet) := by
    simp [outerInvariant, depthState]
  obtain ⟨n, next, hn, hout, he⟩ := generateFilter_eval alphabet
    [false, false, false, false] false (depthState alphabet) hi
    (by simp [depthState]) (by simp [depthState]) (by simp [depthState])
  refine ⟨next, hout, 8 + n + 1, ?_, ?_⟩
  · change n ≤ powerCost alphabet 4 [[]] +
      SubexpNodeFilter.budget (powerRows alphabet 4 [[]]) + 10 at hn
    unfold cost
    omega
  · exact StructuredCalls.compiled_halt_trace ((depthFour_eval alphabet).seq he) 1 5

/-- The primitive compiler preserves the actual generated word table. -/
theorem primitive_runsIn (alphabet : List (List Bool)) :
    ∃ next : State 10 9, next.stacks 5 = ProgramEncoding.encodeRecords (generatedWords alphabet) ∧
      Computation.RunsIn (primitive program).step (primitiveOverhead program * cost alphabet)
        (primitiveCfg program (initial program (ProgramEncoding.encodeRecords alphabet)))
        (primitiveCfg program (next.withPC none)) := by
  obtain ⟨next, hout, hr⟩ := program_runsIn alphabet
  exact ⟨next, hout, primitive_execution program hr⟩

theorem selected_program_runsIn (p : ℕ) [Fact p.Prime] :
    ∃ next : State 10 9,
      next.stacks 5 = ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p) ∧
      RunsIn program
        (cost ((QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block))
        (initial program (ProgramEncoding.encodeRecords
          ((QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block)))
        (next.withPC none) :=
  program_runsIn ((QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block)

end SubexponentialSAT.SubexpNodeGeneration

end OAI.Algorithms
