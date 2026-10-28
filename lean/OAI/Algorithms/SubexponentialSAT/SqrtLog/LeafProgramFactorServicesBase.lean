import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactor
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Exact framing tools for the fixed wide indicator and marked-clause calls.
The functions below only describe states; executable code remains Factor's
already defined finite service tables. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorServices
open SubexponentialSAT BitProgram StructuredCalls
open HashCircuitProgram HashCircuitProgram.Native

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff

abbrev Data := State 40 768

def high (map : Fin 96 → Fin 768) (a : Data) : Fin 40 → List Bool :=
  fun i => a.stacks (map (Memory.highPort i))

def readied (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 true) 2 false,a.stacks⟩

def indicatorScratch : List (Fin 96) :=
  [56,57,58,59,60,61,63,65,66,67,68,70,79,80,81,82,83,84,85,86,87,89,90,91,92,93,94,95]
def clauseScratch : List (Fin 96) := [56,57,58,59,60,61,67,70]

noncomputable def indicatorFinished (a : Data) (rr : Fin 8 → Bool) (hash result : List Bool) : Data :=
  ⟨Function.extend Factor.nativeRegisters rr (readied a).regs,
    Function.update (Function.update (Function.update a.stacks 64 []) 67 result) 68 hash⟩
noncomputable def clauseFinished (a : Data) (rr : Fin 8 → Bool) (result : List Bool) : Data :=
  ⟨Function.extend Clause.callerRegisters rr a.regs,
    Function.update (Function.update a.stacks 63 []) 67 result⟩

theorem ready_eval (a : Data) : Eval Factor.indicatorReady 3 a (readied a) := by
  let a1 : Data := ⟨Function.update a.regs 0 false,a.stacks⟩
  let a2 : Data := ⟨Function.update a1.regs 1 true,a.stacks⟩
  have h1 : Eval (.base (.atom (.set 0 false))) 1 a a1 :=
    Eval.base (StructuredProgram.Eval.atom _ _)
  have h2 : Eval (.base (.atom (.set 1 true))) 1 a1 a2 :=
    Eval.base (StructuredProgram.Eval.atom _ _)
  have h3 : Eval (.base (.atom (.set 2 false))) 1 a2 (readied a) :=
    Eval.base (StructuredProgram.Eval.atom _ _)
  exact h1.seq (h2.seq h3)

theorem input_tapes (map : Fin 96 → Fin 768) (a : Data) (lo : Fin 56 → List Bool)
    (hlow : ∀ i, a.stacks (map (Memory.lowPort i))=lo i) :
    Memory.tapes lo (high map a) = a.stacks ∘ map := by
  funext i
  induction i using (Fin.addCases (m:=56) (n:=40)) with
  | left i =>
    change Memory.tapes lo (high map a) (Memory.lowPort i)=a.stacks (map (Memory.lowPort i))
    simpa only [Memory.tapes_low] using (hlow i).symm
  | right i =>
    change Memory.tapes lo (high map a) (Memory.highPort i)=a.stacks (map (Memory.highPort i))
    simp only [Memory.tapes_high,high]

theorem row_high_input (map : Fin 96 → Fin 768) (a : Data) (source : List Bool)
    (hs : a.stacks (map 64)=source)
    (hw : ∀ i∈indicatorScratch,a.stacks (map i)=[]) :
    Row.recordHigh (high map a) [] source [] = high map a := by
  funext i
  fin_cases i <;> simp [Row.recordHigh,Row.baseHigh,HashCircuitProgram.Native.Clause.baseHigh,literalHigh,high]
  all_goals first | exact hs | exact hs.symm | (apply hw; decide)

theorem clause_high_input (map : Fin 96 → Fin 768) (a : Data) (source : List Bool)
    (hs : a.stacks (map 63)=source)
    (hw : ∀ i∈clauseScratch,a.stacks (map i)=[]) :
    HashCircuitProgram.Native.Clause.recordHigh (high map a) [] source [] = high map a := by
  funext i
  fin_cases i <;> simp [HashCircuitProgram.Native.Clause.recordHigh,
    HashCircuitProgram.Native.Clause.baseHigh,literalHigh,high]
  all_goals first | exact hs | exact hs.symm | (apply hw; decide)

theorem row_output_tapes (lo : Fin 56 → List Bool) (h : Fin 40 → List Bool)
    (source hash result : List Bool) :
    Memory.tapes lo (Function.update (Row.recordHigh h hash [] []) 11 result) =
      Function.update (Function.update (Function.update
        (Memory.tapes lo (Row.recordHigh h [] source [])) 64 []) 67 result) 68 hash := by
  change _ = Function.update (Function.update (Function.update
    (Memory.tapes lo (Row.recordHigh h [] source [])) (Memory.highPort 8) [])
      (Memory.highPort 11) result) (Memory.highPort 12) hash
  rw [Memory.update_high,Memory.update_high,Memory.update_high]
  apply congrArg (Memory.tapes lo)
  funext i
  fin_cases i <;> simp [Row.recordHigh,Row.baseHigh,HashCircuitProgram.Native.Clause.baseHigh,literalHigh]

theorem clause_output_tapes (lo : Fin 56 → List Bool) (h : Fin 40 → List Bool)
    (source result : List Bool) :
    Memory.tapes lo (HashCircuitProgram.Native.Clause.recordHigh h result [] []) =
      Function.update (Function.update
        (Memory.tapes lo (HashCircuitProgram.Native.Clause.recordHigh h [] source [])) 63 []) 67 result := by
  change _ = Function.update (Function.update
    (Memory.tapes lo (HashCircuitProgram.Native.Clause.recordHigh h [] source [])) (Memory.highPort 7) [])
      (Memory.highPort 11) result
  rw [Memory.update_high,Memory.update_high]
  apply congrArg (Memory.tapes lo)
  funext i
  fin_cases i <;> simp [HashCircuitProgram.Native.Clause.recordHigh,HashCircuitProgram.Native.Clause.baseHigh,literalHigh]

theorem extend_project (map : Fin 96 → Fin 768) (hm : Function.Injective map) (a : Data) :
    Function.extend map (a.stacks ∘ map) a.stacks = a.stacks := by
  exact congrArg (fun b : Data => b.stacks)
    (embedState_project Factor.nativeRegisters map a Factor.nativeRegisters_injective hm)

theorem indicator_embed (a : Data) (rr : Fin 8 → Bool) (lo : Fin 56 → List Bool)
    (source hash result : List Bool)
    (hi : Memory.tapes lo (Row.recordHigh (high Factor.indicatorStacks a) [] source [])=
      a.stacks ∘ Factor.indicatorStacks) :
    embedState Factor.nativeRegisters Factor.indicatorStacks (readied a)
      (Memory.state rr lo (Function.update (Row.recordHigh (high Factor.indicatorStacks a) hash [] []) 11 result)) =
      indicatorFinished a rr hash result := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · change Function.extend Factor.indicatorStacks
      (Memory.tapes lo (Function.update (Row.recordHigh (high Factor.indicatorStacks a) hash [] []) 11 result))
      a.stacks = _
    rw [row_output_tapes lo _ source hash result,hi]
    rw [ProgramLinking.extend_update Factor.indicatorStacks_injective,
      ProgramLinking.extend_update Factor.indicatorStacks_injective,
      ProgramLinking.extend_update Factor.indicatorStacks_injective,extend_project]
    rfl
    exact Factor.indicatorStacks_injective

theorem clause_embed (a : Data) (rr : Fin 8 → Bool) (lo : Fin 56 → List Bool)
    (source result : List Bool)
    (hi : Memory.tapes lo (HashCircuitProgram.Native.Clause.recordHigh (high Clause.callerStacks a) [] source [])=
      a.stacks ∘ Clause.callerStacks) :
    embedState Clause.callerRegisters Clause.callerStacks a
      (Memory.state rr lo (HashCircuitProgram.Native.Clause.recordHigh (high Clause.callerStacks a) result [] [])) =
      clauseFinished a rr result := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · change Function.extend Clause.callerStacks
      (Memory.tapes lo (HashCircuitProgram.Native.Clause.recordHigh (high Clause.callerStacks a) result [] []))
      a.stacks = _
    rw [clause_output_tapes lo _ source result,hi]
    have hinj : Function.Injective Clause.callerStacks := Fin.castAdd_injective 96 672
    rw [ProgramLinking.extend_update hinj,
      ProgramLinking.extend_update hinj,extend_project]
    rfl
    exact Fin.castAdd_injective 96 672

end SubexponentialSAT.SqrtLog.LeafProgram.FactorServices

end OAI.Algorithms
