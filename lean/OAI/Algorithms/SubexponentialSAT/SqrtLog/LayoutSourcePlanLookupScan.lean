import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookupBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

namespace Scan

def register : Fin 5 → Fin 16 := Fin.castAdd 11
def stack : Fin 7 → Fin 12 := ![6,3,8,9,10,11,4]
theorem register_injective : Function.Injective register := Fin.castAdd_injective _ _
theorem stack_injective : Function.Injective stack := by decide

def command : Code := liftCommand SubexpNodeIndexProgram.Internal.command 0 6 register stack

theorem command_eval (regs : Fin 16 → Bool) (literal ambient factor query : List Bool)
    (nodes : List (List Bool)) :
    ∃ n ≤ SubexpNodeIndexProgram.Internal.budget query nodes, ∃ rf,
      Eval command n
        (data regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
          [] [] query [] [] [] [] [])
        (data rf literal ambient factor (ProgramEncoding.encodeRecords nodes)
          (List.replicate (nodes.idxOf query) true) [] query [] [] [] [] []) := by
  let d := data regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
    [] [] query [] [] [] [] []
  let rr := fun i => regs (register i)
  obtain ⟨n,hn,rs,he⟩ := SubexpNodeIndexProgram.Internal.command_eval rr query nodes
  have ha : projectState register stack d =
      SubexpNodeIndexProgram.Internal.state rr query
        (ProgramEncoding.encodeRecords nodes) [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [←ha] at he
  have hh := eval_liftCommand_from_state SubexpNodeIndexProgram.Internal.command 0 6
    register stack d register_injective stack_injective he
  let e := embedState register stack d
    (SubexpNodeIndexProgram.Internal.state rs query (ProgramEncoding.encodeRecords nodes)
      [] [] [] [] (List.replicate (nodes.idxOf query) true))
  have hb : e = data e.regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
      (List.replicate (nodes.idxOf query) true) [] query [] [] [] [] [] := by
    apply embedState_eq register stack register_injective stack_injective
    · intro i
      exact embedState_register register stack d _ register_injective i
    · intro i; fin_cases i <;> rfl
    · intro i hi
      exact embedState_register_frame register stack d _ i hi
    · intro i hi
      fin_cases i <;> first
        | rfl
        | exact False.elim (hi ⟨0,rfl⟩)
        | exact False.elim (hi ⟨1,rfl⟩)
        | exact False.elim (hi ⟨2,rfl⟩)
        | exact False.elim (hi ⟨3,rfl⟩)
        | exact False.elim (hi ⟨4,rfl⟩)
        | exact False.elim (hi ⟨5,rfl⟩)
        | exact False.elim (hi ⟨6,rfl⟩)
  refine ⟨n+1,hn,e.regs,?_⟩
  change Eval command (n+1) d e at hh
  rw [hb] at hh
  exact hh

end Scan
end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
