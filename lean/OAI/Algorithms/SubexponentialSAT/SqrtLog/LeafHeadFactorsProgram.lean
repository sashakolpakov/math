import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeBitProgram
import OAI.Algorithms.SubexponentialSAT.SubexpHeadColorProgram
import OAI.Algorithms.SubexponentialSAT.ProgramEncoding

namespace OAI.Algorithms

/-! Factor head selection uses the full original table and a paid ambient offset. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 64
abbrev Code := Cmd 16 64
abbrev unary (n : ℕ) := List.replicate n true
abbrev zeros (n : ℕ) := List.replicate n false
abbrev copy := Subexp.SupportSelectionProgram.copy
abbrev record := Subexp.SupportSelectionProgram.record
abbrev supportPrefix := Subexp.SupportSelectionProgram.supportPrefix

def wordRegs : Fin 5 → Fin 16 := Fin.castAdd 11
def wordPorts : Fin 10 → Fin 64 := ![33,40,38,16,17,36,18,19,20,21]
theorem wordRegs_injective : Function.Injective wordRegs := Fin.castAdd_injective _ _
theorem wordPorts_injective : Function.Injective wordPorts := by decide

def lookup : Code := liftCommand SubexpHeadColorProgram.select 0 5 wordRegs wordPorts

def selected (d : Data) (word : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,Function.update d.stacks 36 word⟩

def lookupCost (j W : ℕ) := j*(14*W+17)+15*W+22

theorem lookup_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hs : d.stacks 33=earlier.flatten++(word++rest))
    (hi : (d.stacks 40).length=earlier.length)
    (hw : word.length=(d.stacks 38).length)
    (hr : ∀ row ∈ earlier,row.length=(d.stacks 38).length)
    (hc : ∀ i ∈ ([16,17,36,18,19,20,21] : List (Fin 64)),d.stacks i=[]) :
    Eval lookup (lookupCost earlier.length (d.stacks 38).length) d (selected d word) := by
  let a := projectState wordRegs wordPorts d
  have hclean : SubexpHeadColorProgram.Clean a := by
    intro i hi
    fin_cases i <;> simp_all [a,projectState,wordPorts]
  have h := SubexpHeadColorProgram.select_eval a earlier word rest
    (by simpa [a,projectState,wordPorts] using hs)
    (by simpa [a,projectState,wordPorts] using hi)
    (by simpa [a,projectState,wordPorts] using hw)
    (by simpa [a,projectState,wordPorts] using hr) hclean
  have hl := eval_liftCommand_from_state SubexpHeadColorProgram.select 0 5 wordRegs wordPorts
    d wordRegs_injective wordPorts_injective h
  have hz : embedState wordRegs wordPorts d (SubexpHeadColorProgram.selected a word)=
      selected d word := by
    apply embedState_eq_of_ports wordRegs wordPorts d _ _ wordRegs_injective wordPorts_injective
    · intro i; fin_cases i <;> simp [SubexpHeadColorProgram.selected,selected,a,projectState,wordRegs,readRegs]
    · intro i hi
      have h0 : i ≠ 0 := fun he => hi ⟨0,by simpa [wordRegs] using he.symm⟩
      have h1 : i ≠ 1 := fun he => hi ⟨1,by simpa [wordRegs] using he.symm⟩
      simp [selected,readRegs,h0,h1]
    · intro i; fin_cases i <;>
        simp [SubexpHeadColorProgram.selected,selected,a,projectState,wordPorts]
    · intro i hi
      have hn : i ≠ 36 := fun he => hi ⟨5,by simpa [wordPorts] using he.symm⟩
      simp [selected,hn]
  rw [hz] at hl
  simpa [lookup,lookupCost,a,projectState,wordPorts,Nat.add_assoc] using hl


end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
