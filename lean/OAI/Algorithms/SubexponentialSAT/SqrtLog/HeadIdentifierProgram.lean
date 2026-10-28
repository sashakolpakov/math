import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SupportSelectionPrimitives
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeBitProgram
import OAI.Algorithms.SubexponentialSAT.SubexpHeadColorProgram
import OAI.Algorithms.SubexponentialSAT.ProgramEncoding

namespace OAI.Algorithms

/-! Physical head-identifier selection uses the original ambient word array.
No packing-coverage predicate participates in the scan. -/
namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 64
abbrev Code := Cmd 16 64
abbrev unary (n : ℕ) := List.replicate n true
abbrev zeros (n : ℕ) := List.replicate n false
abbrev copy := Subexp.SupportSelectionProgram.copy
abbrev record := Subexp.SupportSelectionProgram.record
abbrev supportPrefix := Subexp.SupportSelectionProgram.supportPrefix

def wordRegs : Fin 5 → Fin 16 := Fin.castAdd 11
def wordPorts : Fin 10 → Fin 64 := ![33,39,38,16,17,36,18,19,20,21]
theorem wordRegs_injective : Function.Injective wordRegs := Fin.castAdd_injective _ _
theorem wordPorts_injective : Function.Injective wordPorts := by decide

def lookup : Code := liftCommand SubexpHeadColorProgram.select 0 5 wordRegs wordPorts

def selected (d : Data) (word : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,Function.update d.stacks 36 word⟩

def lookupCost (j W : ℕ) := j*(14*W+17)+15*W+22

theorem lookup_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hs : d.stacks 33=earlier.flatten++(word++rest))
    (hi : (d.stacks 39).length=earlier.length)
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

def bitFlag (low : Bool) : Fin 16 := if low then 6 else 4
def bitSource (low : Bool) : Fin 64 := if low then 13 else 36
def bitRegs (low : Bool) : Fin 3 → Fin 16 := ![0,1,bitFlag low]
def bitPorts (low : Bool) : Fin 2 → Fin 64 := ![12,bitSource low]
theorem bitRegs_injective (low : Bool) : Function.Injective (bitRegs low) := by
  cases low <;> decide
theorem bitPorts_injective (low : Bool) : Function.Injective (bitPorts low) := by
  cases low <;> decide

def readBit (low : Bool) : Code :=
  .call (ProgramLinking.liftProgram Subexp.TypeBitProgram.program (bitRegs low) (bitPorts low))

def bitResult (d : Data) (low answer : Bool) : Data :=
  ⟨Function.update (readRegs d.regs 0 1 none) (bitFlag low) answer,
    Function.update (Function.update d.stacks 12 []) (bitSource low) []⟩

theorem readBit_eval (d : Data) (low : Bool) :
    Eval (readBit low)
      (Subexp.TypeBitProgram.cost (d.stacks 12) (d.stacks (bitSource low)))
      d (bitResult d low ((d.stacks (bitSource low)).getD (d.stacks 12).length false)) := by
  let a := projectState (bitRegs low) (bitPorts low) d
  let b : State 3 2 :=
    ⟨Subexp.TypeBitProgram.resultRegs ((d.stacks (bitSource low)).getD (d.stacks 12).length false),
      ![[],[]]⟩
  have ht := Subexp.TypeBitProgram.trace (d.stacks 12) (d.stacks (bitSource low)) a.regs
  have ht' : Trace Subexp.TypeBitProgram.program
      (Subexp.TypeBitProgram.cost (d.stacks 12) (d.stacks (bitSource low)))
      (a.withPC (some Subexp.TypeBitProgram.program.entry)) (b.withPC none) := by
    have ha : a.withPC (some Subexp.TypeBitProgram.program.entry)=
        Subexp.TypeBitProgram.cfg (some 0) a.regs (d.stacks 12) (d.stacks (bitSource low)) := by
      apply congrArg (fun ss : Fin 2 → List Bool => (⟨some 0,a.regs,ss⟩ : Cfg 3 2 7))
      funext i; fin_cases i <;> rfl
    have hb : b.withPC none=Subexp.TypeBitProgram.cfg none b.regs [] [] := by
      apply congrArg (fun ss : Fin 2 → List Bool => (⟨none,b.regs,ss⟩ : Cfg 3 2 7))
      funext i; fin_cases i <;> rfl
    rw [ha,hb]
    exact ht
  have he := eval_call_from_state Subexp.TypeBitProgram.program (bitRegs low) (bitPorts low)
    d (bitRegs_injective low) (bitPorts_injective low) ht'
  have hz : embedState (bitRegs low) (bitPorts low) d b=
      bitResult d low ((d.stacks (bitSource low)).getD (d.stacks 12).length false) := by
    apply embedState_eq_of_ports (bitRegs low) (bitPorts low) d _ _
      (bitRegs_injective low) (bitPorts_injective low)
    · intro i; cases low <;> fin_cases i <;>
        simp [b,Subexp.TypeBitProgram.resultRegs,bitRegs,bitFlag,bitResult,readRegs]
    · intro i hi
      have h0 : i ≠ 0 := fun he => hi ⟨0,by simpa [bitRegs] using he.symm⟩
      have h1 : i ≠ 1 := fun he => hi ⟨1,by simpa [bitRegs] using he.symm⟩
      have hf : i ≠ bitFlag low := fun he => hi ⟨2,by simpa [bitRegs] using he.symm⟩
      simp [bitResult,readRegs,h0,h1,hf]
    · intro i; cases low <;> fin_cases i <;> simp [b,bitPorts,bitSource,bitResult]
    · intro i hi
      have h12 : i ≠ 12 := fun he => hi ⟨0,by simpa [bitPorts] using he.symm⟩
      have hs : i ≠ bitSource low := fun he => hi ⟨1,by simpa [bitPorts] using he.symm⟩
      simp [bitResult,h12,hs]
  rw [hz] at he
  exact he

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
