import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankFrameCore

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem lookupRegs_inj : Function.Injective lookupRegs := Fin.castAdd_injective _ _
theorem lookupPorts_inj : Function.Injective lookupPorts := by decide
theorem lowPorts_inj : Function.Injective lowPorts := Fin.castAdd_injective _ _
theorem vectorPorts_inj : Function.Injective vectorPorts := Fin.castAdd_injective _ _
theorem blockPorts_inj : Function.Injective (comparePorts 288 291) := by decide
theorem indexPorts_inj : Function.Injective (comparePorts 304 305) := by decide

def metadataStacks (a : Data) (mr mc : GlobalBasisMetadata.Metadata) : Fin 320 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update a.stacks 288 mr.block) 289 mr.typeCode)
      290 mr.rank) 291 mc.block) 292 mc.typeCode) 293 mc.rank

theorem lookup_eval (a : Data) (records : List (List Bool × List Bool))
    (row col : List Bool) (mr mc : GlobalBasisMetadata.Metadata)
    (hr : records.lookup row=some mr.encode) (hc : records.lookup col=some mc.encode)
    (hm : a.stacks 306=SelectorProgram.rawRecords records)
    (hrow : a.stacks 304=row) (hcol : a.stacks 305=col)
    (hready : ∀ j : Fin 320, 288 ≤ j.val → j.val ≤ 300 → a.stacks j=[]) :
    ∃ n ≤ 400*(GlobalBasisMetadata.volume records row)^2+
        400*(GlobalBasisMetadata.volume records col)^2+1,
      ∃ e : Data, Eval lookup n a e ∧ e.stacks=metadataStacks a mr mc ∧
        e.regs 4=mr.coveredFlag ∧ e.regs 5=mc.coveredFlag := by
  have ha : projectState lookupRegs lookupPorts a=
      LookupPair.state (a.regs ∘ lookupRegs) (SelectorProgram.rawRecords records)
        row col [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [lookupPorts,hm,hrow,hcol,hready]
  obtain ⟨n,hn,e,he,hp,hf,_⟩ := EntryBankFrame.lookup_lifted lookupRegs lookupPorts
    lookupRegs_inj lookupPorts_inj a records row col mr mc hr hc ha
  refine ⟨n,hn,e,he,?_,?_,?_⟩
  · funext j
    by_cases hj : ∃ i, lookupPorts i=j
    · obtain ⟨i,rfl⟩ := hj
      have h := congrArg (fun d : LookupPair.Data => d.stacks i) hp
      fin_cases i <;>
        simpa [projectState,lookupPorts,LookupPair.state,metadataStacks,hm,hrow,hcol,hready] using h
    · rw [hf j hj]
      have h288 : j≠288 := by intro h; apply hj; exact ⟨3,h.symm⟩
      have h289 : j≠289 := by intro h; apply hj; exact ⟨4,h.symm⟩
      have h290 : j≠290 := by intro h; apply hj; exact ⟨5,h.symm⟩
      have h291 : j≠291 := by intro h; apply hj; exact ⟨6,h.symm⟩
      have h292 : j≠292 := by intro h; apply hj; exact ⟨7,h.symm⟩
      have h293 : j≠293 := by intro h; apply hj; exact ⟨8,h.symm⟩
      simp [metadataStacks,h288,h289,h290,h291,h292,h293]
  · exact congrArg (fun d : LookupPair.Data => d.regs 4) hp
  · exact congrArg (fun d : LookupPair.Data => d.regs 5) hp

theorem compareBlocks_eval (a : Data) (h301 : a.stacks 301=[]) (h302 : a.stacks 302=[])
    (h303 : a.stacks 303=[]) (h307 : a.stacks 307=[]) :
    ∃ n ≤ 18*(a.stacks 288).length+9*(a.stacks 291).length+32,
      ∃ e : Data, Eval compareBlocks n a e ∧ e.stacks=a.stacks ∧
        e.regs 6=a.regs 6 ∧ e.regs 7=decide (a.stacks 288=a.stacks 291) :=
  EntryBankFrame.compare_lifted _ blockPorts_inj a h301 h302 h303 h307

theorem compareIndices_eval (a : Data) (h301 : a.stacks 301=[]) (h302 : a.stacks 302=[])
    (h303 : a.stacks 303=[]) (h307 : a.stacks 307=[]) :
    ∃ n ≤ 18*(a.stacks 304).length+9*(a.stacks 305).length+32,
      ∃ e : Data, Eval compareIndices n a e ∧ e.stacks=a.stacks ∧
        e.regs 6=a.regs 6 ∧ e.regs 7=decide (a.stacks 304=a.stacks 305) :=
  EntryBankFrame.compare_lifted _ indexPorts_inj a h301 h302 h303 h307

theorem compareTypes_eval (a : Data) (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[])
    (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[]) :
    ∃ n ≤ 18*(a.stacks 23).length+9*(a.stacks 24).length+35,
      ∃ e : Data, Eval compareTypes n a e ∧ e.stacks=a.stacks ∧
        e.regs 7=decide (a.stacks 23=a.stacks 24) := by
  let p := projectState lowRegs lowPorts a
  obtain ⟨n,hn,b,he,hbs,h7⟩ := TypeCompare.command_eval p h0 h1 h2 h3
  let e := embedState lowRegs lowPorts a b
  have hh := eval_liftCommand_from_state TypeCompare.command 23 23 lowRegs lowPorts a
    lowRegs_inj lowPorts_inj he
  refine ⟨n+1,by simpa [p,projectState,lowPorts] using Nat.add_le_add_right hn 1,e,hh,?_,?_⟩
  · change Function.extend lowPorts b.stacks a.stacks=a.stacks
    rw [hbs]
    exact congrArg StructuredProgram.State.stacks (embedState_project lowRegs lowPorts a lowRegs_inj lowPorts_inj)
  · exact (embedState_register lowRegs lowPorts a b lowRegs_inj 7).trans h7

/-- This premise is an actual execution of the fixed native scalar-table
producer. It is supplied by Native.tableProgram_runsIn, never by a value oracle. -/
theorem vector_lifted (a : Data) (bits : List Bool) (rf : Fin 16 → Bool) {n : ℕ}
    (he : Trace LayoutSourceValuesProgram.Native.tableProgram n
      ((projectState id vectorPorts a).withPC (some LayoutSourceValuesProgram.Native.tableProgram.entry))
      ((⟨rf,Function.update (projectState id vectorPorts a).stacks 67 bits⟩ : State 16 256).withPC none)) :
    ∃ b : Data, Eval vector n a b ∧ b.stacks=Function.update a.stacks 67 bits ∧ b.regs=rf := by
  let z : State 16 256 := ⟨rf,Function.update (projectState id vectorPorts a).stacks 67 bits⟩
  let b := embedState id vectorPorts a z
  refine ⟨b,eval_call_from_state _ id vectorPorts a Function.injective_id vectorPorts_inj he,?_,?_⟩
  · change Function.extend vectorPorts z.stacks a.stacks=_
    dsimp only [z]
    rw [ProgramLinking.extend_update vectorPorts_inj]
    have h := congrArg StructuredProgram.State.stacks
      (embedState_project id vectorPorts a Function.injective_id vectorPorts_inj)
    change Function.extend vectorPorts (projectState id vectorPorts a).stacks a.stacks=a.stacks at h
    rw [h]
    rfl
  · funext j
    exact embedState_register id vectorPorts a z Function.injective_id j

theorem literalRegs_inj : Function.Injective literalRegs := Fin.castAdd_injective _ _

theorem literal_eval (src : Fin 320) (hsrc : src=313 ∨ src=314) (a : Data)
    (h315 : a.stacks 315=[]) (h316 : a.stacks 316=[]) (h287 : a.stacks 287=[]) :
    ∃ b : Data, Eval (literal src) (14*(a.stacks src).length+19) a b ∧
      b.stacks=Function.update a.stacks 287 (SubexponentialSAT.SubexpKernelControl.pushWord (a.stacks src)) := by
  have hp : Function.Injective (literalPorts src) := by
    rcases hsrc with rfl|rfl <;> decide
  let small := projectState literalRegs (literalPorts src) a
  have hi : small=Literal.state (a.regs ∘ literalRegs) (a.stacks src) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [literalPorts,h315,h316,h287]
  obtain ⟨rf,he⟩ := Literal.command_eval (a.regs ∘ literalRegs) (a.stacks src)
  rw [← hi] at he
  let z := Literal.state rf (a.stacks src) [] [] (SubexponentialSAT.SubexpKernelControl.pushWord (a.stacks src))
  have hz : z.stacks=Function.update small.stacks 3 (SubexponentialSAT.SubexpKernelControl.pushWord (a.stacks src)) := by
    rw [hi]
    funext j
    fin_cases j <;> simp [z,Literal.state]
  let b := embedState literalRegs (literalPorts src) a z
  refine ⟨b,?_,?_⟩
  · exact eval_liftCommand_from_state Literal.command 0 3 literalRegs (literalPorts src) a literalRegs_inj hp he
  · change Function.extend (literalPorts src) z.stacks a.stacks=_
    rw [hz,ProgramLinking.extend_update hp]
    have hh := congrArg StructuredProgram.State.stacks
      (embedState_project literalRegs (literalPorts src) a literalRegs_inj hp)
    change Function.extend (literalPorts src) small.stacks a.stacks=a.stacks at hh
    rw [hh]
    rfl

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
