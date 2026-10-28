import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBank
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankFrameCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankFrameLookup

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def BaseReady (a : Data) : Prop :=
  (∀ j : Fin 256, j.val < 200 → a.stacks j=[]) ∧ a.stacks 254=[] ∧ a.stacks 255=[]

def metadataStacks (a : Data) (mr mc : GlobalBasisMetadata.Metadata) : Fin 256 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update a.stacks 64 mr.block) 65 mr.typeCode)
      66 mr.rank) 67 mc.block) 68 mc.typeCode) 69 mc.rank

theorem metadataStacks_frame (a : Data) (mr mc : GlobalBasisMetadata.Metadata)
    (j : Fin 256) (hj : j.val < 64 ∨ 70 ≤ j.val) : metadataStacks a mr mc j=a.stacks j := by
  have h64 : j≠64 := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  have h65 : j≠65 := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  have h66 : j≠66 := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  have h67 : j≠67 := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  have h68 : j≠68 := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  have h69 : j≠69 := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  simp [metadataStacks,h64,h65,h66,h67,h68,h69]

theorem lookup_eval (a : Data) (records : List (List Bool × List Bool))
    (row col : List Bool) (mr mc : GlobalBasisMetadata.Metadata)
    (hr : records.lookup row=some mr.encode) (hc : records.lookup col=some mc.encode)
    (hm : a.stacks 200=SelectorProgram.rawRecords records)
    (hrow : a.stacks 252=row) (hcol : a.stacks 253=col)
    (hready : ∀ j : Fin 256, 64 ≤ j.val → j.val ≤ 76 → a.stacks j=[]) :
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
      have h64 : j≠64 := by intro h; apply hj; exact ⟨3,h.symm⟩
      have h65 : j≠65 := by intro h; apply hj; exact ⟨4,h.symm⟩
      have h66 : j≠66 := by intro h; apply hj; exact ⟨5,h.symm⟩
      have h67 : j≠67 := by intro h; apply hj; exact ⟨6,h.symm⟩
      have h68 : j≠68 := by intro h; apply hj; exact ⟨7,h.symm⟩
      have h69 : j≠69 := by intro h; apply hj; exact ⟨8,h.symm⟩
      simp [metadataStacks,h64,h65,h66,h67,h68,h69]
  · exact congrArg (fun d : LookupPair.Data => d.regs 4) hp
  · exact congrArg (fun d : LookupPair.Data => d.regs 5) hp

theorem compareBlocks_eval (a : Data) (h : ∀ j : Fin 256, j.val < 30 → a.stacks j=[]) :
    ∃ n ≤ 18*(a.stacks 64).length+9*(a.stacks 67).length+32,
      ∃ e : Data, Eval compareBlocks n a e ∧ e.stacks=a.stacks ∧
        e.regs 6=a.regs 6 ∧ e.regs 7=decide (a.stacks 64=a.stacks 67) :=
  EntryBankFrame.compare_lifted blockPorts blockPorts_inj a
    (h _ (by decide)) (h _ (by decide)) (h _ (by decide)) (h _ (by decide))

theorem compareIndices_eval (a : Data) (h : ∀ j : Fin 256, j.val < 30 → a.stacks j=[]) :
    ∃ n ≤ 18*(a.stacks 252).length+9*(a.stacks 253).length+32,
      ∃ e : Data, Eval compareIndices n a e ∧ e.stacks=a.stacks ∧
        e.regs 6=a.regs 6 ∧ e.regs 7=decide (a.stacks 252=a.stacks 253) :=
  EntryBankFrame.compare_lifted indexPorts indexPorts_inj a
    (h _ (by decide)) (h _ (by decide)) (h _ (by decide)) (h _ (by decide))

theorem prepare_frame (a : Data) (j : Fin 256) (hj : 64 ≤ j.val) :
    (Staging.result 0 1 prepareOps a).stacks j=a.stacks j := by
  apply Staging.result_frame
  intro op hop
  simp only [prepareOps,List.mem_cons,List.not_mem_nil,or_false] at hop
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [Staging.Action.destination] <;>
    (intro h; have hv := congrArg Fin.val h; simp at hv; omega)

theorem prepare_temp (a : Data) (h : a.stacks 199=[]) :
    (Staging.result 0 1 prepareOps a).stacks 199=[] :=
  EntryBankFrame.staging_result_temp 0 1 199 prepareOps a prepareOps_valid h

def prepareSize (a : Data) : ℕ :=
  (a.stacks 202).length+(a.stacks 203).length+(a.stacks 204).length+
  (a.stacks 205).length+(a.stacks 206).length+(a.stacks 207).length+
  (a.stacks 208).length+(a.stacks 209).length+(a.stacks 210).length+
  (a.stacks 211).length+(a.stacks 65).length+(a.stacks 68).length

theorem prepare_cost (a : Data) : Staging.cost 0 1 prepareOps a=7*prepareSize a+62 := by
  simp [prepareOps,Staging.cost,Staging.actionCost,Staging.actionResult,
    StackRoutines.copyStacks,prepareSize]
  ring

theorem exportPair_stacks (a : Data) (h254 : a.stacks 254=[]) (h255 : a.stacks 255=[]) :
    (Staging.result 0 1 exportOps a).stacks=
      Function.update (Function.update a.stacks 254 (a.stacks 53)) 255 (a.stacks 54) := by
  simp [exportOps,Staging.result,Staging.actionResult,StackRoutines.copyStacks,h254,h255]

theorem exportPair_cost (a : Data) :
    Staging.cost 0 1 exportOps a=7*((a.stacks 53).length+(a.stacks 54).length)+10 := by
  simp [exportOps,Staging.cost,Staging.actionCost,Staging.actionResult,StackRoutines.copyStacks]
  ring

theorem workPorts_mem (j : Fin 256) : j∈workPorts ↔ j.val < 200 := by
  simp only [workPorts,List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    change i.val=j.val at hv
    omega
  · intro hj
    exact ⟨⟨j.val,hj⟩,Fin.ext rfl⟩

theorem workPorts_length : workPorts.length=200 :=
  List.length_ofFn

theorem cleanup_stacks (a : Data) (j : Fin 256) :
    (Staging.result 0 1 cleanupOps a).stacks j=if j.val < 200 then [] else a.stacks j := by
  simpa only [cleanupOps,workPorts_mem] using Staging.result_clears 0 1 workPorts a j

theorem cleanup_cost (a : Data) :
    Staging.cost 0 1 cleanupOps a ≤
      2*(workPorts.map (fun j => (a.stacks j).length)).sum+600 := by
  convert EntryBankFrame.clear_cost_le 0 1 workPorts a using 1 <;>
    norm_num [cleanupOps,workPorts_length]

theorem cleanup_cost_le (a : Data) (B : ℕ)
    (h : ∀ j : Fin 256, j.val < 200 → (a.stacks j).length ≤ B) :
    Staging.cost 0 1 cleanupOps a ≤ 400*B+600 := by
  have hs := EntryBankFrame.sum_map_le_length workPorts (fun j => (a.stacks j).length) B
    (fun j hj => h j ((workPorts_mem j).mp hj))
  have hc := cleanup_cost a
  rw [workPorts_length] at hs
  omega

theorem cleanup_ready (a : Data) (j : Fin 256) (hj : j.val < 200) :
    (Staging.result 0 1 cleanupOps a).stacks j=[] := by rw [cleanup_stacks,ite_eq_left hj]

theorem cleanup_frame (a : Data) (j : Fin 256) (hj : 200 ≤ j.val) :
    (Staging.result 0 1 cleanupOps a).stacks j=a.stacks j := by
  rw [cleanup_stacks,ite_eq_right (by omega)]

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
