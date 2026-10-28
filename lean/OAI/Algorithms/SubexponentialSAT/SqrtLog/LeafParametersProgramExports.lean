import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramExportsTable
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramCache
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBanked
import OAI.Algorithms.SubexponentialSAT.BankRoutines

namespace OAI.Algorithms

/-! Native cache preparation, persistent metadata export, and bank restoration.
The guard register is framed. Unary cache tapes are cleared after copying so
ring setup again receives the ordinary binary parameter model. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def bankRegs : Fin 8 → Fin 40 := Fin.castAdd 32
def bank (i : Fin 77) : Fin 768 := ⟨340+i.val,by omega⟩
theorem bank_injective : Function.Injective bank := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [bank] at this; omega

def cacheCall : Code := liftCommand Cache.command (Bank.port 18) (Bank.port 53) bankRegs bank
def cached (a : Data) (r : Regs) (w : Words) : Data :=
  embedState bankRegs bank a (Bank.state r (Cache.unaryWords w))

theorem cached_stack (a : Data) (r : Regs) (w : Words) (i : Fin 64) :
    (cached a r w).stacks (bank (Bank.port i))=Cache.unaryWords w i := by
  exact (embedState_stack bankRegs bank a _ bank_injective (Bank.port i)).trans (Bank.state_port _ _ _)

theorem cached_frame (a : Data) (r : Regs) (w : Words) (j : Fin 768)
    (hj : j.val < 340 ∨ 417 ≤ j.val) : (cached a r w).stacks j=a.stacks j := by
  apply embedState_stack_frame
  rintro ⟨i,hi⟩
  have := congrArg Fin.val hi
  dsimp [bank] at this
  have := i.isLt
  omega

theorem destination_outside (i : Fin 16) :
    (destination i).val < 340 ∨ 417 ≤ (destination i).val := by fin_cases i <;> decide

theorem cached_empty (a : Data) (r : Regs) (w : Words) (ho : OutputEmpty a) :
    OutputEmpty (cached a r w) := by
  intro i
  rw [cached_frame a r w _ (destination_outside i)]
  exact ho i

theorem cached_scratch (a : Data) (r : Regs) (w : Words) (ht : Scratch a) :
    Scratch (cached a r w) := by
  simpa only [Scratch,cached_frame a r w 659 (by decide),
    cached_frame a r w 660 (by decide),cached_frame a r w 661 (by decide),
    cached_frame a r w 679 (by decide)] using ht

theorem cacheCall_eval (a : Data) (m : Model) (w : Words) (hs : Shape m w)
    (hp : projectState bankRegs bank a=Bank.state (a.regs ∘ bankRegs) w)
    (hr : 0 < m.val 18) :
    ∃ n ≤ Cache.runtimeBound m+1, ∃ rf wb,
      Eval cacheCall n a (cached a rf wb) ∧ Shape (Interval.finalModel m) wb := by
  obtain ⟨n,rf,wb,he,hshape,hn⟩ := Cache.command_eval m (a.regs ∘ bankRegs) w hs hr
  refine ⟨n+1,Nat.add_le_add_right hn 1,rf,wb,?_,hshape⟩
  exact eval_liftCommand_from_state Cache.command (Bank.port 18) (Bank.port 53) bankRegs bank a
    (Fin.castAdd_injective _ _) bank_injective (hp.symm ▸ he)

def cacheLength (m : Model) (j : Fin 64) : ℕ :=
  if j=53 then m.val 50 else if j=52 then m.val 46 else if j=51 then m.val 29 else m.len j

theorem cacheLength_le (m : Model) (w : Words) (hs : Shape m w) (j : Fin 64) :
    (Cache.unaryWords w j).length ≤ cacheLength m j := by
  by_cases h53 : j=53
  · subst j; simp [Cache.unaryWords,cacheLength,hs.1 50]
  by_cases h52 : j=52
  · subst j; simp [Cache.unaryWords,cacheLength,hs.1 46]
  by_cases h51 : j=51
  · subst j; simp [Cache.unaryWords,cacheLength,hs.1 29]
  simpa [Cache.unaryWords,cacheLength,h53,h52,h51] using hs.2 j

def exportFieldBound (m : Model) (i : Fin 16) : ℕ :=
  if i.val < 5 then Cache.unaryBound (m.val (localSource i)) (m.len (localSource i))
  else 7*cacheLength m (localSource i)+5

def exportModelBudget (m : Model) : ℕ := ((List.finRange 16).map (exportFieldBound m)).sum

theorem first_sources (i : Fin 16) (hi : i.val < 5) :
    localSource i≠51 ∧ localSource i≠52 ∧ localSource i≠53 := by
  fin_cases i <;> simp_all [localSource]

theorem exportField_le (m : Model) (w : Words) (hs : Shape m w)
    (a : Data) (r : Regs) (i : Fin 16) :
    fieldCost (field i) (cached a r w) ≤ exportFieldBound m i := by
  have hword : (cached a r w).stacks (field i).src=Cache.unaryWords w (localSource i) :=
    cached_stack a r w (localSource i)
  simp only [fieldCost,hword,exportFieldBound]
  by_cases hi : i.val < 5
  · obtain ⟨h51,h52,h53⟩ := first_sources i hi
    simpa [field,hi,Cache.unaryWords,h51,h52,h53] using
      Cache.unaryCopyBound_le (w (localSource i)) (m.val (localSource i))
        (m.len (localSource i)) (hs.1 _) (hs.2 _)
  · simp only [field,hi,decide_false,Bool.false_eq_true,ite_false]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 7 (cacheLength_le m w hs _)) 5

theorem exportBudget_le (m : Model) (w : Words) (hs : Shape m w) (a : Data) (r : Regs) :
    exportBudget (cached a r w) ≤ exportModelBudget m := by
  simp only [exportBudget,fields,List.map_map,Function.comp_def,exportModelBudget]
  apply List.sum_le_sum
  intro i hi
  exact exportField_le m w hs a r i

def clearPorts : List (Fin 768) := (List.finRange 18).map (fun i => bank ⟨46+i.val,by omega⟩)
def clearCommand : Code := BankRoutines.clearCmd 679 0 1 clearPorts
def cleared (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks clearPorts a.stacks⟩
def clearCost (a : Data) : ℕ := 2*(clearPorts.map (fun j => (a.stacks j).length)).sum+57

theorem clearPorts_nodup : clearPorts.Nodup := by decide

theorem clearPorts_mem (j : Fin 768) : j∈clearPorts ↔ 386 ≤ j.val ∧ j.val < 404 := by
  simp only [clearPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨i,rfl⟩; dsimp [bank]; have := i.isLt; omega
  · intro hj
    refine ⟨⟨j.val-386,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [bank]
    omega

theorem clearCommand_eval (a : Data) (ht : a.stacks 679=[]) :
    Eval clearCommand (clearCost a) a (cleared a) := by
  have he := BankRoutines.clear_eval 679 (0 : Fin 40) 1 clearPorts clearPorts_nodup a.regs a.stacks ht
  simpa only [clearCommand,clearCost,cleared,clearPorts,List.length_map,List.length_finRange,
    show 3*18+3=57 by decide] using he

def clearModelBudget (m : Model) : ℕ :=
  2*((List.finRange 18).map (fun i => cacheLength m ⟨46+i.val,by omega⟩)).sum+57

theorem clearCost_le (m : Model) (w : Words) (hs : Shape m w) (a : Data) (r : Regs)
    (ho : OutputEmpty (cached a r w)) (ht : Scratch (cached a r w)) :
    clearCost (exportState (cached a r w)) ≤ clearModelBudget m := by
  simp only [clearCost,clearPorts,List.map_map,Function.comp_def,clearModelBudget]
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  apply List.sum_le_sum
  intro i hi
  have hn : ∀ j, destination j≠bank ⟨46+i.val,by omega⟩ := by
    intro j heq
    have hj := destination_outside j
    have hv := congrArg Fin.val heq
    dsimp [bank] at hv
    have := i.isLt
    omega
  rw [export_stack_frame _ ho ht _ hn]
  have hbank : (⟨46+i.val,by omega⟩ : Fin 77)=Bank.port ⟨46+i.val,by omega⟩ := rfl
  rw [hbank,cached_stack]
  exact cacheLength_le m w hs _

def restoredWords (w : Words) : Words := fun j => if 46 ≤ j.val then [] else w j

theorem intervalModel_frame (m : Model) (j : Fin 64) (hj : j.val < 46) :
    (Interval.finalModel m).val j=m.val j ∧ (Interval.finalModel m).len j=m.len j := by
  have h46 : j≠46 := by intro h; subst j; norm_num at hj
  have h47 : j≠47 := by intro h; subst j; norm_num at hj
  have h48 : j≠48 := by intro h; subst j; norm_num at hj
  have h49 : j≠49 := by intro h; subst j; norm_num at hj
  have h50 : j≠50 := by intro h; subst j; norm_num at hj
  simpa [Interval.finalModel,CacheWidth.code,Interval.intervalModel,result,next,output,
    lengthBound,h46,h47,h48,h49,h50] using Interval.prepare_frame m j hj

theorem restored_shape (m : Model) (w : Words) (hs : Shape (Interval.finalModel m) w)
    (hz : ∀ j,46 ≤ j.val → m.val j=0) : Shape m (restoredWords w) := by
  constructor
  · intro j
    by_cases hj : 46 ≤ j.val
    · simp [restoredWords,hj,hz j hj]
    · simpa [restoredWords,hj,(intervalModel_frame m j (by omega)).1] using hs.1 j
  · intro j
    by_cases hj : 46 ≤ j.val
    · simp [restoredWords,hj]
    · simpa [restoredWords,hj,(intervalModel_frame m j (by omega)).2] using hs.2 j

def prepareCommand : Code := .seq cacheCall (.seq exportCommand clearCommand)
def prepareBudget (m : Model) : ℕ := Cache.runtimeBound m+1+
  exportModelBudget (Interval.finalModel m)+clearModelBudget (Interval.finalModel m)

theorem restored_projection (a : Data) (r : Regs) (w : Words)
    (ho : OutputEmpty (cached a r w)) (ht : Scratch (cached a r w)) :
    projectState bankRegs bank (cleared (exportState (cached a r w)))=
      Bank.state ((cleared (exportState (cached a r w))).regs ∘ bankRegs) (restoredWords w) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  have hn : ∀ i, destination i≠bank j := by
    intro i heq
    have hi := destination_outside i
    have hv := congrArg Fin.val heq
    dsimp [bank] at hv
    have := j.isLt
    omega
  change (if bank j∈clearPorts then [] else (exportState (cached a r w)).stacks (bank j))=_
  rw [export_stack_frame _ ho ht _ hn]
  have hmem : bank j∈clearPorts ↔ 46 ≤ j.val ∧ j.val < 64 := by
    rw [clearPorts_mem]; dsimp [bank]; omega
  simp only [hmem]
  rw [show (cached a r w).stacks (bank j)=(Bank.state r (Cache.unaryWords w)).stacks j from
    embedState_stack bankRegs bank a _ bank_injective j]
  by_cases hj : j.val < 64
  · have h53 : j.val < 46 → (⟨j.val,hj⟩ : Fin 64)≠53 := by intro h he; have := congrArg Fin.val he; norm_num at this; omega
    have h52 : j.val < 46 → (⟨j.val,hj⟩ : Fin 64)≠52 := by intro h he; have := congrArg Fin.val he; norm_num at this; omega
    have h51 : j.val < 46 → (⟨j.val,hj⟩ : Fin 64)≠51 := by intro h he; have := congrArg Fin.val he; norm_num at this; omega
    by_cases h46 : 46 ≤ j.val
    · simp [restoredWords,hj,h46]
    · simp [Bank.state,restoredWords,hj,h46,Cache.unaryWords,h53 (by omega),h52 (by omega),h51 (by omega)]
  · simp [Bank.state,hj]

theorem prepare_eval (a : Data) (m : Model) (w : Words) (hs : Shape m w)
    (hp : projectState bankRegs bank a=Bank.state (a.regs ∘ bankRegs) w)
    (hr : 0 < m.val 18) (hz : ∀ j,46 ≤ j.val → m.val j=0)
    (ho : OutputEmpty a) (ht : Scratch a) :
    ∃ n ≤ prepareBudget m, ∃ rf wb,
      Eval prepareCommand n a (cleared (exportState (cached a rf wb))) ∧
      Shape (Interval.finalModel m) wb ∧ Shape m (restoredWords wb) := by
  obtain ⟨nc,hnc,rf,wb,hec,hsb⟩ := cacheCall_eval a m w hs hp hr
  have ho' := cached_empty a rf wb ho
  have ht' := cached_scratch a rf wb ht
  obtain ⟨ne,hne,hee⟩ := export_eval (cached a rf wb) ho' ht'
  have htmp : (exportState (cached a rf wb)).stacks 679=[] := by
    rw [export_stack_frame _ ho' ht' _ (by intro i; fin_cases i <;> decide)]
    exact ht'.2.2.2
  have heclear := clearCommand_eval (exportState (cached a rf wb)) htmp
  refine ⟨nc+(ne+clearCost (exportState (cached a rf wb))),?_,rf,wb,hec.seq (hee.seq heclear),
    hsb,restored_shape m wb hsb hz⟩
  have heB := exportBudget_le (Interval.finalModel m) wb hsb a rf
  have hcB := clearCost_le (Interval.finalModel m) wb hsb a rf ho' ht'
  dsimp [prepareBudget]
  omega


theorem clear_output_frame (a : Data) (i : Fin 16) :
    (cleared a).stacks (destination i)=a.stacks (destination i) := by
  change BankRoutines.clearBankStacks clearPorts a.stacks (destination i)=_
  apply BankRoutines.clearBankStacks_frame
  rw [clearPorts_mem]
  have hi := destination_outside i
  omega

theorem prepared_output (a : Data) (r : Regs) (w : Words)
    (ho : OutputEmpty a) (ht : Scratch a) (i : Fin 16) :
    (cleared (exportState (cached a r w))).stacks (destination i)=
      if i.val < 5 then List.replicate (BinaryArithmetic.toNat (Cache.unaryWords w (localSource i))) true
      else Cache.unaryWords w (localSource i) := by
  rw [clear_output_frame,export_output _ (cached_empty a r w ho) (cached_scratch a r w ht)]
  have hc := cached_stack a r w (localSource i)
  have hsrc : (field i).src = bank (Bank.port (localSource i)) := by
    apply Fin.ext
    rfl
  simp only [payload, hsrc]
  by_cases hi : i.val < 5
  · simpa [payload,field,hi] using congrArg (fun bits => List.replicate (BinaryArithmetic.toNat bits) true) hc
  · simpa [payload,field,hi] using hc

def unaryValues (m : Model) : Fin 8 → ℕ :=
  ![m.val 0,m.val 5,m.val 18,m.val 21,m.val 21*m.val 18,m.val 29,
    Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29),
    1+2*Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29)*m.val 29+m.val 21]

def binarySources : Fin 8 → Fin 64 := ![21,18,25,7,1,3,5,29]

theorem cached_small_value (m : Model) (w : Words) (hs : Shape (Interval.finalModel m) w)
    (j : Fin 64) (hj : j.val < 46) : BinaryArithmetic.toNat (Cache.unaryWords w j)=m.val j := by
  have h51 : j≠51 := by intro h; subst j; norm_num at hj
  have h52 : j≠52 := by intro h; subst j; norm_num at hj
  have h53 : j≠53 := by intro h; subst j; norm_num at hj
  simpa [Cache.unaryWords,h51,h52,h53,(intervalModel_frame m j hj).1] using hs.1 j

theorem prepared_unary (a : Data) (r : Regs) (m : Model) (w : Words)
    (hs : Shape (Interval.finalModel m) w) (ho : OutputEmpty a) (ht : Scratch a) (i : Fin 8) :
    (cleared (exportState (cached a r w))).stacks (destination (i.castAdd 8))=
      List.replicate (unaryValues m i) true := by
  rw [prepared_output a r w ho ht]
  have hv := Cache.output_values m w hs
  have hs0 := cached_small_value m w hs 0 (by decide)
  have hs5 := cached_small_value m w hs 5 (by decide)
  have hs18 := cached_small_value m w hs 18 (by decide)
  have hs21 := cached_small_value m w hs 21 (by decide)
  fin_cases i <;> simp_all [localSource,unaryValues]

theorem prepared_binary (a : Data) (r : Regs) (m : Model) (w : Words)
    (hs : Shape (Interval.finalModel m) w) (ho : OutputEmpty a) (ht : Scratch a) (i : Fin 8) :
    BinaryArithmetic.toNat ((cleared (exportState (cached a r w))).stacks (destination (i.natAdd 8)))=
      m.val (binarySources i) := by
  rw [prepared_output a r w ho ht]
  have hi : 8+i.val ≥ 5 := by omega
  have hj : (binarySources i).val < 46 := by fin_cases i <;> decide
  have hv := cached_small_value m w hs (binarySources i) hj
  fin_cases i <;> simpa [localSource,binarySources] using hv


theorem prepared_unary_length (a : Data) (r : Regs) (m : Model) (w : Words)
    (hs : Shape (Interval.finalModel m) w) (ho : OutputEmpty a) (ht : Scratch a) (i : Fin 8) :
    ((cleared (exportState (cached a r w))).stacks (destination (i.castAdd 8))).length=
      unaryValues m i := by rw [prepared_unary a r m w hs ho ht i,List.length_replicate]

theorem prepared_binary_length (a : Data) (r : Regs) (m : Model) (w : Words)
    (hs : Shape (Interval.finalModel m) w) (ho : OutputEmpty a) (ht : Scratch a) (i : Fin 8) :
    ((cleared (exportState (cached a r w))).stacks (destination (i.natAdd 8))).length ≤
      m.len (binarySources i) := by
  rw [prepared_output a r w ho ht]
  have hj : (binarySources i).val < 46 := by fin_cases i <;> decide
  have hv := cacheLength_le (Interval.finalModel m) w hs (binarySources i)
  have h51 : binarySources i≠51 := by fin_cases i <;> decide
  have h52 : binarySources i≠52 := by fin_cases i <;> decide
  have h53 : binarySources i≠53 := by fin_cases i <;> decide
  simp only [cacheLength,h51,h52,h53,ite_false,(intervalModel_frame m _ hj).2] at hv
  fin_cases i <;> simpa [localSource,binarySources] using hv

theorem prepared_register_frame (a : Data) (r : Regs) (w : Words)
    (i : Fin 40) (hi : 8 ≤ i.val) :
    (cleared (exportState (cached a r w))).regs i=a.regs i := by
  have h0 : i≠0 := by intro h; subst i; norm_num at hi
  have h1 : i≠1 := by intro h; subst i; norm_num at hi
  change (readRegs _ 0 1 none) i=_
  simp only [readRegs,Function.update_of_ne h0,Function.update_of_ne h1]
  rw [export_register_frame _ i (by omega)]
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  dsimp [bankRegs] at hv
  have := j.isLt
  omega

theorem prepared_stack_frame (a : Data) (r : Regs) (w : Words)
    (ho : OutputEmpty a) (ht : Scratch a) (j : Fin 768)
    (hb : j.val < 340 ∨ 417 ≤ j.val) (hj : ∀ i, destination i≠j) :
    (cleared (exportState (cached a r w))).stacks j=a.stacks j := by
  change BankRoutines.clearBankStacks clearPorts _ j=_
  rw [BankRoutines.clearBankStacks_frame]
  · rw [export_stack_frame _ (cached_empty a r w ho) (cached_scratch a r w ht) j hj]
    exact cached_frame a r w j hb
  · rw [clearPorts_mem]; omega

def program := compiled prepareCommand 340 727

theorem program_runs (a : Data) (m : Model) (w : Words) (hs : Shape m w)
    (hp : projectState bankRegs bank a=Bank.state (a.regs ∘ bankRegs) w)
    (hr : 0 < m.val 18) (hz : ∀ j,46 ≤ j.val → m.val j=0)
    (ho : OutputEmpty a) (ht : Scratch a) :
    ∃ rf wb, RunsIn program (prepareBudget m+1)
      (a.withPC (some program.entry))
      ((cleared (exportState (cached a rf wb))).withPC none) ∧
      Shape (Interval.finalModel m) wb ∧ Shape m (restoredWords wb) := by
  obtain ⟨n,hn,rf,wb,he,hshape,hrestore⟩ := prepare_eval a m w hs hp hr hz ho ht
  exact ⟨rf,wb,⟨n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 340 727⟩,hshape,hrestore⟩

theorem program_primitive (a : Data) (m : Model) (w : Words) (hs : Shape m w)
    (hp : projectState bankRegs bank a=Bank.state (a.regs ∘ bankRegs) w)
    (hr : 0 < m.val 18) (hz : ∀ j,46 ≤ j.val → m.val j=0)
    (ho : OutputEmpty a) (ht : Scratch a) :
    ∃ rf wb, Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(prepareBudget m+1))
      (primitiveCfg program (a.withPC (some program.entry)))
      (primitiveCfg program ((cleared (exportState (cached a rf wb))).withPC none)) ∧
      Shape (Interval.finalModel m) wb ∧ Shape m (restoredWords wb) := by
  obtain ⟨rf,wb,he,hshape,hrestore⟩ := program_runs a m w hs hp hr hz ho ht
  exact ⟨rf,wb,primitive_execution program he,hshape,hrestore⟩

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
