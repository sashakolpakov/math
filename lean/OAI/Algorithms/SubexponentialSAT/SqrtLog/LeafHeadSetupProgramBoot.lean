import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramAddress
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramIntegerCache
import OAI.Algorithms.SubexponentialSAT.SubexpScopeCountSetup

namespace OAI.Algorithms

/-! Per-node paid bootstrap: address multiplication, actual plan-record
counting, and construction of the integer interpolation coefficient cache. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def addressRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def addressInputs : List (Fin 768 × Fin 7) := [(130,0),(307,2)]
def addressOutputs : List (Fin 7 × Fin 768) := [(3,648),(4,649)]
def initializeAddress : Code := stage Address.program addressRegs (by decide) addressInputs addressOutputs
theorem addressInputs_protected : ∀ p∈addressInputs,Protected p.1 := by simp [addressInputs,Protected,temporary]
theorem addressOutputs_protected : ∀ p∈addressOutputs,Protected p.2 := by simp [addressOutputs,Protected,temporary]

theorem initializeAddress_eval (a : Data) (r t : ℕ)
    (hr : a.stacks 130=List.replicate r true) (ht : a.stacks 307=List.replicate t true) :
    ∃ rf n,n ≤ stageCost addressRegs (by decide) addressInputs addressOutputs a
        (Address.result rf r t) (Address.budget r t) ∧
      Eval initializeAddress n a
        (returned addressRegs (by decide) addressInputs addressOutputs a (Address.result rf r t)) := by
  let regs := (prepared (by decide) addressInputs a).regs ∘ addressRegs
  have hp : projectState addressRegs (workPort (by decide)) (prepared (by decide) addressInputs a)=
      Address.input regs r t := by
    apply prepared_eq addressRegs (by decide) addressInputs a _ addressInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [addressInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> simp [Address.input,SubexponentialSAT.Subexp.BasisTransposePlanProgram.unary,hr,ht]
    · intro j hj
      have h0 : j≠0 := hj (130,0) (by simp [addressInputs])
      have h2 : j≠2 := hj (307,2) (by simp [addressInputs])
      fin_cases j <;> simp_all [Address.input]
  obtain ⟨rf,n,hn,he⟩ := Address.program_runsIn regs r t
  have h := stage_eval Address.program addressRegs (Fin.castAdd_injective _ _) (by decide)
    addressInputs addressOutputs a _ _ addressInputs_protected addressOutputs_protected hp he
  exact ⟨rf,_,by unfold stageCost; omega,h⟩

def rowCountProgram := compiled SubexponentialSAT.SubexpScopeCountSetup.countCommand 1 2
def rowCountRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def rowCountInputs : List (Fin 768 × Fin 15) := [(136,1)]
def rowCountOutputs : List (Fin 15 × Fin 768) := [(2,647)]
def countRows : Code := stage rowCountProgram rowCountRegs (by decide) rowCountInputs rowCountOutputs
theorem rowCountInputs_protected : ∀ p∈rowCountInputs,Protected p.1 := by simp [rowCountInputs,Protected,temporary]
theorem rowCountOutputs_protected : ∀ p∈rowCountOutputs,Protected p.2 := by simp [rowCountOutputs,Protected,temporary]

def rowCountState (regs : Fin 8 → Bool) (records : List (List Bool)) (count : List Bool) : State 8 15 :=
  ⟨regs,fun i => if i=1 then SubexponentialSAT.Encoding.encodeList id records else if i=2 then count else []⟩

theorem countRows_eval (a : Data) (records : List (List Bool))
    (hs : a.stacks 136=SubexponentialSAT.Encoding.encodeList id records) :
    ∃ rf, Eval countRows
      (stageCost rowCountRegs (by decide) rowCountInputs rowCountOutputs a
        (rowCountState rf records (List.replicate records.length true))
        (SubexponentialSAT.SubexpScopeCountSetup.countBudget records+1)) a
      (returned rowCountRegs (by decide) rowCountInputs rowCountOutputs a
        (rowCountState rf records (List.replicate records.length true))) := by
  let regs := (prepared (by decide) rowCountInputs a).regs ∘ rowCountRegs
  have hp : projectState rowCountRegs (workPort (by decide)) (prepared (by decide) rowCountInputs a)=
      rowCountState regs records [] := by
    apply prepared_eq rowCountRegs (by decide) rowCountInputs a _ rowCountInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [rowCountInputs,List.mem_singleton] at hp
      subst p
      simp [rowCountState,hs]
    · intro j hj
      have h1 : j≠1 := hj (136,1) (by simp [rowCountInputs])
      simp [rowCountState,h1]
  obtain ⟨rf,he⟩ := SubexponentialSAT.SubexpScopeCountSetup.count_eval records (rowCountState regs records [])
    (by simp [rowCountState]) (by simp [rowCountState]) (by simp [rowCountState])
    (by simp [rowCountState])
  have hend : (⟨rf,Function.update (rowCountState regs records []).stacks 2
      (List.replicate records.length true)⟩ : State 8 15)=
      rowCountState rf records (List.replicate records.length true) := by
    apply congrArg (StructuredProgram.State.mk rf)
    funext i
    by_cases h2 : i=2
    · subst i
      simp [rowCountState]
    · simp [rowCountState,h2]
  rw [hend] at he
  exact ⟨rf,stage_eval rowCountProgram rowCountRegs (Fin.castAdd_injective _ _) (by decide)
    rowCountInputs rowCountOutputs a _ _ rowCountInputs_protected rowCountOutputs_protected hp
      (compiled_halt_trace he 1 2)⟩

def cacheRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def cacheInputs : List (Fin 768 × Fin 24) := [(139,20),(138,21),(140,22)]
def cacheOutputs : List (Fin 24 × Fin 768) := [(0,640),(1,641),(2,642),(19,643)]
def initializeCache : Code := stage LayoutProgram.IntegerCache.program cacheRegs (by decide)
  cacheInputs cacheOutputs
theorem cacheInputs_protected : ∀ p∈cacheInputs,Protected p.1 := by simp [cacheInputs,Protected,temporary]
theorem cacheOutputs_protected : ∀ p∈cacheOutputs,Protected p.2 := by simp [cacheOutputs,Protected,temporary]

def cacheState (regs : Fin 8 → Bool) (a r width : List Bool) (words : List (List Bool)) : State 8 24 :=
  LayoutProgram.IntegerCache.state regs a r width [] [] width words.flatten
    (List.replicate (r.length*width.length) false) (LayoutProgram.IntegerCache.denominatorWord r.length) []
def cacheBound (a r width : List Bool) : ℕ :=
  7*(a.length+r.length+width.length)+LayoutProgram.IntegerCache.flatCost a.length r.length width.length+
    11*r.length+27

theorem initializeCache_eval (d : Data) (a r width : List Bool)
    (ha : d.stacks 139=a) (hr : d.stacks 138=r) (hwidth : d.stacks 140=width)
    (hw : 1+2*a.length*r.length ≤ width.length) :
    ∃ rf words n,
      n ≤ stageCost cacheRegs (by decide) cacheInputs cacheOutputs d (cacheState rf a r width words)
        (cacheBound a r width) ∧
      Eval initializeCache n d
        (returned cacheRegs (by decide) cacheInputs cacheOutputs d (cacheState rf a r width words)) ∧
      words.length=r.length ∧ (∀ word∈words,word.length=width.length) ∧
      words.map SubexponentialSAT.BinaryArithmetic.toNat=
        (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) := by
  let regs := (prepared (by decide) cacheInputs d).regs ∘ cacheRegs
  have hp : projectState cacheRegs (workPort (by decide)) (prepared (by decide) cacheInputs d)=
      LayoutProgram.IntegerCache.state regs a r width [] [] [] [] [] [] [] := by
    apply prepared_eq cacheRegs (by decide) cacheInputs d _ cacheInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [cacheInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl <;> simp [LayoutProgram.IntegerCache.state,ha,hr,hwidth]
    · intro j hj
      have h20 : j≠20 := hj (139,20) (by simp [cacheInputs])
      have h21 : j≠21 := hj (138,21) (by simp [cacheInputs])
      have h22 : j≠22 := hj (140,22) (by simp [cacheInputs])
      fin_cases j <;> simp_all [LayoutProgram.IntegerCache.state]
  obtain ⟨rf,words,⟨n,hn,he⟩,hlen,hwords,hvalues,hden⟩ := LayoutProgram.IntegerCache.program_runsIn regs a r width hw
  have h := stage_eval LayoutProgram.IntegerCache.program cacheRegs (Fin.castAdd_injective _ _)
    (by decide) cacheInputs cacheOutputs d _ _ cacheInputs_protected cacheOutputs_protected hp he
  exact ⟨rf,words,_,by unfold stageCost cacheBound cacheState; omega,h,hlen,hwords,hvalues⟩

def boot : Code := .seq initializeAddress (.seq countRows initializeCache)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
