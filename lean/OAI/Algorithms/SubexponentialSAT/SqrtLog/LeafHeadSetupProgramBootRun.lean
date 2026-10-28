import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoot

namespace OAI.Algorithms

/-! Exact state and cost of the paid per-node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def addressState (a : Data) (regs : Fin 3 → Bool) (r t : ℕ) : Data :=
  returned addressRegs (by decide) addressInputs addressOutputs a (Address.result regs r t)
def countedState (a : Data) (regs : Fin 8 → Bool) (records : List (List Bool)) : Data :=
  returned rowCountRegs (by decide) rowCountInputs rowCountOutputs a
    (rowCountState regs records (List.replicate records.length true))
def bootState (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) : Data :=
  returned cacheRegs (by decide) cacheInputs cacheOutputs
    (countedState (addressState a ra r t) rd records) (cacheState rc height R width words)

def bootCost (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) : ℕ :=
  stageCost addressRegs (by decide) addressInputs addressOutputs a
      (Address.result ra r t) (Address.budget r t)+
  stageCost rowCountRegs (by decide) rowCountInputs rowCountOutputs (addressState a ra r t)
      (rowCountState rd records (List.replicate records.length true))
      (SubexponentialSAT.SubexpScopeCountSetup.countBudget records+1)+
  stageCost cacheRegs (by decide) cacheInputs cacheOutputs
      (countedState (addressState a ra r t) rd records)
      (cacheState rc height R width words) (cacheBound height R width)

theorem addressState_frame (a : Data) (regs : Fin 3 → Bool) (r t : ℕ) (i : Fin 768)
    (hi : Protected i) (h648 : i≠648) (h649 : i≠649) :
    (addressState a regs r t).stacks i=a.stacks i := by
  apply returned_frame addressRegs (by decide) addressInputs addressOutputs a _ i hi
  intro p hp
  simp only [addressOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl
  · exact h648
  · exact h649

theorem countedState_frame (a : Data) (regs : Fin 8 → Bool) (records : List (List Bool))
    (i : Fin 768) (hi : Protected i) (h647 : i≠647) :
    (countedState a regs records).stacks i=a.stacks i := by
  apply returned_frame rowCountRegs (by decide) rowCountInputs rowCountOutputs a _ i hi
  intro p hp
  simp only [rowCountOutputs,List.mem_singleton] at hp
  subst p
  exact h647

theorem bootState_frame (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (i : Fin 768) (hi : Protected i)
    (hne : i∉([640,641,642,643,647,648,649] : List (Fin 768))) :
    (bootState a ra rd rc r t records height R width words).stacks i=a.stacks i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
  rcases hne with ⟨h640,h641,h642,h643,h647,h648,h649⟩
  rw [bootState,returned_frame cacheRegs (by decide) cacheInputs cacheOutputs _ _ i hi,
    countedState_frame _ _ _ _ hi h647,addressState_frame _ _ _ _ _ hi h648 h649]
  intro p hp
  simp only [cacheOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact h640
  · exact h641
  · exact h642
  · exact h643

theorem boot_eval (a : Data) (r t : ℕ) (records : List (List Bool))
    (height R width : List Bool)
    (hr : a.stacks 130=List.replicate r true) (ht : a.stacks 307=List.replicate t true)
    (hrecords : a.stacks 136=SubexponentialSAT.Encoding.encodeList id records)
    (hheight : a.stacks 139=height) (hR : a.stacks 138=R) (hwidth : a.stacks 140=width)
    (hw : 1+2*height.length*R.length ≤ width.length) :
    ∃ ra rd rc words steps, steps ≤ bootCost a ra rd rc r t records height R width words ∧
      Eval boot steps a (bootState a ra rd rc r t records height R width words) ∧
      words.length=R.length ∧ (∀ w∈words,w.length=width.length) ∧
      words.map SubexponentialSAT.BinaryArithmetic.toNat=
        (List.range R.length).map (LayoutCoefficientRecurrence.H height.length) := by
  obtain ⟨ra,ta,hta,hea⟩ := initializeAddress_eval a r t hr ht
  let b := addressState a ra r t
  obtain ⟨rd,hed⟩ := countRows_eval b records
    ((addressState_frame a ra r t 136 (by decide) (by decide) (by decide)).trans hrecords)
  let c := countedState b rd records
  have cf (i : Fin 768) (hi : Protected i) (h647 : i≠647) (h648 : i≠648) (h649 : i≠649) :
      c.stacks i=a.stacks i :=
    (countedState_frame b rd records i hi h647).trans (addressState_frame a ra r t i hi h648 h649)
  obtain ⟨rc,words,tc,htc,hec,hlen,hword,hvalue⟩ := initializeCache_eval c height R width
    ((cf 139 (by decide) (by decide) (by decide) (by decide)).trans hheight)
    ((cf 138 (by decide) (by decide) (by decide) (by decide)).trans hR)
    ((cf 140 (by decide) (by decide) (by decide) (by decide)).trans hwidth) hw
  refine ⟨ra,rd,rc,words,_,?_,hea.seq (hed.seq hec),hlen,hword,hvalue⟩
  unfold bootCost
  dsimp [b,c] at htc ⊢
  omega

theorem bootState_count (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 648=List.replicate r true := by
  rw [bootState,returned_frame cacheRegs (by decide) cacheInputs cacheOutputs _ _ 648 (by decide),
    countedState_frame _ _ _ _ (by decide) (by decide)]
  · exact returned_word addressRegs (by decide) addressInputs addressOutputs a _
      addressOutputs_protected (by decide) (3,648) (by simp [addressOutputs])
  · simp [cacheOutputs]

theorem bootState_address (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 649=List.replicate (t*r) true := by
  rw [bootState,returned_frame cacheRegs (by decide) cacheInputs cacheOutputs _ _ 649 (by decide),
    countedState_frame _ _ _ _ (by decide) (by decide)]
  · exact returned_word addressRegs (by decide) addressInputs addressOutputs a _
      addressOutputs_protected (by decide) (4,649) (by simp [addressOutputs])
  · simp [cacheOutputs]

theorem bootState_dimension (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 647=List.replicate records.length true := by
  rw [bootState,returned_frame cacheRegs (by decide) cacheInputs cacheOutputs _ _ 647 (by decide)]
  · exact returned_word rowCountRegs (by decide) rowCountInputs rowCountOutputs _ _
      rowCountOutputs_protected (by decide) (2,647) (by simp [rowCountOutputs])
  · simp [cacheOutputs]


theorem bootState_positive (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 640=words.flatten :=
  returned_word cacheRegs (by decide) cacheInputs cacheOutputs _ _ cacheOutputs_protected
    (by decide) (0,640) (by simp [cacheOutputs])


theorem bootState_negative (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 641=List.replicate (R.length*width.length) false :=
  returned_word cacheRegs (by decide) cacheInputs cacheOutputs _ _ cacheOutputs_protected
    (by decide) (1,641) (by simp [cacheOutputs])


theorem bootState_denominator (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 642=LayoutProgram.IntegerCache.denominatorWord R.length :=
  returned_word cacheRegs (by decide) cacheInputs cacheOutputs _ _ cacheOutputs_protected
    (by decide) (2,642) (by simp [cacheOutputs])

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

end

end OAI.Algorithms
