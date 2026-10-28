import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramInitialize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramStorageBounds

namespace OAI.Algorithms

/-! Paid node bootstrap has ordinary polynomial cost, including the copies
retained for subsequent source-polynomial evaluation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem boot_wordBound_mono {r s A B : ℕ} {a : State r s}
    (ha : WordBound A a) (h : A ≤ B) : WordBound B a := fun i => (ha i).trans h

theorem addressResult_wordBound (regs : Fin 3 → Bool) (r t K : ℕ)
    (hr : r ≤ K) (ht : t ≤ K) (hrt : t*r ≤ K) :
    WordBound K (Address.result regs r t) := by
  intro i
  fin_cases i <;> simp_all [Address.result,SubexponentialSAT.Subexp.BasisTransposePlanProgram.unary]

theorem rowCountState_wordBound (regs : Fin 8 → Bool) (records : List (List Bool)) (K : ℕ)
    (hb : (SubexponentialSAT.Encoding.encodeList id records).length ≤ K) (hn : records.length ≤ K) :
    WordBound K (rowCountState regs records (List.replicate records.length true)) := by
  intro i
  by_cases h1 : i=1
  · subst i; simpa [rowCountState] using hb
  by_cases h2 : i=2
  · subst i; simpa [rowCountState] using hn
  simp [rowCountState,h1,h2]

theorem cacheState_wordBound (regs : Fin 8 → Bool) (height R width : List Bool)
    (words : List (List Bool)) (K : ℕ)
    (hh : height.length ≤ K) (hr : R.length ≤ K) (hw : width.length ≤ K)
    (hp : words.flatten.length ≤ K) (hn : R.length*width.length ≤ K)
    (hd : (LayoutProgram.IntegerCache.denominatorWord R.length).length ≤ K) :
    WordBound K (cacheState regs height R width words) := by
  intro i
  fin_cases i <;> simp_all [cacheState,LayoutProgram.IntegerCache.state]

theorem bootState_wordBound (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (r t : ℕ) (records : List (List Bool)) (height R width : List Bool)
    (words : List (List Bool)) (K : ℕ) (ha : WordBound K a)
    (hab : WordBound K (Address.result ra r t))
    (hdb : WordBound K (rowCountState rd records (List.replicate records.length true)))
    (hcb : WordBound K (cacheState rc height R width words)) :
    WordBound K (bootState a ra rd rc r t records height R width words) := by
  have hb : WordBound K (addressState a ra r t) := returned_wordBound _ _ _ _ _ _ K
    addressInputs_protected addressOutputs_protected (by decide) (by decide) ha hab
  have hc : WordBound K (countedState (addressState a ra r t) rd records) :=
    returned_wordBound _ _ _ _ _ _ K rowCountInputs_protected rowCountOutputs_protected
      (by decide) (by decide) hb hdb
  exact returned_wordBound _ _ _ _ _ _ K cacheInputs_protected cacheOutputs_protected
    (by decide) (by decide) hc hcb

theorem bootCost_staging (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (r t : ℕ) (records : List (List Bool)) (height R width : List Bool)
    (words : List (List Bool)) (K : ℕ) (ha : WordBound K a)
    (hab : WordBound K (Address.result ra r t))
    (hdb : WordBound K (rowCountState rd records (List.replicate records.length true)))
    (hcb : WordBound K (cacheState rc height R width words)) :
    bootCost a ra rd rc r t records height R width words ≤
      Address.budget r t+(SubexponentialSAT.SubexpScopeCountSetup.countBudget records+1)+cacheBound height R width+
        451*(K+1) := by
  have hb : WordBound K (addressState a ra r t) := returned_wordBound _ _ _ _ _ _ K
    addressInputs_protected addressOutputs_protected (by decide) (by decide) ha hab
  have hc : WordBound K (countedState (addressState a ra r t) rd records) :=
    returned_wordBound _ _ _ _ _ _ K rowCountInputs_protected rowCountOutputs_protected
      (by decide) (by decide) hb hdb
  have h1 := stageCost_linear addressRegs (by decide) addressInputs addressOutputs a
    (Address.result ra r t) (Address.budget r t) K addressInputs_protected addressOutputs_protected
    (by decide) (by decide) ha hab
  have h2 := stageCost_linear rowCountRegs (by decide) rowCountInputs rowCountOutputs
    (addressState a ra r t) (rowCountState rd records (List.replicate records.length true))
    (SubexponentialSAT.SubexpScopeCountSetup.countBudget records+1) K rowCountInputs_protected rowCountOutputs_protected
    (by decide) (by decide) hb hdb
  have h3 := stageCost_linear cacheRegs (by decide) cacheInputs cacheOutputs
    (countedState (addressState a ra r t) rd records) (cacheState rc height R width words)
    (cacheBound height R width) K cacheInputs_protected cacheOutputs_protected
    (by decide) (by decide) hc hcb
  norm_num [addressInputs,addressOutputs,rowCountInputs,rowCountOutputs,cacheInputs,cacheOutputs] at h1 h2 h3
  unfold bootCost addressInputs addressOutputs rowCountInputs rowCountOutputs cacheInputs cacheOutputs
  omega

theorem retainedState_wordBound (a : Data) (K : ℕ) (ha : WordBound K a) :
    WordBound (2*K) (retainedState a) := by
  intro i
  by_cases h710 : i=710
  · subst i; rw [retainedState_positive_append,List.length_append]; have := ha 640; have := ha 710; omega
  by_cases h711 : i=711
  · subst i; rw [retainedState_negative_append,List.length_append]; have := ha 641; have := ha 711; omega
  by_cases h712 : i=712
  · subst i; rw [retainedState_denominator_append,List.length_append]; have := ha 642; have := ha 712; omega
  by_cases h659 : i=659
  · subst i
    simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
      clearMany_stacks,retainedPorts]
  rw [retainedState_frame a i h659 h710 h711 h712]
  have := ha i
  omega

theorem tupleInitialized_wordBound (a : Data) (K : ℕ) (ha : WordBound K a) :
    WordBound (K+3) (tupleInitialized a) := by
  intro i
  by_cases h665 : i=665
  · subst i
    simp only [tupleInitialized,Function.update_self,List.length_cons]
    have := ha 665
    omega
  by_cases h660 : i=660
  · subst i
    simpa [tupleInitialized] using ha 660
  simpa [tupleInitialized,h660,h665] using (ha i).trans (Nat.le_add_right K 3)

theorem initializeCost_staging (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (r t : ℕ) (records : List (List Bool)) (height R width : List Bool)
    (words : List (List Bool)) (K : ℕ) (ha : WordBound K a)
    (hab : WordBound K (Address.result ra r t))
    (hdb : WordBound K (rowCountState rd records (List.replicate records.length true)))
    (hcb : WordBound K (cacheState rc height R width words)) :
    initializeCost a ra rd rc r t records height R width words ≤
      Address.budget r t+(SubexponentialSAT.SubexpScopeCountSetup.countBudget records+1)+cacheBound height R width+
        500*(K+1) ∧
      WordBound (2*K+3) (nodeStart a ra rd rc r t records height R width words) := by
  have hb := bootState_wordBound a ra rd rc r t records height R width words K ha hab hdb hcb
  constructor
  · have hc := bootCost_staging a ra rd rc r t records height R width words K ha hab hdb hcb
    have h0 := hb 659
    have h1 := hb 640
    have h2 := hb 641
    have h3 := hb 642
    unfold initializeCost
    rw [retainCost_linear]
    omega
  · exact tupleInitialized_wordBound _ (2*K) (retainedState_wordBound _ K hb)

theorem records_lengths_bound (records : List (List Bool)) :
    (records.map List.length).sum ≤ (SubexponentialSAT.Encoding.encodeList id records).length := by
  induction records with
  | nil => simp
  | cons row rows ih => simp only [List.map_cons,List.sum_cons,SubexponentialSAT.Encoding.length_encodeList_cons,id_eq]; omega

theorem rowCountBudget_linear (records : List (List Bool)) :
    SubexponentialSAT.SubexpScopeCountSetup.countBudget records ≤ 17*(SubexponentialSAT.Encoding.encodeList id records).length+10 := by
  have hs := records_lengths_bound records
  have hn := SubexponentialSAT.Encoding.length_encodeList_lower id records
  unfold SubexponentialSAT.SubexpScopeCountSetup.countBudget SubexponentialSAT.SubexpSunflowerProgram.CountRecords.loopSteps
  omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
