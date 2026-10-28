import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainFieldCacheCore
import OAI.Algorithms.SubexponentialSAT.SubexpMainFieldNodes

namespace OAI.Algorithms

/-!
# The source-field cache phase in the Main workspace

The lifted target-node table is moved from ordinary14 to ordinary300 before
the source-field cache uses low workspace. Source ring words at128..133 are
retained; framed source nodes at134 become flat nodes at134, and the actual
inverse, negative, and row-major inverse-difference arrays occupy135..137.
-/

namespace SubexponentialSAT.SubexpMainFieldCache

open BitProgram StructuredCalls SubexpMainProgram
open BinaryArithmetic SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

structure Allocation (es : ℕ) where
  ordinaryCount : ℕ
  enough : 301 ≤ ordinaryCount
  within : ordinaryCount ≤ workStacks es

def nodeAllocation {es : ℕ} (alloc : Allocation es) : SubexpMainFieldNodes.Allocation es where
  ordinaryCount := alloc.ordinaryCount
  enough := by have := alloc.enough; omega
  within := alloc.within

def ringAllocation {es : ℕ} (alloc : Allocation es) : SubexpMainPreparedRings.Allocation es :=
  SubexpMainFieldNodes.ringAllocation (nodeAllocation alloc)

def ordinary {es : ℕ} (alloc : Allocation es) (i : Fin 301) : Fin (totalStacks es) :=
  ⟨i.val, by have := alloc.enough; have := alloc.within; dsimp [totalStacks]; omega⟩

def stackMap {es : ℕ} (alloc : Allocation es) (i : Fin 140) : Fin (totalStacks es) :=
  if hi : i.val < 138 then ordinary alloc ⟨i.val, by omega⟩
  else if i = 138 then ordinary alloc 300 else persistent es 29

theorem stackMap_val {es : ℕ} (alloc : Allocation es) (i : Fin 140) :
    (stackMap alloc i).val =
      if i.val < 138 then i.val else if i = 138 then 300 else workStacks es + 29 := by
  unfold stackMap
  split
  · rfl
  · split
    · rfl
    · rfl

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (stackMap alloc) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [stackMap_val alloc i, stackMap_val alloc j] at hv
  by_cases hi : i.val < 138 <;> by_cases hj : j.val < 138
  · apply Fin.ext
    simpa only [ite_eq_left hi, ite_eq_left hj] using hv
  · by_cases hj' : j = 138
    · simp only [ite_eq_left hi, ite_eq_right hj, ite_eq_left hj'] at hv
      omega
    · simp only [ite_eq_left hi, ite_eq_right hj, ite_eq_right hj'] at hv
      have hw := alloc.enough.trans alloc.within
      omega
  · by_cases hi' : i = 138
    · simp only [ite_eq_right hi, ite_eq_left hi', ite_eq_left hj] at hv
      omega
    · simp only [ite_eq_right hi, ite_eq_right hi', ite_eq_left hj] at hv
      have hw := alloc.enough.trans alloc.within
      omega
  · by_cases hi' : i = 138 <;> by_cases hj' : j = 138
    · exact hi'.trans hj'.symm
    · simp only [ite_eq_right hi, ite_eq_left hi', ite_eq_right hj,
        ite_eq_right hj'] at hv
      have hw := alloc.enough.trans alloc.within
      omega
    · simp only [ite_eq_right hi, ite_eq_right hi', ite_eq_right hj,
        ite_eq_left hj'] at hv
      have hw := alloc.enough.trans alloc.within
      omega
    · apply Fin.ext
      have hi139 : i.val = 139 := by
        have hn : i.val ≠ 138 := fun he => hi' (Fin.ext he)
        omega
      have hj139 : j.val = 139 := by
        have hn : j.val ≠ 138 := fun he => hj' (Fin.ext he)
        omega
      omega

@[simp] theorem stackMap_low {es : ℕ} (alloc : Allocation es) (i : Fin 138) :
    stackMap alloc (i.castAdd 2) = ordinary alloc ⟨i.val, by omega⟩ := by
  simp only [stackMap, Fin.val_castAdd, dite_eq_left i.isLt]

@[simp] theorem stackMap_saved {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 138 = ordinary alloc 300 := rfl

@[simp] theorem stackMap_exponent {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 139 = persistent es 29 := rfl

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 140
  labels := size SubexpMainFieldCacheCore.command + 1
  program := SubexpMainFieldCacheCore.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h; exact Fin.ext (congrArg (fun q : Fin (workRegs er) => q.val) h)⟩
  stack := ⟨stackMap alloc, stackMap_injective alloc⟩

def program (er : ℕ) {es : ℕ} (alloc : Allocation es) :=
  ProgramLinking.liftProgram (procedure er alloc).program
    (procedure er alloc).registerMap (procedure er alloc).stack

/-- Initial emptiness outside the previous producers' cleared work areas.
The ring producer clears0..35, and the node producer replaces only0..19 and134. -/
def initiallyEmpty (i : Fin 301) : Prop :=
  (36 ≤ i.val ∧ i.val < 110) ∨ (135 ≤ i.val ∧ i.val ≤ 137) ∨ i = 300

theorem ready_from_phases {er es : ℕ} (alloc : Allocation es)
    (a b d : MainState er es) (p D : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (hp : SubexpMainPreparedRings.Result (ringAllocation alloc) a b p D coeff hc)
    (hn : SubexpMainFieldNodes.Result (nodeAllocation alloc) b d p (D + 1)
      (SubexpPreparedQuarticSetup.modulus p 1))
    (he : ∀ i, initiallyEmpty i → a.stacks (ordinary alloc i) = []) :
    SubexpMainFieldCacheCore.Ready ((procedure er alloc).project d) p coeff hc := by
  have hw := alloc.enough.trans alloc.within
  constructor
  · intro i
    have hnode := hn.sourceCache_frame i
    have hprep := hp.source i
    have hmap : stackMap alloc (SubexpMainFieldCacheCore.bankPort i) =
        SubexpMainPreparedRings.sourcePort (ringAllocation alloc) i := by
      have hlow := stackMap_low alloc (⟨128 + i.val, by omega⟩ : Fin 138)
      change stackMap alloc (SubexpMainFieldCacheCore.bankPort i) =
        ordinary alloc ⟨128 + i.val, by omega⟩ at hlow
      rw [hlow]
      apply Fin.ext
      rfl
    change d.stacks (stackMap alloc (SubexpMainFieldCacheCore.bankPort i)) = _
    rw [hmap]
    exact hnode.trans hprep
  · exact hn.source
  · intro i hi
    rcases hi with ⟨hi, h14⟩ | ⟨h135, h138⟩
    · have hm : stackMap alloc i = ordinary alloc ⟨i.val, by omega⟩ := by
        simp only [stackMap, dite_eq_left (show i.val < 138 by omega)]
      change d.stacks (stackMap alloc i) = []
      rw [hm]
      by_cases h20 : i.val < 20
      · exact hn.scratch ⟨i.val, h20⟩ (by
          intro h; apply h14; exact Fin.ext (congrArg (fun q : Fin 20 => q.val) h))
      · rw [hn.frame _ (by simpa only [ordinary] using (show 20 ≤ i.val by omega))
          (by simp only [ordinary]; omega)]
        by_cases h36 : i.val < 36
        · exact hp.scratch ⟨i.val, h36⟩
        · rw [hp.work_frame _ (by simp only [ordinary]; omega)
            (Or.inl (by simp only [ordinary]; omega)) (by simp only [ordinary]; omega)]
          exact he (⟨i.val, by omega⟩ : Fin 301) (Or.inl ⟨Nat.le_of_not_lt h36, hi⟩)
    · by_cases his : i = 138
      · subst i
        change d.stacks (ordinary alloc 300) = []
        rw [hn.frame _ (by change 20 ≤ 300; decide) (by change 300 ≠ 134; decide),
          hp.work_frame _ (by change 36 ≤ 300; decide)
            (Or.inr (by change 134 ≤ 300; decide)) (by simp only [ordinary]; omega)]
        exact he 300 (Or.inr (Or.inr rfl))
      · have h137 : i.val ≤ 137 := by
          have hne : i.val ≠ 138 := fun hv => his (Fin.ext hv)
          omega
        change d.stacks (stackMap alloc i) = []
        rw [show stackMap alloc i = ordinary alloc ⟨i.val, by omega⟩ by
          simp only [stackMap, dite_eq_left (show i.val < 138 by omega)]]
        rw [hn.frame _ (by simp only [ordinary]; omega) (by simp only [ordinary]; omega),
          hp.work_frame _ (by simp only [ordinary]; omega)
            (Or.inr (by simp only [ordinary]; omega)) (by simp only [ordinary]; omega)]
        exact he ⟨i.val, by omega⟩ (Or.inr (Or.inl ⟨h135, h137⟩))

end SubexponentialSAT.SubexpMainFieldCache

end OAI.Algorithms
