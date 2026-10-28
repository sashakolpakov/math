import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainSparsify
import OAI.Algorithms.SubexponentialSAT.SubexpSetupProcedure

namespace OAI.Algorithms

/-!
# Protected main-program ports for the finite sparsification node

The node has 32 Boolean registers and `k+39` stack ports. Its ordinary ports
0--36 are low workspace; M at 37 is persistent slot 23; unused ports 38/39
use spare persistent slots 30/31. The growing list of fixed-k thresholds at
40 onward is placed after the whole ordinary helper bank. In particular it
does not overlap the leaf algebra workspace when the helper bank is enlarged.
-/

namespace SubexponentialSAT.SubexpNodePorts

open BitProgram StructuredCalls SubexpMainProgram

def address (k es helper : ℕ) (i : Fin (k + 39)) : ℕ :=
  if i.val < 37 then i.val
  else if i.val = 37 then workStacks es + 23
  else if i.val = 38 then workStacks es + 30
  else if i.val = 39 then workStacks es + 31
  else helper + (i.val - 40)

theorem address_lt {k es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (i : Fin (k + 39)) : address k es helper i < totalStacks es := by
  have hi := i.isLt
  unfold address totalStacks
  split_ifs <;> omega

def stackMap {k es : ℕ} (helper : ℕ)
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (i : Fin (k + 39)) : Fin (totalStacks es) :=
  ⟨address k es helper i, address_lt hhelper hfit i⟩

@[simp] theorem stackMap_val {k es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (i : Fin (k + 39)) :
    (stackMap helper hhelper hfit i).val = address k es helper i := rfl

theorem stackMap_injective {k es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es) :
    Function.Injective (stackMap helper hhelper hfit) := by
  intro i j hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have hv := congrArg (fun x : Fin (totalStacks es) => x.val) hij
  change address k es helper i = address k es helper j at hv
  unfold address at hv
  split_ifs at hv <;> omega

def ordinaryPort (k : ℕ) (i : Fin 37) : Fin (k + 39) :=
  i.castLE (by omega)

def mPort (k : ℕ) : Fin (k + 39) := ⟨37, by omega⟩
def sparePort₀ (k : ℕ) : Fin (k + 39) := ⟨38, by omega⟩
def sparePort₁ (k : ℕ) (hk : 1 ≤ k) : Fin (k + 39) := ⟨39, by omega⟩

def thresholdPort (k : ℕ) (i : Fin (k - 1)) : Fin (k + 39) :=
  ⟨40 + i.val, by have := i.isLt; omega⟩

def protectedPort {k es : ℕ} (helper : ℕ)
    (hfit : helper + (k - 1) ≤ workStacks es) (i : Fin (k - 1)) :
    Fin (totalStacks es) :=
  ⟨helper + i.val, by have := i.isLt; unfold totalStacks; omega⟩

theorem stackMap_ordinary {k es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es) (i : Fin 37) :
    (stackMap helper hhelper hfit (ordinaryPort k i)).val = i.val := by
  simp only [stackMap_val, address, ordinaryPort, Fin.val_castLE, i.isLt, ite_true]

theorem stackMap_M {k es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es) :
    stackMap helper hhelper hfit (mPort k) = persistent es 23 := by
  apply Fin.ext
  rfl

theorem stackMap_spare₀ {k es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es) :
    stackMap helper hhelper hfit (sparePort₀ k) = persistent es 30 := by
  apply Fin.ext
  rfl

theorem stackMap_spare₁ {k es helper : ℕ} (hk : 1 ≤ k)
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es) :
    stackMap helper hhelper hfit (sparePort₁ k hk) = persistent es 31 := by
  apply Fin.ext
  rfl

theorem stackMap_threshold {k es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (i : Fin (k - 1)) :
    stackMap helper hhelper hfit (thresholdPort k i) = protectedPort helper hfit i := by
  apply Fin.ext
  simp only [stackMap_val, address, thresholdPort, protectedPort]
  split_ifs <;> omega

theorem protectedPort_outside_helpers {k es helper : ℕ}
    (hfit : helper + (k - 1) ≤ workStacks es) (i : Fin (k - 1)) :
    helper ≤ (protectedPort helper hfit i).val := by
  change helper ≤ helper + i.val
  omega

theorem protectedPort_before_persistent {k es helper : ℕ}
    (hfit : helper + (k - 1) ≤ workStacks es) (i : Fin (k - 1)) :
    (protectedPort helper hfit i).val < workStacks es := by
  change helper + i.val < workStacks es
  have := i.isLt
  omega

/-- No node port lies in the expanded ordinary helper region 37..helper-1.
Thresholds remain beyond this region even for arbitrarily large fixed k. -/
theorem stackMap_avoids_middle {k es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (i : Fin (totalStacks es)) (hlo : 37 ≤ i.val) (hhi : i.val < helper) :
    ¬ ∃ j, stackMap helper hhelper hfit j = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg (fun x : Fin (totalStacks es) => x.val) hj
  change address k es helper j = i.val at hv
  unfold address at hv
  split_ifs at hv <;> omega

theorem stackMap_avoids_persistent {k es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (i : Fin 32) (h23 : i ≠ 23) (h30 : i ≠ 30) (h31 : i ≠ 31) :
    ¬ ∃ j, stackMap helper hhelper hfit j = persistent es i := by
  rintro ⟨j, hj⟩
  have hv := congrArg (fun x : Fin (totalStacks es) => x.val) hj
  change address k es helper j = workStacks es + i.val at hv
  have hjlt := j.isLt
  have hn23 : i.val ≠ 23 := fun h => h23 (Fin.ext h)
  have hn30 : i.val ≠ 30 := fun h => h30 (Fin.ext h)
  have hn31 : i.val ≠ 31 := fun h => h31 (Fin.ext h)
  unfold address at hv
  split_ifs at hv <;> omega

def registerMap {er : ℕ} (hr : 32 ≤ workRegs er) (i : Fin 32) : Fin (workRegs er) :=
  i.castLE hr

theorem registerMap_injective {er : ℕ} (hr : 32 ≤ workRegs er) :
    Function.Injective (registerMap hr) := Fin.castLE_injective hr

theorem registerMap_core {er es : ℕ} (hr : 32 ≤ workRegs er) (i : Fin 4) :
    registerMap hr (i.castAdd 28) = (SubexpMainSparsify.mainPorts er es).register i := by
  apply Fin.ext
  rfl

theorem stackMap_core {k er es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es) (i : Fin 5) :
    stackMap helper hhelper hfit (i.castLE (by omega)) =
      (SubexpMainSparsify.mainPorts er es).coreStack i := by
  apply Fin.ext
  change address k es helper (i.castLE (by omega)) =
    (SubexpMainSparsify.mainStack es (i.castAdd 2)).val
  rw [SubexpMainSparsify.mainStack_val]
  have hi37 : i.val < 37 := by have := i.isLt; omega
  simp only [address, Fin.val_castLE, Fin.val_castAdd, hi37, i.isLt, ite_true]

/-- This is the actual instruction-table relocation, with no semantic
operations added to the target machine. -/
abbrev liftNode {k er es labels : ℕ} (p : Program 32 (k + 39) labels)
    (helper : ℕ) (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (hr : 32 ≤ workRegs er) : Program (workRegs er) (totalStacks es) labels :=
  ProgramLinking.liftProgram p (registerMap hr) (stackMap helper hhelper hfit)

theorem liftNode_call {k er es labels : ℕ} (p : Program 32 (k + 39) labels)
    (helper : ℕ) (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (hr : 32 ≤ workRegs er) (frame : State (workRegs er) (totalStacks es))
    (out : State 32 (k + 39)) (bound : ℕ)
    (h : RunsIn p bound
      ((projectState (registerMap hr) (stackMap helper hhelper hfit) frame).withPC (some p.entry))
      (out.withPC none)) :
    ∃ steps ≤ bound, Eval (.call (liftNode p helper hhelper hfit hr)) steps frame
      (embedState (registerMap hr) (stackMap helper hhelper hfit) frame out) := by
  obtain ⟨steps, hsteps, ht⟩ := h
  exact ⟨steps, hsteps, eval_call_from_state p _ _ frame
    (registerMap_injective hr) (stackMap_injective hhelper hfit) ht⟩

/-! ## Exact specialization to the published setup storage layout -/

theorem setup_fit (c : SubexpSetupProgram.Config) :
    SubexpSetupProgram.helperSize c + (c.k - 1) =
      workStacks (SubexpSetupProgram.mainExtraStacks c) := by
  unfold SubexpSetupProgram.helperSize SubexpSetupProgram.mainExtraStacks
    SubexpSetupProgram.thresholdCount workStacks
  omega

def setupStackMap (c : SubexpSetupProgram.Config) :
    Fin (c.k + 39) → Fin (totalStacks (SubexpSetupProgram.mainExtraStacks c)) :=
  stackMap (SubexpSetupProgram.helperSize c)
    (by have := SubexpSetupProgram.helperSize_ge c; omega) (setup_fit c).le

theorem setupStackMap_injective (c : SubexpSetupProgram.Config) :
    Function.Injective (setupStackMap c) := stackMap_injective _ _

theorem setupStackMap_M (c : SubexpSetupProgram.Config) :
    setupStackMap c (mPort c.k) =
      persistent (SubexpSetupProgram.mainExtraStacks c) 23 := stackMap_M _ _

theorem setupStackMap_threshold (c : SubexpSetupProgram.Config)
    (i : Fin (c.k - 1)) :
    setupStackMap c (thresholdPort c.k i) =
      SubexpSetupProgram.mainStack c (SubexpSetupProgram.threshold c i) := by
  rw [setupStackMap, stackMap_threshold]
  apply Fin.ext
  rfl

theorem setupStackMap_avoids_leaf_workspace (c : SubexpSetupProgram.Config)
    (i : Fin (totalStacks (SubexpSetupProgram.mainExtraStacks c)))
    (hlo : 37 ≤ i.val) (hhi : i.val < SubexpSetupProgram.helperSize c) :
    ¬ ∃ j, setupStackMap c j = i := stackMap_avoids_middle _ _ i hlo hhi

end SubexponentialSAT.SubexpNodePorts

end OAI.Algorithms
