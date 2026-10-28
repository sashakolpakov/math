import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowContext

namespace OAI.Algorithms

/-! Persistent and high-workspace frames for the actual row preparation. -/

namespace SubexponentialSAT.SubexpMainRowPreparation

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)

attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem header_target_lt320 {es : ℕ} (alloc : Allocation es) (i : Fin 6) :
    (SubexpMainRowHeader.targetPort alloc i).val < 320 := by
  fin_cases i <;> norm_num [SubexpMainRowHeader.targetPort, ordinary]

theorem result_high_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin (totalStacks es)) (hlo : 320 ≤ i.val) (hhi : i.val < workStacks es) :
    (result alloc a).stacks i = a.stacks i := by
  change (SubexpMainRowHeader.installed alloc
    (SubexpMainRowSetup.contextResult alloc (pre alloc a))).stacks i = _
  rw [SubexpMainRowHeader.installed_frame alloc _ i]
  · exact (SubexpMainRowSetup.context_high_frame alloc _ i (by omega) hhi).trans
      (SubexpMainRowPreclear.result_high_frame alloc a i (by omega))
  · intro j he
    have h := header_target_lt320 alloc j
    rw [he] at h
    omega
  · intro he
    have hv := congrArg (fun j : Fin (totalStacks es) => j.val) he
    change 319 = i.val at hv
    omega

theorem result_master {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 32) : (result alloc a).stacks (master alloc i) = a.stacks (master alloc i) := by
  apply result_high_frame
  · rw [SubexpLayoutPorts.master_val]
    omega
  · exact (SubexpLayoutPorts.master_below_cleanup alloc i).trans_le alloc.within

theorem result_threshold {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin (totalStacks es)) (hlo : alloc.ordinaryCount ≤ i.val)
    (hhi : i.val < workStacks es) : (result alloc a).stacks i = a.stacks i :=
  result_high_frame alloc a i (by have := alloc.enough; omega) hhi

theorem result_persistent {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 32) : (result alloc a).stacks (persistent es i) = a.stacks (persistent es i) := by
  have hw := alloc.enough.trans alloc.within
  change (SubexpMainRowHeader.installed alloc
    (SubexpMainRowSetup.contextResult alloc (pre alloc a))).stacks (persistent es i) = _
  rw [SubexpMainRowHeader.installed_frame alloc _ (persistent es i)]
  · exact (SubexpSourceRowContext.Main.persistent_frame er
      (SubexpMainRowSetup.contextAllocation alloc) (pre alloc a) i).trans
        (SubexpMainRowPreclear.result_persistent alloc a i)
  · intro j he
    have h := header_target_lt320 alloc j
    rw [he] at h
    simp only [persistent, Fin.val_natAdd] at h
    omega
  · intro he
    have hv := congrArg (fun j : Fin (totalStacks es) => j.val) he
    change 319 = workStacks es + i.val at hv
    omega

theorem result_control {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 3) : (result alloc a).regs (controlRegister er i) = a.regs (controlRegister er i) := by
  change (SubexpMainRowHeader.installed alloc
    (SubexpMainRowSetup.contextResult alloc (pre alloc a))).regs (controlRegister er i) = _
  rw [SubexpMainRowHeader.installed_control]
  have h := Procedure.install_control (SubexpMainRowSetup.contextProcedure er alloc)
    (pre alloc a) (SubexpSourceRowContext.result (SubexpMainRowSetup.projected alloc (pre alloc a))) i
  exact h.trans (SubexpMainRowPreclear.result_control alloc a i)

end SubexponentialSAT.SubexpMainRowPreparation

end OAI.Algorithms
