import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedRingStaging
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram
import OAI.Algorithms.SubexponentialSAT.SubexpSetupProcedure
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

namespace OAI.Algorithms

/-!
# Prepared-ring staging in the Main persistent ABI

The fixed local program copies persistent 6/22/15, computes the target ring,
and then computes the source ring with the physical precision word `[true]`.
Target caches replace persistent 12/13/14/28/30/31; source caches occupy
ordinary stacks 128..133. Staging owns and clears ordinary stacks 0..35.

The allocation requires the source bank to be below the ordinary-workspace
boundary, not merely below the end of all work stacks. Thus the threshold
extension, pending leaf stream, and parser payload are framed. Callers must
place this phase after the scalar readiness guard and coefficient producer,
and before other live data occupy the staging workspace.
-/

namespace SubexponentialSAT.SubexpMainPreparedRings

open BitProgram StructuredCalls SubexpMainProgram
open BinaryArithmetic SubexpLiftRing SubexpQuarticRing

/-- The threshold bank starts at `ordinaryCount`. Both ring banks must remain
disjoint from that bank even when the ambient workspace has extra stacks. -/
structure Allocation (es : ℕ) where
  ordinaryCount : ℕ
  enough : 134 ≤ ordinaryCount
  within : ordinaryCount ≤ workStacks es

/-- The numerical setup already allocates enough ordinary workspace. This
uses its published size theorem and adds no input-dependent program field. -/
def setupAllocation (c : SubexpSetupProgram.Config) :
    Allocation (SubexpSetupProgram.mainExtraStacks c) where
  ordinaryCount := SubexpSetupProgram.helperSize c
  enough := by have := SubexpSetupProgram.helperSize_ge c; omega
  within := by
    unfold SubexpSetupProgram.helperSize SubexpSetupProgram.mainExtraStacks workStacks
    omega

def inputIndex : Fin 3 → Fin 32 := ![6, 22, 15]
def targetIndex : Fin 6 → Fin 32 := ![12, 13, 14, 28, 30, 31]
def persistentIndex : Fin 9 → Fin 32 := ![6, 22, 15, 12, 13, 14, 28, 30, 31]
def inputIndices : List (Fin 32) := List.ofFn inputIndex
def targetIndices : List (Fin 32) := List.ofFn targetIndex

def lowPort (es : ℕ) (i : Fin 36) : Fin (totalStacks es) :=
  ⟨i.val, by dsimp [totalStacks, workStacks]; omega⟩

def sourcePort {es : ℕ} (alloc : Allocation es) (i : Fin 6) : Fin (totalStacks es) :=
  ⟨128 + i.val, by have := alloc.enough; have := alloc.within; dsimp [totalStacks]; omega⟩

def stackMap {es : ℕ} (alloc : Allocation es) (i : Fin 51) : Fin (totalStacks es) :=
  if hlow : i.val < 36 then lowPort es ⟨i.val, hlow⟩
  else if hmid : i.val < 45 then persistent es (persistentIndex ⟨i.val - 36, by omega⟩)
  else sourcePort alloc ⟨i.val - 45, by omega⟩

theorem stackMap_eq_low {es : ℕ} (alloc : Allocation es) (i : Fin 51)
    (hi : i.val < 36) : stackMap alloc i = lowPort es ⟨i.val, hi⟩ := by
  unfold stackMap
  rw [dite_eq_left hi]

theorem stackMap_eq_mid {es : ℕ} (alloc : Allocation es) (i : Fin 51)
    (hlow : ¬i.val < 36) (hmid : i.val < 45) :
    stackMap alloc i = persistent es (persistentIndex ⟨i.val - 36, by omega⟩) := by
  unfold stackMap
  rw [dite_eq_right hlow, dite_eq_left hmid]

theorem stackMap_eq_high {es : ℕ} (alloc : Allocation es) (i : Fin 51)
    (hlow : ¬i.val < 36) (hmid : ¬i.val < 45) :
    stackMap alloc i = sourcePort alloc ⟨i.val - 45, by omega⟩ := by
  unfold stackMap
  rw [dite_eq_right hlow, dite_eq_right hmid]

theorem sourcePort_below_boundary {es : ℕ} (alloc : Allocation es) (i : Fin 6) :
    (sourcePort alloc i).val < alloc.ordinaryCount := by
  have := alloc.enough
  simp only [sourcePort]
  omega

theorem sourcePort_ne_persistent {es : ℕ} (alloc : Allocation es) (i : Fin 6) (j : Fin 32) :
    sourcePort alloc i ≠ persistent es j := by
  intro h
  have hlo := sourcePort_below_boundary alloc i
  have hhi := alloc.within
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
  simp only [persistent, Fin.val_natAdd] at hv
  omega

theorem persistentIndex_injective : Function.Injective persistentIndex := by decide

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (stackMap alloc) := by
  intro i j h
  by_cases hi : i.val < 36 <;> by_cases hj : j.val < 36
  · apply Fin.ext
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
    rw [stackMap_eq_low alloc i hi, stackMap_eq_low alloc j hj] at hv
    exact hv
  · by_cases hj' : j.val < 45
    · have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
      rw [stackMap_eq_low alloc i hi, stackMap_eq_mid alloc j hj hj'] at hv
      simp only [lowPort, persistent, Fin.val_natAdd] at hv
      have := alloc.enough
      have := alloc.within
      omega
    · have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
      rw [stackMap_eq_low alloc i hi, stackMap_eq_high alloc j hj hj'] at hv
      simp only [lowPort, sourcePort] at hv
      omega
  · by_cases hi' : i.val < 45
    · have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
      rw [stackMap_eq_mid alloc i hi hi', stackMap_eq_low alloc j hj] at hv
      simp only [persistent, Fin.val_natAdd, lowPort] at hv
      have := alloc.enough
      have := alloc.within
      omega
    · have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
      rw [stackMap_eq_high alloc i hi hi', stackMap_eq_low alloc j hj] at hv
      simp only [sourcePort, lowPort] at hv
      omega
  · by_cases hi' : i.val < 45 <;> by_cases hj' : j.val < 45
    · rw [stackMap_eq_mid alloc i hi hi', stackMap_eq_mid alloc j hj hj'] at h
      have he := persistent_injective es h
      have hd := congrArg (fun q : Fin 9 => q.val) (persistentIndex_injective he)
      apply Fin.ext
      dsimp only at hd
      omega
    · have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
      rw [stackMap_eq_mid alloc i hi hi', stackMap_eq_high alloc j hj hj'] at hv
      simp only [persistent, Fin.val_natAdd, sourcePort] at hv
      have := alloc.enough
      have := alloc.within
      omega
    · have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
      rw [stackMap_eq_high alloc i hi hi', stackMap_eq_mid alloc j hj hj'] at hv
      simp only [sourcePort, persistent, Fin.val_natAdd] at hv
      have := alloc.enough
      have := alloc.within
      omega
    · apply Fin.ext
      have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
      rw [stackMap_eq_high alloc i hi hi', stackMap_eq_high alloc j hj hj'] at hv
      simp only [sourcePort] at hv
      omega

@[simp] theorem stackMap_low {es : ℕ} (alloc : Allocation es) (i : Fin 36) :
    stackMap alloc (i.castAdd 15) = lowPort es i := by
  simp only [stackMap, Fin.val_castAdd, dite_eq_left i.isLt]

@[simp] theorem stackMap_input {es : ℕ} (alloc : Allocation es) (i : Fin 3) :
    stackMap alloc (SubexpPreparedRingStaging.inputPort i) = persistent es (inputIndex i) := by
  fin_cases i <;> rfl

@[simp] theorem stackMap_target {es : ℕ} (alloc : Allocation es) (i : Fin 6) :
    stackMap alloc (SubexpPreparedRingStaging.destination false i) =
      persistent es (targetIndex i) := by
  fin_cases i <;> rfl

@[simp] theorem stackMap_source {es : ℕ} (alloc : Allocation es) (i : Fin 6) :
    stackMap alloc (SubexpPreparedRingStaging.destination true i) = sourcePort alloc i := by
  fin_cases i <;> rfl

theorem stackMap_avoids_persistent {es : ℕ} (alloc : Allocation es) (i : Fin 32)
    (hi : i ∉ inputIndices ++ targetIndices) :
    ¬ ∃ j, stackMap alloc j = persistent es i := by
  rintro ⟨j, hj⟩
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) hj
  have henough := alloc.enough.trans alloc.within
  by_cases hlow : j.val < 36
  · rw [stackMap_eq_low alloc j hlow] at hv
    simp only [lowPort, persistent, Fin.val_natAdd] at hv
    omega
  by_cases hmid : j.val < 45
  · rw [stackMap_eq_mid alloc j hlow hmid] at hj
    have he := persistent_injective es hj
    apply hi
    rw [← he]
    have hall : ∀ q, persistentIndex q ∈ inputIndices ++ targetIndices := by decide
    exact hall _
  · rw [stackMap_eq_high alloc j hlow hmid] at hv
    simp only [sourcePort, persistent, Fin.val_natAdd] at hv
    omega

theorem stackMap_avoids_work {es : ℕ} (alloc : Allocation es) (i : Fin (totalStacks es))
    (hlow : 36 ≤ i.val) (hcache : i.val < 128 ∨ 134 ≤ i.val)
    (hwork : i.val < workStacks es) : ¬ ∃ j, stackMap alloc j = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) hj
  by_cases hsmall : j.val < 36
  · rw [stackMap_eq_low alloc j hsmall] at hv
    simp only [lowPort] at hv
    omega
  by_cases hmid : j.val < 45
  · rw [stackMap_eq_mid alloc j hsmall hmid] at hv
    simp only [persistent, Fin.val_natAdd] at hv
    omega
  · rw [stackMap_eq_high alloc j hsmall hmid] at hv
    simp only [sourcePort] at hv
    omega

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 51
  labels := size SubexpPreparedRingStaging.command + 1
  program := SubexpPreparedRingStaging.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun q : Fin (workRegs er) => q.val) h)⟩
  stack := ⟨stackMap alloc, stackMap_injective alloc⟩

def program (er : ℕ) {es : ℕ} (alloc : Allocation es) :=
  ProgramLinking.liftProgram (procedure er alloc).program
    (procedure er alloc).registerMap (procedure er alloc).stack

structure Result {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (p D : ℕ) [Fact p.Prime] (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)) : Prop where
  target : ∀ i, b.stacks (persistent es (targetIndex i)) =
    SubexpPreparedRingStaging.bankWords p D coeff hc i
  source : ∀ i, b.stacks (sourcePort alloc i) =
    SubexpPreparedRingStaging.bankWords p 0 coeff hc i
  inputs : ∀ i, b.stacks (persistent es (inputIndex i)) = a.stacks (persistent es (inputIndex i))
  scratch : ∀ i, b.stacks (lowPort es i) = []
  frame : ∀ i, (¬ ∃ j, stackMap alloc j = i) → b.stacks i = a.stacks i
  registers : ∀ i : Fin 16, b.regs ((procedure er alloc).registerMap i) = false
  registerFrame : ∀ i, (¬ ∃ j, (procedure er alloc).registerMap j = i) → b.regs i = a.regs i
  controls : ∀ i, b.regs (controlRegister er i) = a.regs (controlRegister er i)

namespace Result

theorem persistent_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {p D : ℕ} [Fact p.Prime] {coeff : Quad (Word (baseWidth p 1))}
    {hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)}
    (h : Result alloc a b p D coeff hc) (i : Fin 32) (hi : i ∉ targetIndices) :
    b.stacks (persistent es i) = a.stacks (persistent es i) := by
  by_cases hin : i ∈ inputIndices
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hin
    exact h.inputs j
  · exact h.frame _ (stackMap_avoids_persistent alloc i (by simpa only [List.mem_append, not_or] using And.intro hin hi))

theorem pending {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {p D : ℕ} [Fact p.Prime] {coeff : Quad (Word (baseWidth p 1))}
    {hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)}
    (h : Result alloc a b p D coeff hc) :
    b.stacks (persistent es 7) = a.stacks (persistent es 7) :=
  h.persistent_frame 7 (by decide)

theorem payload {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {p D : ℕ} [Fact p.Prime] {coeff : Quad (Word (baseWidth p 1))}
    {hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)}
    (h : Result alloc a b p D coeff hc) :
    b.stacks (persistent es 8) = a.stacks (persistent es 8) :=
  h.persistent_frame 8 (by decide)

theorem threshold_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {p D : ℕ} [Fact p.Prime] {coeff : Quad (Word (baseWidth p 1))}
    {hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)}
    (h : Result alloc a b p D coeff hc) (i : Fin (totalStacks es))
    (hstart : alloc.ordinaryCount ≤ i.val) (hend : i.val < workStacks es) :
    b.stacks i = a.stacks i := by
  have hn := alloc.enough
  exact h.frame i (stackMap_avoids_work alloc i (by omega) (Or.inr (by omega)) hend)

/-- Additional ordinary caches, including the node/inverse bank at 134..137,
are preserved as well as the protected threshold extension. -/
theorem work_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {p D : ℕ} [Fact p.Prime] {coeff : Quad (Word (baseWidth p 1))}
    {hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)}
    (h : Result alloc a b p D coeff hc) (i : Fin (totalStacks es))
    (hlow : 36 ≤ i.val) (hcache : i.val < 128 ∨ 134 ≤ i.val)
    (hwork : i.val < workStacks es) : b.stacks i = a.stacks i :=
  h.frame i (stackMap_avoids_work alloc i hlow hcache hwork)

theorem target_width {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {p D : ℕ} [Fact p.Prime] {coeff : Quad (Word (baseWidth p 1))}
    {hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)}
    (h : Result alloc a b p D coeff hc) :
    (b.stacks (persistent es 13)).length = baseWidth p (D + 1) := by
  have hw := h.target 1
  change b.stacks (persistent es 13) = SubexpPreparedQuarticPrelude.widthWord p (D + 1) at hw
  rw [hw, SubexpPreparedQuarticPrelude.widthWord_length]

theorem source_width {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {p D : ℕ} [Fact p.Prime] {coeff : Quad (Word (baseWidth p 1))}
    {hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)}
    (h : Result alloc a b p D coeff hc) :
    (b.stacks (sourcePort alloc 1)).length = baseWidth p 1 := by
  have hw := h.source 1
  change b.stacks (sourcePort alloc 1) = SubexpPreparedQuarticPrelude.widthWord p 1 at hw
  rw [hw, SubexpPreparedQuarticPrelude.widthWord_length]

theorem target_zero {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {p D : ℕ} [Fact p.Prime] {coeff : Quad (Word (baseWidth p 1))}
    {hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)}
    (h : Result alloc a b p D coeff hc) :
    b.stacks (persistent es 28) = List.replicate (4 * baseWidth p (D + 1)) false :=
  (h.target 3).trans (SubexpPreparedRingStaging.bankWords_zero p D coeff hc)

theorem source_zero {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {p D : ℕ} [Fact p.Prime] {coeff : Quad (Word (baseWidth p 1))}
    {hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)}
    (h : Result alloc a b p D coeff hc) :
    b.stacks (sourcePort alloc 3) = List.replicate (4 * baseWidth p 1) false :=
  (h.source 3).trans (SubexpPreparedRingStaging.bankWords_zero p 0 coeff hc)

end Result

theorem install_result {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpPreparedRingStaging.Data) (p D : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (hr : SubexpPreparedRingStaging.Result ((procedure er alloc).project a) out p D coeff hc) :
    Result alloc a ((procedure er alloc).install a out) p D coeff hc := by
  have hs (i : Fin 51) := embedState_stack (procedure er alloc).registerMap
    (procedure er alloc).stack a out (procedure er alloc).stack.injective i
  constructor
  · intro i
    have hh := hs (SubexpPreparedRingStaging.destination false i)
    change ((procedure er alloc).install a out).stacks (stackMap alloc _) = _ at hh
    rw [stackMap_target] at hh
    exact hh.trans (hr.target i)
  · intro i
    have hh := hs (SubexpPreparedRingStaging.destination true i)
    change ((procedure er alloc).install a out).stacks (stackMap alloc _) = _ at hh
    rw [stackMap_source] at hh
    exact hh.trans (hr.source i)
  · intro i
    have hh := hs (SubexpPreparedRingStaging.inputPort i)
    change ((procedure er alloc).install a out).stacks (stackMap alloc _) = _ at hh
    rw [stackMap_input] at hh
    rw [hr.inputs] at hh
    change ((procedure er alloc).install a out).stacks (persistent es (inputIndex i)) =
      a.stacks (stackMap alloc (SubexpPreparedRingStaging.inputPort i)) at hh
    simpa only [stackMap_input] using hh
  · intro i
    have hh := hs (i.castAdd 15)
    change ((procedure er alloc).install a out).stacks (stackMap alloc _) = _ at hh
    rw [stackMap_low] at hh
    exact hh.trans (hr.scratch i)
  · intro i hi
    exact embedState_stack_frame _ _ _ _ _ hi
  · intro i
    exact (embedState_register _ _ _ _ (procedure er alloc).registerMap_injective i).trans
      (hr.registers i)
  · intro i hi
    exact embedState_register_frame _ _ _ _ _ hi
  · exact Procedure.install_control _ _ _

/-- Only the 51 physically selected words enter this size bound. In particular,
arbitrarily long pending/parser/threshold data do not affect it. -/
def wordBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (p D : ℕ) : ℕ :=
  SubexpPreparedRingStaging.wordBound ((procedure er alloc).project a) p D

def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (p D : ℕ) : ℕ :=
  SubexpPreparedRingStaging.runtimeBound p D (wordBound alloc a p D)
    (a.stacks (persistent es 6)) (a.stacks (persistent es 22))

/-- Input premises identify the prime, precision, and producer's selected
coefficient bytes. Both prepared caches, their widths, and their storage
frames are outputs of this actual fixed program execution. -/
theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p D : ℕ) [Fact p.Prime] (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (he : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hcoeff : a.stacks (persistent es 15) = SubexpPreparedQuarticSetup.flat coeff) :
    ∃ n ≤ runtimeBound alloc a p D, ∃ b,
      Eval (procedure er alloc).invoke n a b ∧ Result alloc a b p D coeff hc := by
  have hinput (i : Fin 3) : ((procedure er alloc).project a).stacks
      (SubexpPreparedRingStaging.inputPort i) = a.stacks (persistent es (inputIndex i)) := by
    change a.stacks (stackMap alloc _) = _
    rw [stackMap_input]
  have h36 : ((procedure er alloc).project a).stacks (36 : Fin 51) =
      a.stacks (persistent es 6) := hinput 0
  have h37 : ((procedure er alloc).project a).stacks (37 : Fin 51) =
      a.stacks (persistent es 22) := hinput 1
  have h38 : ((procedure er alloc).project a).stacks (38 : Fin 51) =
      a.stacks (persistent es 15) := hinput 2
  obtain ⟨out, hrun, _, hr⟩ := SubexpPreparedRingStaging.run ((procedure er alloc).project a)
    p D coeff hc (by rw [h36]; exact hp) (by rw [h37]; exact he) (h38.trans hcoeff)
  obtain ⟨n, hn, ht⟩ := hrun
  refine ⟨n, ?_, (procedure er alloc).install a out, Procedure.invoke_trace _ _ _ ht,
    install_result alloc a out p D coeff hc hr⟩
  simpa only [runtimeBound, wordBound, h36, h37] using hn

theorem program_runsIn {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p D : ℕ) [Fact p.Prime] (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (he : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hcoeff : a.stacks (persistent es 15) = SubexpPreparedQuarticSetup.flat coeff) :
    ∃ b, RunsIn (program er alloc) (runtimeBound alloc a p D)
      (a.withPC (some (program er alloc).entry)) (b.withPC none) ∧ Result alloc a b p D coeff hc := by
  obtain ⟨n, hn, b, heval, hr⟩ := execution alloc a p D coeff hc hp he hcoeff
  refine ⟨b, ⟨n, hn, ?_⟩, hr⟩
  cases heval with
  | call _ ht => exact ht

theorem primitive_execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p D : ℕ) [Fact p.Prime] (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (he : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hcoeff : a.stacks (persistent es 15) = SubexpPreparedQuarticSetup.flat coeff) :
    ∃ b, Computation.RunsIn (primitive (program er alloc)).step
      (primitiveOverhead (program er alloc) * runtimeBound alloc a p D)
      (primitiveCfg (program er alloc) (a.withPC (some (program er alloc).entry)))
      (primitiveCfg (program er alloc) (b.withPC none)) ∧ Result alloc a b p D coeff hc := by
  obtain ⟨b, hb, hr⟩ := program_runsIn alloc a p D coeff hc hp he hcoeff
  exact ⟨b, BitProgram.primitive_execution _ hb, hr⟩

abbrev SelectedResult {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (p D : ℕ) [Fact p.Prime] : Prop :=
  Result alloc a b p D (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p)

/-- Direct join to the selected-quartic producer's forward byte output. No
separate coefficient representation or prepared-cache premise is required. -/
theorem selected_execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p D : ℕ) [Fact p.Prime]
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (he : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hcoeff : a.stacks (persistent es 15) =
      SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode p)
        (QuarticSearch.coefficients p)) :
    ∃ n ≤ runtimeBound alloc a p D, ∃ b,
      Eval (procedure er alloc).invoke n a b ∧ SelectedResult alloc a b p D :=
  execution alloc a p D (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p) hp he
    (hcoeff.trans (SubexpPreparedQuarticSetup.selectedInputCoefficients_flat p).symm)

end SubexponentialSAT.SubexpMainPreparedRings

end OAI.Algorithms
