import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCacheLoad
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCacheInterpretation
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedRingStaging
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-! The fixed local cache phase, including the physical target-table save. -/

namespace SubexponentialSAT.SubexpMainFieldCacheCore

open BitProgram StructuredCalls SubexpScanPrimitives
open BinaryArithmetic SubexpLiftRing SubexpQuarticRing
open SubexpCRTCofactorControl
open SubexpQuarticFlatMul (flat)
open SubexpFieldCacheInterpretation (fieldValue)

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 16 140
abbrev Code := Cmd 16 140

def registers : Fin 8 ↪ Fin 16 := ⟨fun i => i.castAdd 8, by
  intro i j h; exact Fin.ext (congrArg (fun q : Fin 16 => q.val) h)⟩

def ports : Fin 110 ↪ Fin 140 :=
  SubexpFieldCacheLoad.ordinaryPorts.trans ⟨fun i => i.castAdd 2, by
    intro i j h; exact Fin.ext (congrArg (fun q : Fin 140 => q.val) h)⟩

@[simp] theorem ports_apply (i : Fin 110) :
    ports i = (SubexpFieldCacheLoad.ordinaryPort i).castAdd 2 := rfl

def save : Code := .seq (.call (StackRoutines.transferProgram 14 0 0 1))
  (.call (StackRoutines.transferProgram 0 138 0 1))

def saved (a : Data) : Data := ⟨readRegs a.regs 0 1 none,
  Function.update (Function.update a.stacks 14 []) 138 (a.stacks 14)⟩

theorem save_eval (a : Data) (h0 : a.stacks 0 = []) (h138 : a.stacks 138 = []) :
    Eval save (6 * (a.stacks 14).length + 6) a (saved a) := by
  have h1 := transfer_eval a 14 0 0 1 (by decide) (by decide)
  have h2 := transfer_eval (afterTransfer a 14 0 0 1) 0 138 0 1 (by decide) (by decide)
  have he : afterTransfer (afterTransfer a 14 0 0 1) 0 138 0 1 = saved a := by
    apply state_ext
    · simp [afterTransfer, saved, StackRoutines.readRegs_reset]
    · funext j
      by_cases hj : j = 138
      · subst j; simp [afterTransfer, saved, StackRoutines.transferStacks, h0, h138]
      · by_cases hz : j = 0
        · subst j; simp [afterTransfer, saved, StackRoutines.transferStacks, h0]
        · by_cases hs : j = 14
          · subst j; simp [afterTransfer, saved, StackRoutines.transferStacks]
          · simp [afterTransfer, saved, StackRoutines.transferStacks, hj, hz, hs]
  have h := h1.seq h2
  rw [he] at h
  have hl : ((afterTransfer a 14 0 0 1).stacks 0).length = (a.stacks 14).length := by
    simp [afterTransfer, StackRoutines.transferStacks, h0]
  rw [hl] at h
  have htime : 3 * (a.stacks 14).length + 3 +
      (3 * (a.stacks 14).length + 3) = 6 * (a.stacks 14).length + 6 := by omega
  rw [← htime]
  exact h

def command : Code := .seq save (.seq
  (SubexpFieldCacheLoad.command registers ports 139) RegisterResetProgram.all)

abbrev program : Program 16 140 (size command + 1) := compiled command 134 137

def bankPort (i : Fin 6) : Fin 140 := ⟨128 + i.val, by omega⟩

def sourceWords (p : ℕ) [Fact p.Prime] (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)) :
    Words where
  modulus := (SubexpPreparedQuarticSetup.preparedData p 0 coeff hc).modulus.bits
  reduction := flat (SubexpPreparedQuarticSetup.preparedData p 0 coeff hc).reduction
  width := SubexpPreparedQuarticPrelude.widthWord p 1
  exponent := []
  minusOne := (SubexpPreparedQuarticSetup.minusOne p 1).val
  unit := flat (SubexpPreparedQuarticSetup.preparedData p 0 coeff hc).one
  blockWidth := []
  stream := []
  accumulator := []

def sourceFrame (p : ℕ) [Fact p.Prime] : Fin 110 → List Bool :=
  Function.update (fun _ => []) 97
    (ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p))

def emptyInput (i : Fin 140) : Prop :=
  (i.val < 110 ∧ i ≠ 14) ∨ (135 ≤ i.val ∧ i.val ≤ 138)

structure Ready (a : Data) (p : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)) : Prop where
  bank : ∀ i, a.stacks (bankPort i) = SubexpPreparedRingStaging.bankWords p 0 coeff hc i
  source : a.stacks 134 = ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p)
  empty : ∀ i, emptyInput i → a.stacks i = []

private theorem flat_eq {B : ℕ} (x : Quad (Word B)) :
    SubexpPreparedQuarticSetup.flat x = flat x := rfl

theorem ready_store (a : Data) (p : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (h : Ready a p coeff hc) :
    ∀ i, (saved a).stacks (ports i) =
      store (sourceFrame p) (SubexpFieldCacheNodeLoop.ready (sourceWords p coeff hc) [] []) i := by
  have hb := h.bank
  have hz : ∀ j : Fin 140, j.val < 110 → (saved a).stacks j = [] := by
    intro j hj
    by_cases he : j = 14
    · subst j; simp [saved]
    · have h138 : j ≠ 138 := by intro h; subst j; norm_num at hj
      simp only [saved, Function.update_of_ne h138, Function.update_of_ne he]
      exact h.empty j (Or.inl ⟨hj, he⟩)
  intro i
  by_cases h66 : i = 66
  · subst i; simpa [ports_apply,
      SubexpFieldCacheLoad.ordinaryPort, saved, sourceWords, SubexpFieldCacheNodeLoop.ready,
      bankPort, SubexpPreparedRingStaging.bankWords] using hb 0
  by_cases h73 : i = 73
  · subst i; simpa [ports_apply,
      SubexpFieldCacheLoad.ordinaryPort, saved, sourceWords, SubexpFieldCacheNodeLoop.ready,
      bankPort, SubexpPreparedRingStaging.bankWords, flat_eq] using hb 2
  by_cases h74 : i = 74
  · subst i; simpa [ports_apply,
      SubexpFieldCacheLoad.ordinaryPort, saved, sourceWords, SubexpFieldCacheNodeLoop.ready,
      bankPort, SubexpPreparedRingStaging.bankWords] using hb 1
  by_cases h92 : i = 92
  · subst i; simpa [ports_apply,
      SubexpFieldCacheLoad.ordinaryPort, saved, sourceWords, SubexpFieldCacheNodeLoop.ready,
      bankPort, SubexpPreparedRingStaging.bankWords] using hb 5
  by_cases h93 : i = 93
  · subst i; simpa [ports_apply,
      SubexpFieldCacheLoad.ordinaryPort, saved, sourceWords, SubexpFieldCacheNodeLoop.ready,
      bankPort, SubexpPreparedRingStaging.bankWords, flat_eq] using hb 4
  by_cases h97 : i = 97
  · subst i; simpa [ports_apply,
      SubexpFieldCacheLoad.ordinaryPort, saved, store, sourceFrame] using h.source
  by_cases h98 : i = 98
  · subst i; simpa [ports_apply,
      SubexpFieldCacheLoad.ordinaryPort, saved, sourceWords, SubexpFieldCacheNodeLoop.ready]
      using h.empty 135 (by right; decide)
  by_cases h100 : i = 100
  · subst i; simpa [ports_apply,
      SubexpFieldCacheLoad.ordinaryPort, saved, sourceWords, store, sourceFrame]
      using h.empty 136 (by right; decide)
  by_cases h103 : i = 103
  · subst i; simpa [ports_apply,
      SubexpFieldCacheLoad.ordinaryPort, saved, sourceWords, store, sourceFrame]
      using h.empty 137 (by right; decide)
  have hp : ports i = (⟨i.val, by omega⟩ : Fin 140) := by
    simp [ports_apply, SubexpFieldCacheLoad.ordinaryPort,
      h66, h73, h74, h92, h93, h97, h98, h100, h103]
  rw [hp, hz _ i.isLt]
  by_cases h77 : i.val < 77
  · have hn66 : (⟨i.val, h77⟩ : Fin 77) ≠ 66 := by
      intro he; apply h66; exact Fin.ext (congrArg (fun q : Fin 77 => q.val) he)
    have hn73 : (⟨i.val, h77⟩ : Fin 77) ≠ 73 := by
      intro he; apply h73; exact Fin.ext (congrArg (fun q : Fin 77 => q.val) he)
    have hn74 : (⟨i.val, h77⟩ : Fin 77) ≠ 74 := by
      intro he; apply h74; exact Fin.ext (congrArg (fun q : Fin 77 => q.val) he)
    simp [store, h77, nativeStore, SubexpQuarticFlatMul.bankStore,
      SubexpFieldCacheNodeLoop.ready, hn66, hn73, hn74, Function.update_apply]
  · simp [store, h77, SubexpFieldCacheNodeLoop.ready, sourceWords,
      sourceFrame, h92, h93, h97]

def output (a : Data) (p : ℕ) [Fact p.Prime]
    (ys : List (Quad (Word (baseWidth p 1))))
    (rows : List (List (Quad (Word (baseWidth p 1))))) : Data :=
  ⟨fun _ => false, SubexpFieldCacheCall.resultStacks ports
    (SubexpMachineNodeOrder.nodeWords p).flatten (ys.flatMap flat)
    (SubexpFieldCacheNodeLoop.negativeBytes p 1 (SubexpPreparedQuarticSetup.modulus p 1)
      (SubexpPreparedQuarticSetup.minusOne p 1) (SubexpNodeLiftData.nodeQuads p))
    (rows.flatten.flatMap flat) (saved a).stacks⟩

def runtimeBound (a : Data) (p : ℕ) : ℕ :=
  6 * (a.stacks 14).length + SubexpFieldCacheProgram.budget (baseWidth p 1)
    (a.stacks 139) (p^4 - 1) + 9 * (a.stacks 139).length + 32

end SubexponentialSAT.SubexpMainFieldCacheCore

end OAI.Algorithms
