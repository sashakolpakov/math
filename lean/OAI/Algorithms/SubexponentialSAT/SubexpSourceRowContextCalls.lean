import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSourceRowContext
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedSetupBounds

namespace OAI.Algorithms

/-! Physical embeddings of the source-row constructor.  In Main, its two
read-only inputs refer directly to the existing persistent radius and target
width.  No assertion equates an ordinary work port with a persistent port. -/

namespace SubexponentialSAT.SubexpSourceRowContext

open BitProgram StructuredCalls SubexpSetupStorage

theorem prepared_bounded (a : Data) (W : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ W) :
    ∀ i, ((prepared a).stacks i).length ≤ W := by
  apply SubexpPreparedSetupCalls.copyMany_bound copies
    (beforeCopies copyTemporary clearPorts a)
    (SubexpPreparedSetupCalls.beforeCopies_bound copyTemporary clearPorts a ha)
    copies_nodup
  · intro q hq
    simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
      ite_eq_left ((mem_clearPorts _).mpr (copies_cleared q hq))]
  · exact copies_separated

theorem prepareCost_bound (a : Data) (W : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ W) :
    SubexpSetupStorage.prepareCost copyTemporary clearPorts copies a ≤
      257 * (2 * W + 3) + 9 + 7 * (7 * W + 5) := by
  have h₁ := SubexpPreparedSetupCalls.clearManyCost_le [copyTemporary] a ha
  have h₂ := SubexpPreparedSetupCalls.clearManyCost_le clearPorts
    (clearManyState [copyTemporary] a)
    (SubexpPreparedSetupCalls.clearMany_bound [copyTemporary] a ha)
  have hlen : clearPorts.length ≤ 256 := by
    simpa only [clearPorts, List.length_finRange] using
      List.length_filter_le (fun i : Fin 256 => decide (NeedsClear i)) (List.finRange 256)
  have h₂' : clearManyCost clearPorts (clearManyState [copyTemporary] a) ≤
      256 * (2 * W + 3) := h₂.trans (Nat.mul_le_mul_right _ hlen)
  have hsource : ∀ q ∈ copies,
      ((beforeCopies copyTemporary clearPorts a).stacks q.1).length ≤ W := by
    intro q hq
    exact SubexpPreparedSetupCalls.beforeCopies_bound copyTemporary clearPorts a ha q.1
  have h₃ := SubexpPreparedSetupCalls.copyManyCost_le copies
    (beforeCopies copyTemporary clearPorts a) hsource copies_separated
  have hcopies : copies.length = 7 := rfl
  simp only [List.length_singleton, one_mul] at h₁
  rw [hcopies] at h₃
  unfold prepareCost
  omega

/-- The complete instruction count is quadratic in a common bound for all
input word lengths and the numerical radius. No whole-word arithmetic is a
machine instruction in this bound. -/
theorem runtimeBound_le (a : Data) (W : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ W)
    (hR : BinaryArithmetic.toNat (a.stacks radiusInput) ≤ W) :
    runtimeBound a ≤ 2000 * (W + 1)^2 := by
  have hp := prepareCost_bound a W ha
  have hwidth : sourceWidth a ≤ W := ha 129
  have hdim : dimension a ≤ W + 1 := by
    simpa only [dimension, CounterPrograms.value_eq_toNat] using Nat.add_le_add_right hR 1
  have hu : CounterConversions.runtimeBound (a.stacks radiusInput) ≤ 32 * (W + 1)^2 := by
    unfold CounterConversions.runtimeBound
    rw [CounterPrograms.value_eq_toNat, pow_two]
    have he := ha radiusInput
    nlinarith [Nat.mul_le_mul (Nat.add_le_add_right hR 1) (Nat.add_le_add_right he 1)]
  have hj : dimension a * (28 * sourceWidth a + 14) ≤ (W + 1) * (28 * W + 14) :=
    Nat.mul_le_mul hdim (by omega)
  unfold runtimeBound
  nlinarith [Nat.zero_le (W^2)]

theorem result_bounded (a : Data) (W : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ W)
    (hR : BinaryArithmetic.toNat (a.stacks radiusInput) ≤ W) :
    ∀ i, ((result a).stacks i).length ≤ 4 * (W + 1)^2 := by
  have hp := prepared_bounded a W ha
  have hwidth : sourceWidth a ≤ W := ha 129
  have hdim : dimension a ≤ W + 1 := by
    simpa only [dimension, CounterPrograms.value_eq_toNat] using Nat.add_le_add_right hR 1
  have hbig : W + 1 ≤ 4 * (W + 1)^2 := by nlinarith [Nat.zero_le (W^2)]
  intro i
  by_cases h104 : i = 104
  · subst i
    rw [result_shape, List.length_replicate]
    nlinarith [Nat.zero_le (W^2)]
  by_cases h242 : i = 242
  · subst i
    rw [result_zeroArray, List.length_replicate]
    have h := Nat.mul_le_mul hdim (Nat.mul_le_mul_left 4 hwidth)
    nlinarith [Nat.zero_le (W^2)]
  by_cases h243 : i = 243
  · subst i
    rw [result_dimension, List.length_replicate]
    exact hdim.trans hbig
  by_cases h248 : i = binaryCopy
  · subst i
    rw [result_scratch_empty a binaryCopy (by decide) (by decide)]
    exact Nat.zero_le _
  by_cases h249 : i = unaryScratch
  · subst i
    rw [result_scratch_empty a unaryScratch (by decide) (by decide)]
    exact Nat.zero_le _
  rw [result_prepared_frame a i h104 h242 h243 h248 h249]
  exact (hp i).trans ((Nat.le_succ W).trans hbig)

abbrev PrimitiveRunsIn {r s l : ℕ} (P : Program r s l) (budget : ℕ)
    (a b : Cfg r s l) : Prop :=
  Computation.RunsIn (primitive P).step budget (primitiveCfg P a) (primitiveCfg P b)

theorem primitive_run (a : Data) :
    PrimitiveRunsIn program (primitiveOverhead program * runtimeBound a)
      (a.withPC (some program.entry)) ((result a).withPC none) :=
  primitive_execution program (program_runs a)

def projectAt {R S : ℕ} (reg : Fin 16 ↪ Fin R) (port : Fin 256 ↪ Fin S)
    (a : StructuredProgram.State R S) : Data :=
  ⟨a.regs ∘ reg, a.stacks ∘ port⟩

noncomputable def resultAt {R S : ℕ} (reg : Fin 16 ↪ Fin R) (port : Fin 256 ↪ Fin S)
    (a : StructuredProgram.State R S) : StructuredProgram.State R S :=
  embedState reg port a (result (projectAt reg port a))

abbrev callAt {R S : ℕ} (reg : Fin 16 ↪ Fin R) (port : Fin 256 ↪ Fin S) : Cmd R S :=
  .call (ProgramLinking.liftProgram program reg port)

theorem callAt_eval {R S : ℕ} (reg : Fin 16 ↪ Fin R) (port : Fin 256 ↪ Fin S)
    (a : StructuredProgram.State R S) :
    ∃ n, Eval (callAt reg port) n a (resultAt reg port a) ∧
      n ≤ runtimeBound (projectAt reg port a) := by
  obtain ⟨n, hn, ht⟩ := program_runs (projectAt reg port a)
  have heq : embedState reg port a (projectAt reg port a) = a := by
    apply embedState_eq_of_ports reg port a a _ reg.injective port.injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; rfl
    · intro i hi; rfl
  have h := eval_call_lifted program reg port a reg.injective port.injective
    (a := projectAt reg port a) (b := result (projectAt reg port a)) ht
  exact ⟨n, by simpa only [callAt, resultAt, heq] using h, hn⟩

theorem resultAt_stack {R S : ℕ} (reg : Fin 16 ↪ Fin R) (port : Fin 256 ↪ Fin S)
    (a : StructuredProgram.State R S) (i : Fin 256) :
    (resultAt reg port a).stacks (port i) = (result (projectAt reg port a)).stacks i :=
  embedState_stack reg port a _ port.injective i

/-- A single frame rule covers protected inputs inside the local ABI and
all caller storage outside that ABI. -/
theorem resultAt_frame {R S : ℕ} (reg : Fin 16 ↪ Fin R) (port : Fin 256 ↪ Fin S)
    (a : StructuredProgram.State R S) (i : Fin S)
    (h : ∀ j, port j = i → ¬ NeedsClear j) :
    (resultAt reg port a).stacks i = a.stacks i := by
  classical
  by_cases hi : ∃ j, port j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [resultAt_stack, result_frame _ _ (h j rfl)]
    rfl
  · exact embedState_stack_frame reg port a _ i hi

def outerRegister : Fin 16 ↪ Fin 25 := ⟨Fin.castAdd 9, Fin.castAdd_injective _ _⟩
def outerStack : Fin 256 ↪ Fin 288 := ⟨Fin.castAdd 32, Fin.castAdd_injective _ _⟩
abbrev outerCommand : Cmd 25 288 := callAt outerRegister outerStack
def outerProgram := compiled outerCommand (250 : Fin 288) 242

theorem outer_runs (a : StructuredProgram.State 25 288) :
    RunsIn outerProgram (runtimeBound (projectAt outerRegister outerStack a) + 1)
      (a.withPC (some outerProgram.entry))
      ((resultAt outerRegister outerStack a).withPC none) := by
  obtain ⟨n, he, hn⟩ := callAt_eval outerRegister outerStack a
  exact ⟨n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 250 242⟩

theorem outer_high_frame (a : StructuredProgram.State 25 288) (i : Fin 288)
    (hi : 256 ≤ i.val) : (resultAt outerRegister outerStack a).stacks i = a.stacks i := by
  apply resultAt_frame
  intro j hj
  have hv := congrArg (fun k : Fin 288 => k.val) hj
  change j.val = i.val at hv
  have := j.isLt
  omega

namespace Main

open SubexpMainProgram

structure Allocation (es : ℕ) where
  ordinaryCount : ℕ
  enough : 256 ≤ ordinaryCount
  within : ordinaryCount ≤ workStacks es

def register (er : ℕ) : Fin 16 ↪ Fin (totalRegs er) :=
  ⟨fun i => ⟨i.val, by have := i.isLt; dsimp [totalRegs, workRegs]; omega⟩,
    fun i j h => Fin.ext (congrArg (fun k : Fin (totalRegs er) => k.val) h)⟩

def stackMap {es : ℕ} (alloc : Allocation es) (i : Fin 256) : Fin (totalStacks es) :=
  if i = radiusInput then persistent es 25
  else if i = targetWidthInput then persistent es 13
  else ⟨i.val, by
    have := i.isLt
    have := alloc.enough
    have := alloc.within
    dsimp [totalStacks]
    omega⟩

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (stackMap alloc) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun k : Fin (totalStacks es) => k.val) h
  have hi := i.isLt
  have hj := j.isLt
  have ha := alloc.enough.trans alloc.within
  simp only [stackMap] at hv
  split_ifs at hv <;> simp_all only [persistent, Fin.val_natAdd, Fin.coe_ofNat_eq_mod]
  all_goals omega

def port {es : ℕ} (alloc : Allocation es) : Fin 256 ↪ Fin (totalStacks es) :=
  ⟨stackMap alloc, stackMap_injective alloc⟩

def command (er : ℕ) {es : ℕ} (alloc : Allocation es) : MainCmd er es :=
  callAt (register er) (port alloc)

noncomputable def result (er : ℕ) {es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    MainState er es := resultAt (register er) (port alloc) a

theorem command_eval (er : ℕ) {es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    ∃ n, Eval (command er alloc) n a (result er alloc a) ∧
      n ≤ runtimeBound (projectAt (register er) (port alloc) a) :=
  callAt_eval (register er) (port alloc) a

theorem radius_word (er : ℕ) {es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (projectAt (register er) (port alloc) a).stacks radiusInput =
      a.stacks (persistent es 25) := by rfl

theorem target_width_word (er : ℕ) {es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (projectAt (register er) (port alloc) a).stacks targetWidthInput =
      a.stacks (persistent es 13) := by rfl

/-- Every persistent input is preserved, including the radius and target
width actually used by the constructor. -/
theorem persistent_frame (er : ℕ) {es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (i : Fin 32) :
    (result er alloc a).stacks (persistent es i) = a.stacks (persistent es i) := by
  apply resultAt_frame
  intro j hj
  by_cases hr : j = radiusInput
  · subst j; decide
  by_cases ht : j = targetWidthInput
  · subst j; decide
  have hv := congrArg (fun k : Fin (totalStacks es) => k.val) hj
  change (stackMap alloc j).val = (persistent es i).val at hv
  rw [stackMap, ite_eq_right hr, ite_eq_right ht] at hv
  change j.val = workStacks es + i.val at hv
  have hjlt := j.isLt
  have hwork : 256 ≤ workStacks es := alloc.enough.trans alloc.within
  omega

/-- Storage above the constructor's ordinary work interval is framed,
including the row traversal's scope, dimension, and lookup ports. -/
theorem ordinary_high_frame (er : ℕ) {es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (i : Fin (totalStacks es))
    (hi : 256 ≤ i.val) (hwork : i.val < workStacks es) :
    (result er alloc a).stacks i = a.stacks i := by
  apply resultAt_frame
  intro j hj
  have hv := congrArg (fun k : Fin (totalStacks es) => k.val) hj
  change (stackMap alloc j).val = i.val at hv
  simp only [stackMap] at hv
  split_ifs at hv <;> simp only [persistent, Fin.val_natAdd, Fin.coe_ofNat_eq_mod] at hv
  all_goals have := j.isLt; omega

end Main
end SubexponentialSAT.SubexpSourceRowContext

end OAI.Algorithms
