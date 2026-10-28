import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldNodeStaging
import OAI.Algorithms.SubexponentialSAT.SubexpMainPreparedRings
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

namespace OAI.Algorithms

/-!
# The field-node producer in the Main ABI

This phase copies the retained prime into the actual normalized field-node
generator. It preserves the generated framed source table at ordinary 134,
then physically supplies the source modulus and both width shapes to the
node mapper. The lifted table remains at ordinary 14 for the node-master
save step. No input premise supplies a precomputed node table.
-/

namespace SubexponentialSAT.SubexpMainFieldNodes

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupStorage
open BinaryArithmetic SubexpLiftRing SubexpQuarticRing
open scoped BigOperators

attribute [local simp] Fin.coe_ofNat_eq_mod

structure Allocation (es : ℕ) where
  ordinaryCount : ℕ
  enough : 135 ≤ ordinaryCount
  within : ordinaryCount ≤ workStacks es

def setupAllocation (c : SubexpSetupProgram.Config) :
    Allocation (SubexpSetupProgram.mainExtraStacks c) where
  ordinaryCount := SubexpSetupProgram.helperSize c
  enough := by have := SubexpSetupProgram.helperSize_ge c; omega
  within := by
    unfold SubexpSetupProgram.helperSize SubexpSetupProgram.mainExtraStacks workStacks
    omega

def ringAllocation {es : ℕ} (alloc : Allocation es) : SubexpMainPreparedRings.Allocation es where
  ordinaryCount := alloc.ordinaryCount
  enough := by have := alloc.enough; omega
  within := alloc.within

def ordinary {es : ℕ} (alloc : Allocation es) (i : Fin 135) : Fin (totalStacks es) :=
  ⟨i.val, by have := alloc.enough; have := alloc.within; dsimp [totalStacks]; omega⟩

def highPort {es : ℕ} (alloc : Allocation es) : Fin 5 → Fin (totalStacks es) :=
  ![persistent es 6, ordinary alloc 128, ordinary alloc 129,
    persistent es 13, ordinary alloc 134]

def stackMap {es : ℕ} (alloc : Allocation es) (i : Fin 25) : Fin (totalStacks es) :=
  if hi : i.val < 20 then ordinary alloc ⟨i.val, by omega⟩
  else highPort alloc ⟨i.val - 20, by omega⟩

theorem highPort_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (highPort alloc) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hw := alloc.enough.trans alloc.within
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [highPort, ordinary, persistent] at hv <;> omega

theorem highPort_lower {es : ℕ} (alloc : Allocation es) (i : Fin 5) :
    20 ≤ (highPort alloc i).val := by
  have hw := alloc.enough.trans alloc.within
  fin_cases i <;> simp [highPort, ordinary, persistent] <;> omega

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (stackMap alloc) := by
  intro i j h
  have hv := congrArg Fin.val h
  by_cases hi : i.val < 20 <;> by_cases hj : j.val < 20
  · apply Fin.ext
    simpa only [stackMap, dite_eq_left hi, dite_eq_left hj, ordinary] using hv
  · have hl := highPort_lower alloc ⟨j.val - 20, by omega⟩
    simp only [stackMap, dite_eq_left hi, dite_eq_right hj, ordinary] at hv
    omega
  · have hl := highPort_lower alloc ⟨i.val - 20, by omega⟩
    simp only [stackMap, dite_eq_right hi, dite_eq_left hj, ordinary] at hv
    omega
  · have hh := highPort_injective alloc (by
      simpa only [stackMap, dite_eq_right hi, dite_eq_right hj] using h)
    have hv' := congrArg Fin.val hh
    apply Fin.ext
    dsimp only at hv'
    omega

@[simp] theorem stackMap_low {es : ℕ} (alloc : Allocation es) (i : Fin 20) :
    stackMap alloc (i.castAdd 5) = ordinary alloc ⟨i.val, by omega⟩ := by
  simp only [stackMap, Fin.val_castAdd, dite_eq_left i.isLt]

@[simp] theorem stackMap_prime {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 20 = persistent es 6 := rfl
@[simp] theorem stackMap_modulus {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 21 = ordinary alloc 128 := rfl
@[simp] theorem stackMap_sourceWidth {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 22 = ordinary alloc 129 := rfl
@[simp] theorem stackMap_targetWidth {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 23 = persistent es 13 := rfl
@[simp] theorem stackMap_source {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 24 = ordinary alloc 134 := rfl
@[simp] theorem stackMap_lifted {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 14 = ordinary alloc 14 := rfl

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 25
  labels := size SubexpFieldNodeStaging.command + 1
  program := SubexpFieldNodeStaging.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin (workRegs er) => k.val) h)⟩
  stack := ⟨stackMap alloc, stackMap_injective alloc⟩

def program (er : ℕ) {es : ℕ} (alloc : Allocation es) :=
  ProgramLinking.liftProgram (procedure er alloc).program
    (procedure er alloc).registerMap (procedure er alloc).stack

def wordBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  stackBits ((procedure er alloc).project a).stacks

theorem project_wordBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    WordBound (wordBound alloc a) ((procedure er alloc).project a) := by
  intro i
  exact Finset.single_le_sum
    (f := fun j : Fin 25 => (((procedure er alloc).project a).stacks j).length)
    (s := Finset.univ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (p μ : ℕ) : ℕ :=
  SubexpFieldNodeStaging.runtimeBound p μ (wordBound alloc a)

structure Result {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1) : Prop where
  lifted : b.stacks (ordinary alloc 14) =
    ProgramEncoding.encodeRecords (SubexpNodeLiftData.liftedNodeWords p μ M)
  source : b.stacks (ordinary alloc 134) =
    ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p)
  frame : ∀ i : Fin (totalStacks es), 20 ≤ i.val → i.val ≠ 134 → b.stacks i = a.stacks i
  scratch : ∀ i : Fin 20, i ≠ 14 → b.stacks (ordinary alloc ⟨i.val, by omega⟩) = []
  registers : ∀ i : Fin 16, b.regs ((procedure er alloc).registerMap i) = false
  registerFrame : ∀ i, (¬ ∃ j, (procedure er alloc).registerMap j = i) → b.regs i = a.regs i
  control : ∀ i, b.regs (controlRegister er i) = a.regs (controlRegister er i)

theorem Result.persistent_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {p μ : ℕ} [Fact p.Prime] {M : SubexpPreparedQuartic.Modulus p 1}
    (h : Result alloc a b p μ M) (i : Fin 32) :
    b.stacks (persistent es i) = a.stacks (persistent es i) := by
  have hw := alloc.enough.trans alloc.within
  apply h.frame <;> simp only [persistent, Fin.val_natAdd] <;> omega

theorem Result.sourceCache_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {p μ : ℕ} [Fact p.Prime] {M : SubexpPreparedQuartic.Modulus p 1}
    (h : Result alloc a b p μ M) (i : Fin 6) :
    b.stacks (SubexpMainPreparedRings.sourcePort (ringAllocation alloc) i) =
      a.stacks (SubexpMainPreparedRings.sourcePort (ringAllocation alloc) i) := by
  apply h.frame <;> simp only [SubexpMainPreparedRings.sourcePort] <;> omega

theorem install_result {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpFieldNodeStaging.Data) (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1)
    (h : SubexpFieldNodeStaging.Result ((procedure er alloc).project a) out p μ M) :
    Result alloc a ((procedure er alloc).install a out) p μ M := by
  have hs (i : Fin 25) := embedState_stack (procedure er alloc).registerMap
    (procedure er alloc).stack a out (procedure er alloc).stack.injective i
  constructor
  · exact (hs 14).trans h.lifted
  · exact (hs 24).trans h.source
  · intro i hi hne
    by_cases hm : ∃ j, stackMap alloc j = i
    · obtain ⟨j, rfl⟩ := hm
      have hj : 20 ≤ j.val := by
        by_contra hj
        have hlt : j.val < 20 := by omega
        simp only [stackMap, dite_eq_left hlt, ordinary] at hi
        omega
      have hj' : j.val < 24 := by
        by_contra hn
        have he : j = 24 := Fin.ext (by omega)
        subst j
        change (134 : ℕ) ≠ 134 at hne
        exact hne rfl
      exact (hs j).trans (h.inputs j hj hj')
    · exact embedState_stack_frame _ _ _ _ _ hm
  · intro i hi
    have hh := hs (i.castAdd 5)
    change ((procedure er alloc).install a out).stacks (stackMap alloc _) = _ at hh
    rw [stackMap_low] at hh
    exact hh.trans (h.scratch _ i.isLt (by
      intro he
      apply hi
      exact Fin.ext (congrArg (fun q : Fin 25 => q.val) he)))
  · intro i
    exact (embedState_register _ _ _ _ (procedure er alloc).registerMap_injective i).trans
      (h.registers i)
  · intro i hi
    exact embedState_register_frame _ _ _ _ _ hi
  · exact Procedure.install_control _ _ _

theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1) (hμ : 0 < μ)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hmod : a.stacks (ordinary alloc 128) = M.bits)
    (hsw : (a.stacks (ordinary alloc 129)).length = baseWidth p 1)
    (htw : (a.stacks (persistent es 13)).length = baseWidth p μ) :
    ∃ n ≤ runtimeBound alloc a p μ, ∃ b,
      Eval (procedure er alloc).invoke n a b ∧ Result alloc a b p μ M := by
  have h20 : ((procedure er alloc).project a).stacks (20 : Fin 25) = a.stacks (persistent es 6) := rfl
  have h21 : ((procedure er alloc).project a).stacks (21 : Fin 25) = a.stacks (ordinary alloc 128) := rfl
  have h22 : ((procedure er alloc).project a).stacks (22 : Fin 25) = a.stacks (ordinary alloc 129) := rfl
  have h23 : ((procedure er alloc).project a).stacks (23 : Fin 25) = a.stacks (persistent es 13) := rfl
  obtain ⟨out, hrun, _, hr⟩ := SubexpFieldNodeStaging.program_runsIn p μ
    (wordBound alloc a) M ((procedure er alloc).project a) (project_wordBound alloc a) hμ
    (by rw [h20, CounterPrograms.value_eq_toNat]; exact hp)
    (h21.trans hmod) (by rw [h22]; exact hsw) (by rw [h23]; exact htw)
  obtain ⟨n, hn, ht⟩ := hrun
  exact ⟨n, hn, (procedure er alloc).install a out, Procedure.invoke_trace _ _ _ ht,
    install_result alloc a out p μ M hr⟩

theorem program_runsIn {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1) (hμ : 0 < μ)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hmod : a.stacks (ordinary alloc 128) = M.bits)
    (hsw : (a.stacks (ordinary alloc 129)).length = baseWidth p 1)
    (htw : (a.stacks (persistent es 13)).length = baseWidth p μ) :
    ∃ b, RunsIn (program er alloc) (runtimeBound alloc a p μ)
      (a.withPC (some (program er alloc).entry)) (b.withPC none) ∧ Result alloc a b p μ M := by
  obtain ⟨n, hn, b, he, hr⟩ := execution alloc a p μ M hμ hp hmod hsw htw
  refine ⟨b, ⟨n, hn, ?_⟩, hr⟩
  cases he with
  | call _ ht => exact ht

theorem primitive_execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1) (hμ : 0 < μ)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hmod : a.stacks (ordinary alloc 128) = M.bits)
    (hsw : (a.stacks (ordinary alloc 129)).length = baseWidth p 1)
    (htw : (a.stacks (persistent es 13)).length = baseWidth p μ) :
    ∃ b, Computation.RunsIn (primitive (program er alloc)).step
      (primitiveOverhead (program er alloc) * runtimeBound alloc a p μ)
      (primitiveCfg (program er alloc) (a.withPC (some (program er alloc).entry)))
      (primitiveCfg (program er alloc) (b.withPC none)) ∧ Result alloc a b p μ M := by
  obtain ⟨b, hb, hr⟩ := program_runsIn alloc a p μ M hμ hp hmod hsw htw
  exact ⟨b, BitProgram.primitive_execution _ hb, hr⟩

/-- Direct composition after the proved prepared-ring stage. Only the prime
value is supplied; modulus and width inputs come from its actual result. -/
theorem after_prepared {er es : ℕ} (alloc : Allocation es) (before a : MainState er es)
    (p D : ℕ) [Fact p.Prime] (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (h : SubexpMainPreparedRings.Result (ringAllocation alloc) before a p D coeff hc)
    (hp : BinaryArithmetic.toNat (before.stacks (persistent es 6)) = p) :
    ∃ n ≤ runtimeBound alloc a p (D + 1), ∃ b,
      Eval (procedure er alloc).invoke n a b ∧
      Result alloc a b p (D + 1) (SubexpPreparedQuarticSetup.preparedData p 0 coeff hc).modulus := by
  apply execution alloc a p (D + 1) _ (by omega)
  · have hv := h.inputs 0
    change a.stacks (persistent es 6) = before.stacks (persistent es 6) at hv
    rw [hv]
    exact hp
  · exact h.source 0
  · exact h.source_width
  · exact h.target_width

end SubexponentialSAT.SubexpMainFieldNodes

end OAI.Algorithms
