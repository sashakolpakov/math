import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScalarAlphabetCore
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixImageServices

namespace OAI.Algorithms

/-!
# Actual Main scalar-alphabet preparation

The persistent prime word is copied and normalized by the fixed core program.
The seven scalar-cache words occupy Main ordinary ports 661 through 667.
Only ordinary ports 0 through 5 are scratch; their old contents and old cache
contents are physically cleared and charged. Other words are preserved.
-/

namespace SubexponentialSAT.SubexpMainScalarAlphabet

open BitProgram StructuredCalls SubexpMainProgram
open Subexp

attribute [local simp] Fin.coe_ofNat_eq_mod

def localTarget (i : Fin 7) : Fin 14 := ⟨1 + i.val, by omega⟩
def localWork (i : Fin 6) : Fin 14 := ⟨8 + i.val, by omega⟩

def targetWord (p : ℕ) [Fact p.Prime] : Fin 7 → List Bool :=
  ![MatrixWordEncoding.word p 0, MatrixWordEncoding.word p 1, MatrixWordEncoding.modulus p,
    ProgramEncoding.encodeRecords (ScalarSetupProgram.tokenAlphabet p),
    ProgramEncoding.encodeRecords (ScalarSetupProgram.rawAlphabet p),
    Encoding.frame (MatrixWordEncoding.word p 0), Encoding.frame (MatrixWordEncoding.word p 1)]

def targetPort {es : ℕ} (a : SubexpLayoutPorts.Allocation es) (i : Fin 7) : Fin (totalStacks es) :=
  SubexpLayoutPorts.master a ⟨21 + i.val, by omega⟩

def workPort {es : ℕ} (a : SubexpLayoutPorts.Allocation es) (i : Fin 6) : Fin (totalStacks es) :=
  SubexpLayoutPorts.ordinary a (i.castLE (by decide))

def stackMap {es : ℕ} (a : SubexpLayoutPorts.Allocation es) : Fin 14 → Fin (totalStacks es) :=
  ![persistent es 6, targetPort a 0, targetPort a 1, targetPort a 2, targetPort a 3,
    targetPort a 4, targetPort a 5, targetPort a 6,
    workPort a 0, workPort a 1, workPort a 2, workPort a 3, workPort a 4, workPort a 5]

theorem stackMap_value {es : ℕ} (a : SubexpLayoutPorts.Allocation es) (i : Fin 14) :
    (stackMap a i).val =
      if i.val = 0 then workStacks es + 6 else if i.val < 8 then 660 + i.val else i.val - 8 := by
  fin_cases i <;> rfl

theorem stackMap_injective {es : ℕ} (a : SubexpLayoutPorts.Allocation es) :
    Function.Injective (stackMap a) := by
  intro i j hij
  have h := congrArg (fun k : Fin (totalStacks es) => k.val) hij
  have hw := a.enough.trans a.within
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  change (stackMap a i).val = (stackMap a j).val at h
  rw [stackMap_value, stackMap_value] at h
  split_ifs at h <;> omega

@[simp] theorem stackMap_source {es : ℕ} (a : SubexpLayoutPorts.Allocation es) :
    stackMap a 0 = persistent es 6 := rfl

@[simp] theorem stackMap_target {es : ℕ} (a : SubexpLayoutPorts.Allocation es) (i : Fin 7) :
    stackMap a (localTarget i) = targetPort a i := by fin_cases i <;> rfl

@[simp] theorem stackMap_work {es : ℕ} (a : SubexpLayoutPorts.Allocation es) (i : Fin 6) :
    stackMap a (localWork i) = workPort a i := by fin_cases i <;> rfl

def procedure (er : ℕ) {es : ℕ} (a : SubexpLayoutPorts.Allocation es) : Procedure er es where
  registers := 16
  stackCount := 14
  labels := size SubexpScalarAlphabetCore.command + 1
  program := SubexpScalarAlphabetCore.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin (workRegs er) => k.val) h)⟩
  stack := ⟨stackMap a, stackMap_injective a⟩

noncomputable def installed {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] : MainState er es :=
  (procedure er alloc).install a (SubexpScalarAlphabetCore.result ((procedure er alloc).project a) p)

theorem local_result_target (a : SubexpScalarAlphabetCore.Data) (p : ℕ) [Fact p.Prime] (i : Fin 7) :
    (SubexpScalarAlphabetCore.result a p).stacks (localTarget i) = targetWord p i := by
  fin_cases i <;> rfl

theorem installed_target {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] (i : Fin 7) :
    (installed alloc a p).stacks (targetPort alloc i) = targetWord p i := by
  have h := (embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack a
    (SubexpScalarAlphabetCore.result ((procedure er alloc).project a) p)
    (procedure er alloc).stack.injective (localTarget i)).trans (local_result_target _ p i)
  change (installed alloc a p).stacks (stackMap alloc (localTarget i)) = targetWord p i at h
  simpa only [stackMap_target] using h

theorem installed_source {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] :
    (installed alloc a p).stacks (persistent es 6) = a.stacks (persistent es 6) :=
  embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack a
    (SubexpScalarAlphabetCore.result ((procedure er alloc).project a) p)
    (procedure er alloc).stack.injective (0 : Fin 14)

theorem installed_work {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] (i : Fin 6) :
    (installed alloc a p).stacks (workPort alloc i) = [] := by
  have h := embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack a
    (SubexpScalarAlphabetCore.result ((procedure er alloc).project a) p)
    (procedure er alloc).stack.injective (localWork i)
  change (installed alloc a p).stacks (stackMap alloc (localWork i)) = _ at h
  rw [stackMap_work] at h
  rw [h]
  fin_cases i <;> rfl

theorem installed_frame {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] (j : Fin (totalStacks es))
    (ht : ∀ i, targetPort alloc i ≠ j) (hw : ∀ i, workPort alloc i ≠ j) :
    (installed alloc a p).stacks j = a.stacks j := by
  by_cases hm : ∃ i, stackMap alloc i = j
  · obtain ⟨i, rfl⟩ := hm
    have hi : i = 0 := by
      by_contra hn
      by_cases hsmall : i.val < 8
      · let k : Fin 7 := ⟨i.val - 1, by have := i.isLt; have := Fin.pos_iff_ne_zero.mpr hn; omega⟩
        have he : localTarget k = i := by apply Fin.ext; dsimp [localTarget, k]; have := Fin.pos_iff_ne_zero.mpr hn; omega
        exact ht k (by rw [← stackMap_target, he])
      · let k : Fin 6 := ⟨i.val - 8, by have := i.isLt; omega⟩
        have he : localWork k = i := by apply Fin.ext; dsimp [localWork, k]; omega
        exact hw k (by rw [← stackMap_work, he])
    subst i
    exact installed_source alloc a p
  · exact embedState_stack_frame _ _ _ _ _ hm

theorem installed_control {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] (i : Fin 3) :
    (installed alloc a p).regs (controlRegister er i) = a.regs (controlRegister er i) :=
  Procedure.install_control _ _ _ _

theorem installed_register {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] (i : Fin 16) :
    (installed alloc a p).regs ((procedure er alloc).registerMap i) = false :=
  embedState_register (procedure er alloc).registerMap (procedure er alloc).stack a
    (SubexpScalarAlphabetCore.result ((procedure er alloc).project a) p)
    (procedure er alloc).registerMap_injective i

theorem tokenAlphabet_eq_tokens (p : ℕ) [Fact p.Prime] :
    ScalarSetupProgram.tokenAlphabet p = MatrixImageEnumeration.tokens p := by
  rw [ScalarSetupProgram.tokenAlphabet_eq]
  rfl

theorem installed_tokens {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] :
    (installed alloc a p).stacks (SubexpLayoutPorts.master alloc 24) =
      ProgramEncoding.encodeRecords (MatrixImageEnumeration.tokens p) := by
  have h := installed_target alloc a p 3
  change (installed alloc a p).stacks (SubexpLayoutPorts.master alloc 24) =
    ProgramEncoding.encodeRecords (ScalarSetupProgram.tokenAlphabet p) at h
  simpa only [tokenAlphabet_eq_tokens] using h

def runtimeBound {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (p : ℕ) : ℕ :=
  500 * (stackBits ((procedure er alloc).project a).stacks + p + 1) * (MatrixWordEncoding.width p + 1)

theorem execution {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime]
    (hp : CounterPrograms.value (a.stacks (persistent es 6)) = p) :
    ∃ ticks ≤ runtimeBound alloc a p,
      Eval (procedure er alloc).invoke ticks a (installed alloc a p) := by
  have h := SubexpScalarAlphabetCore.program_run ((procedure er alloc).project a) p hp
  obtain ⟨ticks, ht, he⟩ := h
  refine ⟨ticks, ht.trans (SubexpScalarAlphabetCore.budget_le _ p), ?_⟩
  exact Procedure.invoke_trace _ _ _ he

end SubexponentialSAT.SubexpMainScalarAlphabet

end OAI.Algorithms
