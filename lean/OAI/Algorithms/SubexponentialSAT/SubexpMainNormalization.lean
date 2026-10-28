import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFrontendNormalizationProgram

namespace OAI.Algorithms

/-! The retained-body normalizer as a framed MainProgram procedure. -/

namespace SubexponentialSAT.SubexpMainNormalization

open BitProgram StructuredCalls
open SubexpMainProgram

def workPort (es : ℕ) (i : Fin 17) : Fin (totalStacks es) :=
  ⟨i.val, by dsimp [totalStacks, workStacks]; omega⟩

def stackMap (es : ℕ) (i : Fin 18) : Fin (totalStacks es) :=
  if i = 16 then persistent es 0
  else if i = 17 then workPort es 16
  else ⟨i.val, by dsimp [totalStacks, workStacks]; omega⟩

theorem stackMap_injective (es : ℕ) : Function.Injective (stackMap es) := by
  intro i j h
  have hv := congrArg (fun i : Fin (totalStacks es) => i.val) h
  apply Fin.ext
  by_cases hi16 : i = 16 <;> by_cases hi17 : i = 17 <;>
    by_cases hj16 : j = 16 <;> by_cases hj17 : j = 17 <;>
    simp [stackMap, hi16, hi17, hj16, hj17, workPort, persistent, workStacks] at hv <;>
    norm_num [Fin.ext_iff] at hi16 hi17 hj16 hj17 <;> omega

theorem stackMap_avoids_persistent (es : ℕ) (j : Fin 32) (hj : j ≠ 0) :
    ¬ ∃ i, stackMap es i = persistent es j := by
  rintro ⟨i, h⟩
  by_cases hi16 : i = 16
  · subst i
    have hp : (0 : Fin 32) = j := (persistent_injective es) h
    exact hj hp.symm
  · have hv := congrArg (fun i : Fin (totalStacks es) => i.val) h
    by_cases hi17 : i = 17 <;>
      simp [stackMap, hi16, hi17, workPort, persistent, workStacks] at hv <;> omega

def procedure (er es : ℕ) : Procedure er es where
  registers := 16
  stackCount := 18
  labels := StructuredCalls.size SubexpFrontendNormalizationProgram.command + 1
  program := SubexpFrontendNormalizationProgram.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun i : Fin (workRegs er) => i.val) h)⟩
  stack := ⟨stackMap es, stackMap_injective es⟩

def WorkspaceClean {er es : ℕ} (a : MainState er es) : Prop :=
  ∀ i : Fin 17, a.stacks (workPort es i) = []

theorem project_ready {er es : ℕ} (a : MainState er es) (ha : WorkspaceClean a) :
    SubexpFrontendNormalizationProgram.Ready ((procedure er es).project a) := by
  intro i hi16
  change a.stacks (stackMap es i) = []
  by_cases hi17 : i = 17
  · subst i
    exact ha 16
  · have hi : i.val < 17 := by
      have hn17 : i.val ≠ 17 := fun h => hi17 (Fin.ext h)
      omega
    let j : Fin 17 := ⟨i.val, hi⟩
    simpa only [stackMap, ite_eq_right hi16, ite_eq_right hi17, workPort] using ha j

theorem install_workspace_clean {er es : ℕ} (a : MainState er es)
    (b : SubexpFrontendNormalizationProgram.Data)
    (hb : SubexpFrontendNormalizationProgram.Ready b) :
    WorkspaceClean ((procedure er es).install a b) := by
  intro i
  by_cases hi : i = 16
  · subst i
    exact (embedState_stack (procedure er es).registerMap (procedure er es).stack a b
      (procedure er es).stack.injective (17 : Fin 18)).trans (hb 17 (by decide))
  · let j : Fin 18 := i.castAdd 1
    have hj16 : j ≠ 16 := by
      intro h
      exact hi (Fin.ext (congrArg (fun j : Fin 18 => j.val) h))
    have hj17 : j ≠ 17 := by
      intro h
      have hv := congrArg (fun j : Fin 18 => j.val) h
      have := i.isLt
      change i.val = 17 at hv
      omega
    have hm : (procedure er es).stack j = workPort es i := by
      change stackMap es j = workPort es i
      simp only [stackMap, ite_eq_right hj16, ite_eq_right hj17, workPort]
      rfl
    have hs := embedState_stack (procedure er es).registerMap (procedure er es).stack a b
      (procedure er es).stack.injective j
    rw [hm] at hs
    exact hs.trans (hb j hj16)

/-- Actual normalization changes only persistent body slot 0. In particular
the exact n/s/u words and every other persistent list remain unchanged. -/
theorem invoke_eval {er es : ℕ} (F : List (List ℕ)) (a : MainState er es)
    (hbody : a.stacks (persistent es 0) = SubexpNormalizationProgram.formulaCode F)
    (hwork : WorkspaceClean a) :
    ∃ t ≤ 3500 * ((SubexpNormalizationProgram.formulaCode F).length + 1) ^ 2,
      ∃ b : MainState er es, Eval (procedure er es).invoke t a b ∧
      WorkspaceClean b ∧
      b.stacks (persistent es 0) = SubexpNormalizationProgram.formulaCode
        (ExecCNF.normalize SubexpFrontend.negateCode F) ∧
      (∀ i : Fin 32, i ≠ 0 → b.stacks (persistent es i) = a.stacks (persistent es i)) ∧
      (∀ i : Fin 3, b.regs (controlRegister er i) = a.regs (controlRegister er i)) := by
  obtain ⟨out, hr, ho, t, ht, htrace⟩ := SubexpFrontendNormalizationProgram.program_runsIn F
    ((procedure er es).project a) hbody (project_ready a hwork)
  let b := (procedure er es).install a out
  refine ⟨t, ht, b, Procedure.invoke_trace _ _ _ htrace,
    install_workspace_clean a out hr, ?_, ?_, ?_⟩
  · exact (embedState_stack (procedure er es).registerMap (procedure er es).stack a out
      (procedure er es).stack.injective (16 : Fin 18)).trans ho
  · intro i hi
    exact embedState_stack_frame (procedure er es).registerMap (procedure er es).stack a out
      (persistent es i) (stackMap_avoids_persistent es i hi)
  · intro i
    exact Procedure.install_control _ _ _ i

theorem invoke_canonical {er es n : ℕ} (F : SAT.CNF (Fin n)) (a : MainState er es)
    (hbody : a.stacks (persistent es 0) = Encoding.encodeCNFBody F)
    (hwork : WorkspaceClean a) :
    ∃ t ≤ 3500 * ((Encoding.encodeCNFBody F).length + 1) ^ 2,
      ∃ b : MainState er es, Eval (procedure er es).invoke t a b ∧
      WorkspaceClean b ∧
      b.stacks (persistent es 0) = SubexpNormalizationCorrectness.normalizedBody F ∧
      (∀ i : Fin 32, i ≠ 0 → b.stacks (persistent es i) = a.stacks (persistent es i)) ∧
      (∀ i : Fin 3, b.regs (controlRegister er i) = a.regs (controlRegister er i)) := by
  obtain ⟨t, ht, b, he, hw, hb, hf, hc⟩ := invoke_eval (Encoding.cnfNumbers F) a hbody hwork
  have hout : SubexpNormalizationProgram.formulaCode
      (ExecCNF.normalize SubexpFrontend.negateCode (Encoding.cnfNumbers F)) =
      SubexpNormalizationCorrectness.normalizedBody F :=
    (ExecCNFCodeTransport.encode_normalized_formulaList F).symm
  exact ⟨t, ht, b, he, hw, hb.trans hout, hf, hc⟩

end SubexponentialSAT.SubexpMainNormalization

end OAI.Algorithms
