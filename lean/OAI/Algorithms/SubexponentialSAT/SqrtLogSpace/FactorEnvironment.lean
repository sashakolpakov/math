import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProduct

/-! The seven fixed persistent cache words are physically copied into the
native arithmetic environment. Cleanup clears those seven copies; both
commands frame all other stacks, including the query buffers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment

open OAI BitProgram StructuredCalls
open SubexpSetupStorage SqrtLog.MomentsProgram

abbrev Data := State 40 896

def registerMap : Fin 16 → Fin 40 := Fin.castAdd 24

def lowPort : Fin 56 → Fin 896 := Fin.castAdd 840

def pairs : List (Fin 896 × Fin 896) :=
  [(194, 5), (202, 12), (203, 17), (201, 22), (204, 39), (212, 45), (243, 46)]

def environmentPorts : List (Fin 896) := [5, 12, 17, 22, 39, 45, 46]

def bootstrap16 : Cmd 16 896 := copyMany 159 pairs

def reset16 : Cmd 16 896 := clearMany environmentPorts

def bootstrap : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram (compiled bootstrap16 194 5) registerMap id)

def reset : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram (compiled reset16 5 5) registerMap id)

noncomputable def bootstrapResult (a : Data) : Data :=
  embedState registerMap id a (copyManyState pairs (projectState registerMap id a))

noncomputable def resetResult (a : Data) : Data :=
  embedState registerMap id a (clearManyState environmentPorts (projectState registerMap id a))

def bootstrapCost (a : Data) : ℕ := copyManyCost pairs (projectState registerMap id a) + 1

def resetCost (a : Data) : ℕ := clearManyCost environmentPorts (projectState registerMap id a) + 1

theorem pairs_valid : ∀ p ∈ pairs, p.1 ≠ p.2 ∧ p.1 ≠ 159 ∧ (159 : Fin 896) ≠ p.2 := by
  intro p hp
  simp only [pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem bootstrap_eval (a : Data) (htmp : a.stacks 159 = []) :
    Eval bootstrap (bootstrapCost a) a (bootstrapResult a) := by
  have he := copyMany_eval 159 pairs (projectState registerMap id a) pairs_valid htmp
  exact eval_liftCommand_from_state bootstrap16 194 5 registerMap id a
    (Fin.castAdd_injective 16 24) Function.injective_id he

theorem reset_eval (a : Data) : Eval reset (resetCost a) a (resetResult a) := by
  have he := clearMany_eval environmentPorts (projectState registerMap id a)
  exact eval_liftCommand_from_state reset16 5 5 registerMap id a
    (Fin.castAdd_injective 16 24) Function.injective_id he

private theorem embed_identity_stacks (a : Data) (b : State 16 896) :
    (embedState registerMap id a b).stacks = b.stacks := by
  funext i
  exact Function.injective_id.extend_apply b.stacks a.stacks i

theorem bootstrap_stacks (a : Data) :
    (bootstrapResult a).stacks =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update a.stacks 5 (a.stacks 194 ++ a.stacks 5))
          12 (a.stacks 202 ++ a.stacks 12)) 17 (a.stacks 203 ++ a.stacks 17))
          22 (a.stacks 201 ++ a.stacks 22)) 39 (a.stacks 204 ++ a.stacks 39))
          45 (a.stacks 212 ++ a.stacks 45)) 46 (a.stacks 243 ++ a.stacks 46) := by
  funext i
  rw [bootstrapResult, embed_identity_stacks]
  simp only [pairs, copyManyState, copyState, StackRoutines.copyStacks, projectState,
    Function.comp_apply, id_eq, Function.update_of_ne (by decide : (202 : Fin 896) ≠ 5),
    Function.update_of_ne (by decide : (12 : Fin 896) ≠ 5)]
  simp

theorem bootstrap_frame (a : Data) (i : Fin 896) (hi : i ∉ environmentPorts) :
    (bootstrapResult a).stacks i = a.stacks i := by
  rw [bootstrapResult, embed_identity_stacks]
  apply copyMany_frame
  intro p hp
  simp only [pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  simp only [environmentPorts, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hi
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only; tauto

theorem bootstrap_low (a : Data) (hempty : ∀ i, a.stacks (lowPort i) = []) :
    ∀ i, (bootstrapResult a).stacks (lowPort i) =
      Product.tapes (Product.idle (a.stacks 194) (a.stacks 202) (a.stacks 203)
        (a.stacks 201) (a.stacks 204) (a.stacks 212) (a.stacks 243)) i := by
  have h5 : a.stacks 5 = [] := hempty 5
  have h12 : a.stacks 12 = [] := hempty 12
  have h17 : a.stacks 17 = [] := hempty 17
  have h22 : a.stacks 22 = [] := hempty 22
  have h39 : a.stacks 39 = [] := hempty 39
  have h45 : a.stacks 45 = [] := hempty 45
  have h46 : a.stacks 46 = [] := hempty 46
  intro i
  have hi := hempty i
  clear hempty
  rw [bootstrap_stacks]
  fin_cases i <;> simp_all [lowPort, Product.tapes, Product.idle]

theorem reset_stacks (a : Data) (i : Fin 896) :
    (resetResult a).stacks i = if i ∈ environmentPorts then [] else a.stacks i := by
  rw [resetResult, embed_identity_stacks, clearMany_stacks]
  rfl

theorem reset_frame (a : Data) (i : Fin 896) (hi : i ∉ environmentPorts) :
    (resetResult a).stacks i = a.stacks i := by simp [reset_stacks, hi]

theorem reset_low (a : Data)
    (hidle : ∀ i, a.stacks (lowPort i) =
      Product.tapes (Product.idle (a.stacks 194) (a.stacks 202) (a.stacks 203)
        (a.stacks 201) (a.stacks 204) (a.stacks 212) (a.stacks 243)) i) :
    ∀ i, (resetResult a).stacks (lowPort i) = [] := by
  intro i
  have hi := hidle i
  clear hidle
  rw [reset_stacks]
  fin_cases i <;> simp_all [lowPort, environmentPorts, Product.tapes, Product.idle]

private theorem word_le_total (a : Data) (i : Fin 896) :
    (a.stacks i).length ≤ stackBits a.stacks :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((a.stacks j).length)) (Finset.mem_univ i)

theorem bootstrapCost_le (a : Data) : bootstrapCost a ≤ 49 * stackBits a.stacks + 36 := by
  have h194 := word_le_total a 194
  have h202 := word_le_total a 202
  have h203 := word_le_total a 203
  have h201 := word_le_total a 201
  have h204 := word_le_total a 204
  have h212 := word_le_total a 212
  have h243 := word_le_total a 243
  simp [bootstrapCost, pairs, copyManyCost, copyState, StackRoutines.copyStacks, projectState]
  omega

theorem resetCost_le (a : Data) : resetCost a ≤ 14 * stackBits a.stacks + 22 := by
  have h5 := word_le_total a 5
  have h12 := word_le_total a 12
  have h17 := word_le_total a 17
  have h22 := word_le_total a 22
  have h39 := word_le_total a 39
  have h45 := word_le_total a 45
  have h46 := word_le_total a 46
  simp [resetCost, environmentPorts, clearManyCost, clearState, projectState]
  omega

theorem bootstrap_run_space (a : Data) (htmp : a.stacks 159 = []) :
    let program := compiled bootstrap 194 5
    Trace program (bootstrapCost a + 1) (a.withPC (some program.entry))
      ((bootstrapResult a).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ bootstrapCost a + 1 →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ 50 * stackBits a.stacks + 37 := by
  refine ⟨compiled_halt_trace (bootstrap_eval a htmp) 194 5, ?_⟩
  intro prefixSteps intermediate hp ht
  have hgrowth := trace_dataBits (compiled bootstrap 194 5) ht
  change dataBits intermediate ≤ stackBits a.stacks + prefixSteps at hgrowth
  have hb := bootstrapCost_le a
  omega

theorem reset_run_space (a : Data) :
    let program := compiled reset 5 5
    Trace program (resetCost a + 1) (a.withPC (some program.entry))
      ((resetResult a).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ resetCost a + 1 →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ 15 * stackBits a.stacks + 23 := by
  refine ⟨compiled_halt_trace (reset_eval a) 5 5, ?_⟩
  intro prefixSteps intermediate hp ht
  have hgrowth := trace_dataBits (compiled reset 5 5) ht
  change dataBits intermediate ≤ stackBits a.stacks + prefixSteps at hgrowth
  have hb := resetCost_le a
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment
