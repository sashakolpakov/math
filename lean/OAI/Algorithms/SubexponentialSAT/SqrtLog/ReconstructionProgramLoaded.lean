import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramMiddle
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramControl

namespace OAI.Algorithms

/-! Framing lemmas for the exact states reached by the physical node sweep. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram

abbrev Store := Fin 320 → List Bool

def sweepChanged : List (Fin 320) := [213,216,225,257,258,259,260,261,266]
def initializationChanged : List (Fin 320) := [104,261,268,277,214,257,266]

theorem sweepStore_frame (f : Store) (w : SweepWords) (j : Fin 320)
    (hj : j ∉ sweepChanged) : sweepStore f w j = f j := by
  simp only [sweepChanged, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp [sweepStore, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1,
    hj.2.2.2.2.2.1, hj.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2]

theorem initializedStacks_frame (d : Data) (J : ℕ) (exponent : List Bool) (j : Fin 320)
    (hj : j ∉ initializationChanged) : initializedStacks d J exponent j = d.stacks j := by
  simp only [initializationChanged, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp [initializedStacks, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1,
    hj.2.2.2.2.1, hj.2.2.2.2.2.1, hj.2.2.2.2.2.2]

theorem loaded_low {I C : Type*} (f : Store) (encode jet : I → List Bool)
    (encodeAcc : C → List Bool) (processed remaining : List I) (i : I) (acc : C) :
    CRTLocalProgram.LowFrame (f ∘ localPorts)
      ((sweepStore f (loadedReady encode jet encodeAcc processed remaining i acc)) ∘ localPorts) := by
  intro j hj
  apply sweepStore_frame
  simp only [sweepChanged, List.mem_cons, List.not_mem_nil, or_false]
  intro h
  have hv : (localPorts j).val = j.val := rfl
  rcases h with h | h | h | h | h | h | h | h | h <;>
    have hh := congrArg Fin.val h <;> norm_num at hh <;> omega

theorem loaded_clean {I C : Type*} (d : Data) (J : ℕ) (exponent : List Bool)
    (encode jet : I → List Bool) (encodeAcc : C → List Bool)
    (processed remaining : List I) (i : I) (acc : C)
    (hc : ∀ j ∈ Middle.cleanPorts, d.stacks j = []) :
    ∀ j ∈ Middle.cleanPorts,
      sweepStore (initializedStacks d J exponent)
        (loadedReady encode jet encodeAcc processed remaining i acc) j = [] := by
  intro j hj
  have hs : List.Disjoint Middle.cleanPorts sweepChanged := by
    simp [List.Disjoint, Middle.cleanPorts, CofactorOuter.cleanPorts,
      Scalar.cleanPorts, Horner.cleanPorts, sweepChanged]
  have hi : List.Disjoint Middle.cleanPorts initializationChanged := by
    simp [List.Disjoint, Middle.cleanPorts, CofactorOuter.cleanPorts,
      Scalar.cleanPorts, Horner.cleanPorts, initializationChanged]
  rw [sweepStore_frame _ _ j (fun h => (List.disjoint_left.mp hs) hj h),
    initializedStacks_frame _ _ _ j (fun h => (List.disjoint_left.mp hi) hj h)]
  exact hc j hj

theorem loaded_update_acc {I C : Type*} (f : Store) (encode jet : I → List Bool)
    (encodeAcc : C → List Bool) (processed remaining : List I) (i : I) (a b : C) :
    Function.update (sweepStore f (loadedReady encode jet encodeAcc processed remaining i a))
      261 (encodeAcc b) =
      sweepStore f (loadedReady encode jet encodeAcc processed remaining i b) := by
  funext j
  by_cases h : j = 261
  · subst j; simp [loadedReady, loadedWords, readyWords]
  · simp only [Function.update_of_ne h]
    simp [sweepStore, loadedReady, loadedWords, readyWords, h]

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
