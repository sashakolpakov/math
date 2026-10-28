import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramLoaded
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramEntry
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramExecution

namespace OAI.Algorithms

/-! The concrete caller frame seen at every loaded Hermite node. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram

/-- The native arithmetic context after the paid cache and width preparation. -/
def arithmeticBase (input : Data) : Fin 256 → List Bool :=
  (Function.update (Entry.prepared input.stacks) 104 (input.stacks 280)) ∘ localPorts

def workingClean : List (Fin 320) := Middle.cleanPorts ++
  CRTLocalProgram.localWork.map localPorts ++
  (List.ofFn fun i => localPorts (SubexpConvolutionControl.bufferPorts i))

def cleanPorts : List (Fin 320) := initialCleanPorts ++ workingClean ++ [5,10]

theorem initialized_low (input : Data) (J : ℕ) (exponent : List Bool) :
    CRTLocalProgram.LowFrame
      ((Function.update input.stacks 104 (input.stacks 280)) ∘ localPorts)
      ((initializedStacks input J exponent) ∘ localPorts) := by
  intro i hi
  have hn (j : Fin 320) (hj : 205 ≤ j.val) : localPorts i ≠ j := by
    intro he; have hval := congrArg Fin.val he
    change i.val = j.val at hval
    omega
  simp [initializedStacks,
    hn 261 (by decide), hn 268 (by decide), hn 277 (by decide),
    hn 214 (by decide), hn 257 (by decide), hn 266 (by decide)]

theorem workingClean_frame {I C : Type*} (input : Data) (J : ℕ) (exponent : List Bool)
    (encode jet : I → List Bool) (encodeAcc : C → List Bool)
    (processed remaining : List I) (i : I) (acc : C)
    (hc : ∀ j ∈ workingClean, input.stacks j = []) :
    ∀ j ∈ workingClean, sweepStore (initializedStacks input J exponent)
      (loadedReady encode jet encodeAcc processed remaining i acc) j = [] := by
  intro j hj
  have hs : List.Disjoint workingClean sweepChanged := by
    simp [List.Disjoint, workingClean, Middle.cleanPorts,
      CofactorOuter.cleanPorts, Scalar.cleanPorts, Horner.cleanPorts,
      CRTLocalProgram.localWork, SubexpConvolutionControl.bufferPorts,
      sweepChanged, localPorts]
  have hi : List.Disjoint workingClean initializationChanged := by
    simp [List.Disjoint, workingClean, Middle.cleanPorts,
      CofactorOuter.cleanPorts, Scalar.cleanPorts, Horner.cleanPorts,
      CRTLocalProgram.localWork, SubexpConvolutionControl.bufferPorts,
      initializationChanged, localPorts]
  rw [sweepStore_frame _ _ j (fun h => (List.disjoint_left.mp hs) hj h),
    initializedStacks_frame _ _ _ j (fun h => (List.disjoint_left.mp hi) hj h)]
  exact hc j hj

theorem entry_workingClean (input : Data) (hc : ∀ j ∈ cleanPorts, input.stacks j = []) :
    ∀ j ∈ workingClean, Entry.prepared input.stacks j = [] := by
  intro j hj
  have hd : List.Disjoint workingClean ([5,10] : List (Fin 320)) := by
    simp [List.Disjoint, workingClean, Middle.cleanPorts,
      CofactorOuter.cleanPorts, Scalar.cleanPorts, Horner.cleanPorts,
      CRTLocalProgram.localWork, SubexpConvolutionControl.bufferPorts, localPorts]
  have h5 : j ≠ (5 : Fin 320) := by
    intro he; exact (List.disjoint_left.mp hd) hj (by simp [he])
  have h10 : j ≠ (10 : Fin 320) := by
    intro he; exact (List.disjoint_left.mp hd) hj (by simp [he])
  simpa [Entry.prepared, h5, h10] using hc j (by simp [cleanPorts, hj])

theorem entry_initialClean (input : Data) (hc : ∀ j ∈ cleanPorts, input.stacks j = []) :
    ∀ j ∈ initialCleanPorts, Entry.prepared input.stacks j = [] := by
  intro j hj
  have hd : List.Disjoint initialCleanPorts ([5,10] : List (Fin 320)) := by
    simp [List.Disjoint, initialCleanPorts]
  have h5 : j ≠ (5 : Fin 320) := by
    intro he; exact (List.disjoint_left.mp hd) hj (by simp [he])
  have h10 : j ≠ (10 : Fin 320) := by
    intro he; exact (List.disjoint_left.mp hd) hj (by simp [he])
  simpa [Entry.prepared, h5, h10] using hc j (by simp [cleanPorts, hj])

end SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState

end OAI.Algorithms
