import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramLoops
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramConstructor
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCRTSetup
import OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl

namespace OAI.Algorithms

/-! Exact initialization and scan-state bridges for the native local CRT
controller. Only finite stack programs occur in these statements. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

/-- The initialization code, kept shallow so its trace can be checked
independently of the later arithmetic stages. Definitionally equal to
`initializeLocal` in the final controller. -/
def executionInitialization : Code :=
  .seq (SubexpPolynomialConstructor.construct 207 104 240)
    (.seq (copy 214 215) (.seq (copy 216 217) (SubexpLocalCRTSetup.token 229)))

def initializationBudget (J W nodes index : ℕ) : ℕ :=
  220 * (J + 1) * (W + 1) + 7 * (nodes + index) + 12

def initializedLocal (s : Store) (one : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update s 240 one)
    215 (s 214)) 217 (s 216)) 229 [true]

theorem initializeLocal_run (s : Store) (J W : ℕ)
    (hJ : s 243 = List.replicate J true)
    (hone : (s 207).length = W) (hzero : s 104 = List.replicate W false)
    (hclean : ∀ i ∈ ([100,101,102,107,108,120,215,217,229,240,245] : List (Fin 256)), s i = []) :
    ExecutesIn executionInitialization (initializationBudget J W (s 214).length (s 216).length) s
      (initializedLocal s (DensePolynomialProgram.Constructor.Counter.paddedBits W (s 207) (s 104) J)) := by
  let bits := DensePolynomialProgram.Constructor.Counter.paddedBits W (s 207) (s 104) J
  let s1 := Function.update s 240 bits
  let s2 := Function.update s1 215 (s 214)
  let s3 := Function.update s2 217 (s 216)
  have h1 : ExecutesIn (SubexpPolynomialConstructor.construct 207 104 240)
      (220 * (J + 1) * (W + 1)) s s1 := by
    exact DensePolynomialProgram.Constructor.construct_run s 207 104 240
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      J W hone (by simp [hzero]) hJ hzero
      (hclean 100 (by simp)) (hclean 101 (by simp)) (hclean 102 (by simp))
      (hclean 107 (by simp)) (hclean 108 (by simp)) (hclean 120 (by simp))
      (hclean 245 (by simp)) (hclean 240 (by simp))
  have h2 : ExecutesIn (copy 214 215) (7 * (s 214).length + 5) s1 s2 := by
    simpa [s2, s1, hclean 215 (by simp)] using copy_run 214 215 s1
      (by decide) (by decide) (by decide) (by simp [s1, hclean 120 (by simp)])
  have h3 : ExecutesIn (copy 216 217) (7 * (s 216).length + 5) s2 s3 := by
    simpa [s3, s2, s1, hclean 217 (by simp)] using copy_run 216 217 s2
      (by decide) (by decide) (by decide) (by simp [s2, s1, hclean 120 (by simp)])
  have h4 : ExecutesIn (SubexpLocalCRTSetup.token 229) 2 s3 (initializedLocal s bits) := by
    simpa [s3, s2, s1, initializedLocal, hclean 229 (by simp)] using
      SubexpLocalCRTSetup.token_run s3 229
  convert h1.seq (h2.seq (h3.seq h4)) using 1 <;>
    simp only [executionInitialization, initializationBudget] ; ring

theorem initializedLocal_eq_ready {C P : Type*} (s : Store)
    (encC : C → List Bool) (encP : P → List Bool) (cs : List C) (one : P)
    (hcs : s 214 = cs.flatMap encC) (h218 : s 218 = []) (h219 : s 219 = []) :
    initializedLocal s (encP one) = SubexpNodeScanControl.ready s encC encP cs
      ⟨one, s 216, true⟩ [] [] := by
  funext i
  by_cases hi : ∃ j, SubexpNodeScanControl.ports j = i
  · obtain ⟨j, rfl⟩ := hi
    fin_cases j <;> simp [initializedLocal, SubexpNodeScanControl.ready,
      SubexpNodeScanControl.words, SubexpNodeScanControl.ports, SubexpNodeScanControl.marker,
      hcs, h218, h219]
  · have hout := SubexpNodeScanControl.work_frame s
      (SubexpNodeScanControl.words encC encP cs ⟨one, s 216, true⟩ [] []) i hi
    have hneq (j : Fin 6) : i ≠ SubexpNodeScanControl.ports j := by
      intro h; exact hi ⟨j, h.symm⟩
    have h215 : i ≠ (215 : Fin 256) := hneq 0
    have h217 : i ≠ (217 : Fin 256) := hneq 1
    have h229 : i ≠ (229 : Fin 256) := hneq 2
    have h240 : i ≠ (240 : Fin 256) := hneq 3
    simpa [initializedLocal, SubexpNodeScanControl.ready, Function.update_apply,
      h215, h217, h229, h240] using hout.symm

theorem scan_skip_length_le {C P : Type*} (f : P → C → P) (cs : List C)
    (x : SubexpNodeScanControl.Cursor P) :
    (SubexpNodeScanControl.run f cs x).skip.length ≤ x.skip.length := by
  induction cs generalizing x with
  | nil => exact le_rfl
  | cons c cs ih =>
    apply (ih (SubexpNodeScanControl.next f c x)).trans
    rcases x with ⟨value, skip, pending⟩
    cases skip <;> cases pending <;> simp [SubexpNodeScanControl.next]

theorem cleared_scan_eq_factor {C P : Type*} (s : Store)
    (encC : C → List Bool) (encP : P → List Bool) (x : SubexpNodeScanControl.Cursor P)
    (hclean : ∀ i ∈ ([215,217,218,219,229] : List (Fin 256)), s i = []) :
    SubexpLocalCRTSetup.cleared [217,229]
      (SubexpNodeScanControl.ready s encC encP [] x [] []) = Function.update s 240 (encP x.value) := by
  funext i
  by_cases hi : ∃ j, SubexpNodeScanControl.ports j = i
  · obtain ⟨j, rfl⟩ := hi
    fin_cases j <;> simp [SubexpLocalCRTSetup.cleared_apply, SubexpNodeScanControl.ready,
      SubexpNodeScanControl.words, SubexpNodeScanControl.ports, hclean 215 (by simp),
      hclean 217 (by simp), hclean 218 (by simp), hclean 219 (by simp), hclean 229 (by simp)]
  · have hout := SubexpNodeScanControl.work_frame s
      (SubexpNodeScanControl.words encC encP [] x [] []) i hi
    have hneq (j : Fin 6) : i ≠ SubexpNodeScanControl.ports j := by
      intro h; exact hi ⟨j, h.symm⟩
    have h217 : i ≠ (217 : Fin 256) := hneq 1
    have h229 : i ≠ (229 : Fin 256) := hneq 2
    have h240 : i ≠ (240 : Fin 256) := hneq 3
    simpa [SubexpLocalCRTSetup.cleared_apply, SubexpNodeScanControl.ready,
      Function.update_apply, h217, h229, h240] using hout

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
