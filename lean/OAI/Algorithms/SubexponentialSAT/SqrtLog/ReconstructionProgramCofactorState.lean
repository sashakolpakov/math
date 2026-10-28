import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramCofactorScan

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec)

private theorem run_false {C : Type*} (f : C → C → C) (cs : List C) (a : C) :
    SubexpNodeScanControl.run f cs ⟨a, [], false⟩ = ⟨cs.foldl f a, [], false⟩ := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih => simpa [SubexpNodeScanControl.run, SubexpNodeScanControl.next] using ih (f a c)

theorem ready_eq_of_ports {C : Type*} (s : Store) (encode : C → List Bool)
    (cs : List C) (a : C)
    (h : ∀ i, s (SubexpNodeScanControl.ports i) =
      SubexpNodeScanControl.words encode encode cs ⟨a, [], false⟩ [] [] i) :
    SubexpNodeScanControl.ready s encode encode cs ⟨a, [], false⟩ [] [] = s := by
  funext j
  by_cases hj : ∃ i, SubexpNodeScanControl.ports i = j
  · obtain ⟨i, rfl⟩ := hj
    exact (SubexpNodeScanControl.work_port s _ i).trans (h i).symm
  · exact SubexpNodeScanControl.work_frame s _ j hj

theorem scan_state_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply : Code) (mul : C → C → C) (minusOne : C) (K W J : ℕ)
    (hspec : ServiceSpec base encode multiply mul K)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (s : Store) (hf : LowFrame base s) (cs : List C) (unit : C)
    (hm : s 211 = encode minusOne) (hj : s 243 = List.replicate J true)
    (hwidth : (s 104).length = W)
    (hstream : s 215 = cs.flatMap encode) (hunit : s 240 = encode unit)
    (hclean : ∀ j ∈ ([120,121,122,217,218,219,223,229,241,244,245,246] : List (Fin 256)), s j = []) :
    ExecutesIn (scan multiply) (cs.length * (includeBudget K W J + 18 * W + 28) + 2) s
      (Function.update (Function.update s 215 [])
        240 (encode (cs.foldl (includeValue mul minusOne J) unit))) := by
  have hh := scan_run s encode multiply mul minusOne K W J
    (reframe_service hf encode multiply mul K hspec) hw hW hm hj hwidth
    (by
      intro j hj
      apply hclean j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
      tauto) cs unit
  have hin : SubexpNodeScanControl.ready s encode encode cs ⟨unit, [], false⟩ [] [] = s := by
    apply ready_eq_of_ports
    intro i
    fin_cases i <;> simp [SubexpNodeScanControl.ports, SubexpNodeScanControl.words,
      SubexpNodeScanControl.marker, hstream, hunit,
      hclean 217 (by simp), hclean 218 (by simp), hclean 219 (by simp), hclean 229 (by simp)]
  have hout : SubexpNodeScanControl.ready s encode encode []
      (SubexpNodeScanControl.run (includeValue mul minusOne J) cs ⟨unit, [], false⟩) [] [] =
      Function.update (Function.update s 215 [])
        240 (encode (cs.foldl (includeValue mul minusOne J) unit)) := by
    rw [run_false]
    conv_rhs => rw [← hin]
    change SubexpNodeScanControl.work s _ = Function.update (Function.update
      (SubexpNodeScanControl.work s _) (SubexpNodeScanControl.ports 0) [])
        (SubexpNodeScanControl.ports 3) _
    rw [← SubexpNodeScanControl.work_update, ← SubexpNodeScanControl.work_update]
    apply congrArg (SubexpNodeScanControl.work s)
    funext i
    fin_cases i <;> simp [SubexpNodeScanControl.words]
  simpa only [hin, hout] using hh

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

end OAI.Algorithms
