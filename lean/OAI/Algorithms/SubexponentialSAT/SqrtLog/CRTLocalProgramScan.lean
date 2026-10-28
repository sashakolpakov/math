import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramInclude
import OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

private theorem scan_ports_high (i : Fin 6) : 205 ≤ (SubexpNodeScanControl.ports i).val := by
  fin_cases i <;> decide

theorem scanReady_low {C P : Type*} (base : Store) (encC : C → List Bool) (encP : P → List Bool)
    (cs : List C) (x : SubexpNodeScanControl.Cursor P) (current negative : List Bool) :
    LowFrame base (SubexpNodeScanControl.ready base encC encP cs x current negative) := by
  intro i hi
  apply SubexpNodeScanControl.work_frame
  rintro ⟨j, hj⟩
  have hg := scan_ports_high j
  have hv := congrArg Fin.val hj
  omega

def localUpdate {C P : Type*} (cm ca : C → C → C) (pm : P → P → P)
    (linear : C → P) (theta minusOne : C) (J : ℕ) (acc : P) (c : C) : P :=
  (fun p => pm p (linear (differenceValue cm ca theta c minusOne)))^[J] acc

def scanCommand (sm sa pm : Code) : Code :=
  SubexpNodeScanControl.command (includeNodeCommand sm sa pm)

theorem includeNode_spec {C P : Type*} (base : Store)
    (encC : C → List Bool) (encP : P → List Bool)
    (sm sa pm : Code) (cm ca : C → C → C) (mulP : P → P → P)
    (Km Ka Kp W V J : ℕ) (theta one minusOne : C) (linear : C → P)
    (hsm : ServiceSpec base encC sm cm Km) (hsa : ServiceSpec base encC sa ca Ka)
    (hpm : ServiceSpec base encP pm mulP Kp)
    (hcwidth : ∀ a, (encC a).length = W) (hpwidth : ∀ a, (encP a).length ≤ V)
    (hlinear : ∀ a, encP (linear a) = DensePolynomialProgram.Constructor.Counter.paddedBits
      W (encC a) (encC one) J)
    (htheta : base 213 = encC theta) (hone : base 207 = encC one)
    (hminus : base 211 = encC minusOne) (hJ : base 243 = List.replicate J true)
    (hzero : base 104 = List.replicate W false)
    (hclean : ∀ i ∈ ([100,101,102,107,108,120,205,223,241,244,245,246] : List (Fin 256)),
      base i = []) :
    SubexpNodeScanControl.IncludeSpec (includeNodeCommand sm sa pm) base encC encP
      (fun _ => []) (localUpdate cm ca mulP linear theta minusOne J)
      (includeBudget Km Ka Kp W V J) := by
  intro cs x c
  let s := SubexpNodeScanControl.ready base encC encP cs x (encC c) []
  have hout (j : Fin 256) (hj : ¬ ∃ i, SubexpNodeScanControl.ports i = j) : s j = base j :=
    SubexpNodeScanControl.work_frame base _ j hj
  have h := includeNodeCommand_run base encC encP sm sa pm cm ca mulP Km Ka Kp W V J
    one minusOne linear hsm hsa hpm hcwidth hpwidth hlinear s theta c x.value
    (scanReady_low base encC encP cs x (encC c) [])
    ((hout 213 (by decide)).trans htheta)
    (by simp [s, SubexpNodeScanControl.ready, SubexpNodeScanControl.words])
    ((hout 207 (by decide)).trans hone) ((hout 211 (by decide)).trans hminus)
    ((hout 243 (by decide)).trans hJ) ((hout 104 (by decide)).trans hzero)
    ((hout 100 (by decide)).trans (hclean 100 (by simp)))
    ((hout 101 (by decide)).trans (hclean 101 (by simp)))
    ((hout 102 (by decide)).trans (hclean 102 (by simp)))
    ((hout 107 (by decide)).trans (hclean 107 (by simp)))
    ((hout 108 (by decide)).trans (hclean 108 (by simp)))
    ((hout 120 (by decide)).trans (hclean 120 (by simp)))
    ((hout 205 (by decide)).trans (hclean 205 (by simp)))
    (by simp [s, SubexpNodeScanControl.ready, SubexpNodeScanControl.words])
    ((hout 223 (by decide)).trans (hclean 223 (by simp)))
    (by simp [s, SubexpNodeScanControl.ready, SubexpNodeScanControl.words])
    ((hout 241 (by decide)).trans (hclean 241 (by simp)))
    ((hout 244 (by decide)).trans (hclean 244 (by simp)))
    ((hout 245 (by decide)).trans (hclean 245 (by simp)))
    ((hout 246 (by decide)).trans (hclean 246 (by simp)))
  have he : Function.update s 240
      (encP (localUpdate cm ca mulP linear theta minusOne J x.value c)) =
      SubexpNodeScanControl.ready base encC encP cs
        {x with value := localUpdate cm ca mulP linear theta minusOne J x.value c} (encC c) [] := by
    change Function.update (SubexpNodeScanControl.work base
      (SubexpNodeScanControl.words encC encP cs x (encC c) []))
      (SubexpNodeScanControl.ports 3) _ = _
    rw [← SubexpNodeScanControl.work_update]
    apply congrArg (SubexpNodeScanControl.work base)
    funext i
    fin_cases i <;> simp [SubexpNodeScanControl.words]
  change ExecutesIn _ _ s (Function.update s 240
    (encP (localUpdate cm ca mulP linear theta minusOne J x.value c))) at h
  rw [he] at h
  exact h

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
