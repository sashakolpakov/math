import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramCofactor

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec)

private theorem scan_ports_high (i : Fin 6) : 205 ≤ (SubexponentialSAT.SubexpNodeScanControl.ports i).val := by
  fin_cases i <;> decide

theorem ready_low {C : Type*} (base : Store) (encode : C → List Bool)
    (cs : List C) (x : SubexponentialSAT.SubexpNodeScanControl.Cursor C) (current negative : List Bool) :
    LowFrame base (SubexponentialSAT.SubexpNodeScanControl.ready base encode encode cs x current negative) := by
  intro i hi
  apply SubexpNodeScanControl.work_frame
  rintro ⟨j, hj⟩
  have hg := scan_ports_high j
  have hv := congrArg Fin.val hj
  omega

private theorem ready_outside {C : Type*} (base : Store) (encode : C → List Bool)
    (cs : List C) (x : SubexponentialSAT.SubexpNodeScanControl.Cursor C) (current negative : List Bool) (j : Fin 256)
    (hj : ¬ ∃ i, SubexponentialSAT.SubexpNodeScanControl.ports i = j) :
    SubexponentialSAT.SubexpNodeScanControl.ready base encode encode cs x current negative j = base j :=
  SubexpNodeScanControl.work_frame base _ j hj

theorem include_spec {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply : Code) (mul : C → C → C) (minusOne : C) (K W J : ℕ)
    (hspec : ServiceSpec base encode multiply mul K)
    (hw : ∀ a, (encode a).length ≤ W)
    (hm : base 211 = encode minusOne) (hj : base 243 = List.replicate J true)
    (hclean : ∀ j ∈ ([120,223,241,244,245,246] : List (Fin 256)), base j = []) :
    SubexpNodeScanControl.IncludeSpec (includeNode multiply) base encode encode
      (fun c => encode (mul c minusOne)) (includeValue mul minusOne J) (includeBudget K W J) := by
  intro cs x c
  let s := SubexponentialSAT.SubexpNodeScanControl.ready base encode encode cs x (encode c) []
  have hout (j : Fin 256) (h : ¬ ∃ i, SubexponentialSAT.SubexpNodeScanControl.ports i = j) : s j = base j :=
    ready_outside base encode cs x (encode c) [] j h
  have hh := includeNode_run base encode multiply mul minusOne K W J hspec hw s x.value c
    (ready_low base encode cs x (encode c) [])
    (by simp [s, SubexponentialSAT.SubexpNodeScanControl.ready, SubexponentialSAT.SubexpNodeScanControl.words]) (by simp [s, SubexponentialSAT.SubexpNodeScanControl.ready, SubexponentialSAT.SubexpNodeScanControl.words])
    ((hout 211 (by decide)).trans hm) ((hout 243 (by decide)).trans hj)
    ((hout 120 (by decide)).trans (hclean 120 (by simp)))
    (by simp [s, SubexponentialSAT.SubexpNodeScanControl.ready, SubexponentialSAT.SubexpNodeScanControl.words])
    ((hout 223 (by decide)).trans (hclean 223 (by simp)))
    ((hout 241 (by decide)).trans (hclean 241 (by simp)))
    ((hout 244 (by decide)).trans (hclean 244 (by simp)))
    ((hout 245 (by decide)).trans (hclean 245 (by simp)))
    ((hout 246 (by decide)).trans (hclean 246 (by simp)))
  have he : Function.update (Function.update s 240
      (encode (includeValue mul minusOne J x.value c))) 219 (encode (mul c minusOne)) =
      SubexponentialSAT.SubexpNodeScanControl.ready base encode encode cs {x with value := includeValue mul minusOne J x.value c}
        (encode c) (encode (mul c minusOne)) := by
    change Function.update (Function.update (SubexponentialSAT.SubexpNodeScanControl.work base (SubexponentialSAT.SubexpNodeScanControl.words encode encode cs x (encode c) []))
      (SubexponentialSAT.SubexpNodeScanControl.ports 3) _) (SubexponentialSAT.SubexpNodeScanControl.ports 5) _ = _
    rw [← SubexpNodeScanControl.work_update, ← SubexpNodeScanControl.work_update]
    apply congrArg (SubexponentialSAT.SubexpNodeScanControl.work base)
    funext i
    fin_cases i <;> simp [SubexponentialSAT.SubexpNodeScanControl.words]
  simpa only [he] using hh

def scan (multiply : Code) : Code := SubexpNodeScanControl.command (includeNode multiply)

theorem scan_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply : Code) (mul : C → C → C) (minusOne : C) (K W J : ℕ)
    (hspec : ServiceSpec base encode multiply mul K)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (hm : base 211 = encode minusOne) (hj : base 243 = List.replicate J true)
    (hwidth : (base 104).length = W)
    (hclean : ∀ j ∈ ([120,121,122,223,241,244,245,246] : List (Fin 256)), base j = [])
    (cs : List C) (unit : C) :
    ExecutesIn (scan multiply) (cs.length * (includeBudget K W J + 18 * W + 28) + 2)
      (SubexponentialSAT.SubexpNodeScanControl.ready base encode encode cs ⟨unit, [], false⟩ [] [])
      (SubexponentialSAT.SubexpNodeScanControl.ready base encode encode []
        (SubexpNodeScanControl.run (includeValue mul minusOne J) cs ⟨unit, [], false⟩) [] []) := by
  apply SubexpNodeScanControl.command_run (includeNode multiply) base encode encode
    (fun c => encode (mul c minusOne)) (includeValue mul minusOne J)
    (includeBudget K W J) W _ hw hW (fun c => (hw _).le) hwidth
    (hclean 121 (by simp)) (hclean 122 (by simp)) cs ⟨unit, [], false⟩
  apply include_spec base encode multiply mul minusOne K W J hspec (fun a => (hw a).le) hm hj
  intro j hj
  apply hclean j
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
  tauto

section Semantics
variable {C A : Type*} [CommRing A]

theorem includeValue_decode (decode : C → A) (mul : C → C → C)
    (hmul : ∀ a b, decode (mul a b) = decode a * decode b)
    (minusOne : C) (hminus : decode minusOne = -1) (J : ℕ) (a c : C) :
    decode (includeValue mul minusOne J a c) = decode a * (-decode c)^J := by
  rw [includeValue, CRTLocalProgram.iterate_mul_decode decode mul hmul, hmul, hminus]
  simp

theorem scan_decode (decode : C → A) (mul : C → C → C)
    (hmul : ∀ a b, decode (mul a b) = decode a * decode b)
    (minusOne : C) (hminus : decode minusOne = -1) (J : ℕ) (cs : List C) (unit : C)
    (hu : decode unit = 1) :
    decode (SubexpNodeScanControl.run (includeValue mul minusOne J) cs ⟨unit, [], false⟩).value =
      (cs.map (fun c => (-decode c)^J)).prod := by
  rw [SubexpNodeScanControl.run_after_skip]
  have hfold (a : C) : decode (cs.foldl (includeValue mul minusOne J) a) =
      decode a * (cs.map (fun c => (-decode c)^J)).prod := by
    induction cs generalizing a with
    | nil => simp
    | cons c cs ih =>
      rw [List.foldl_cons, ih, includeValue_decode decode mul hmul minusOne hminus]
      simp [mul_assoc]
  rw [hfold, hu, one_mul]
end Semantics

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

end OAI.Algorithms
