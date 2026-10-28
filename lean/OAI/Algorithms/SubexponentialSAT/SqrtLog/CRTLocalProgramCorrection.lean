import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramGeometricAt
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramCorrectionAlgebra

namespace OAI.Algorithms

/-! Native local Hermite correction once the truncated cofactor and its
constant inverse have been prepared. Only output244 changes. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def correctionCommand (multiply add : Code) : Code :=
  .seq (callAt multiply 223 228 222)
    (.seq (callAt add 222 220 222)
      (.seq (geometricAt multiply add)
        (.seq (callAt multiply 224 227 224)
          (.seq (callAt multiply 224 225 224)
            (.seq (replace 224 244) (SubexpLocalCRTSetup.clearMany [222,224]))))))

def correctionBudget (J Km Ka W : ℕ) : ℕ :=
  (J+1)*(4*Km+2*Ka+300*W+400)

theorem correctionCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (zero one negInverse inverse factor jet : C) (hf : LowFrame base s)
    (hzero : s 242 = encode zero) (hone : s 220 = encode one)
    (hneg : s 228 = encode negInverse) (hinv : s 227 = encode inverse)
    (hfactor : s 223 = encode factor) (hjet : s 225 = encode jet)
    (h120 : s 120 = []) (h222 : s 222 = []) (h224 : s 224 = [])
    (h240 : s 240 = []) (h241 : s 241 = []) (h244 : s 244 = [])
    (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (correctionCommand multiply add)
      (correctionBudget (s 243).length Km Ka W) s
      (Function.update s 244 (encode (correctionValue mulOp addOp
        zero one negInverse inverse factor jet (s 243).length))) := by
  let p := mulOp factor negInverse
  let z := addOp p one
  let g := (hornerValue mulOp addOp z one)^[(s 243).length] zero
  let inv := mulOp g inverse
  let v := mulOp inv jet
  let s1 := Function.update s 222 (encode p)
  let s2 := Function.update s1 222 (encode z)
  let s3 := Function.update s2 224 (encode g)
  let s4 := Function.update s3 224 (encode inv)
  let s5 := Function.update s4 224 (encode v)
  let s6 := Function.update s5 244 (encode v)
  have hf1 : LowFrame base s1 := lowFrame_update hf 222 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 222 (by decide) _
  have hf3 : LowFrame base s3 := lowFrame_update hf2 224 (by decide) _
  have hf4 : LowFrame base s4 := lowFrame_update hf3 224 (by decide) _
  have h1 : ExecutesIn (callAt multiply 223 228 222) (Km+40*W+50) s s1 :=
    callAt_run base encode multiply mulOp Km W hm hwidth s factor negInverse 223 228 222
      (by decide) (by decide) (by decide) hf hfactor hneg h120 h240 h241 h244 h245
      (by simp [h222])
  have h2 : ExecutesIn (callAt add 222 220 222) (Ka+40*W+50) s1 s2 :=
    callAt_run base encode add addOp Ka W ha hwidth s1 p one 222 220 222
      (by decide) (by decide) (by decide) hf1 (by simp [s1]) (by simp [s1, hone])
      (by simp [s1, h120]) (by simp [s1, h240]) (by simp [s1, h241])
      (by simp [s1, h244]) (by simp [s1, h245]) (by simpa [s1] using hwidth p)
  have h3 : ExecutesIn (geometricAt multiply add)
      (((s 243).length+1)*(Km+Ka+80*W+100)) s2 s3 := by
    have h := geometricAt_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s2 z zero one hf2 (by simp [s2, s1, hzero]) (by simp [s2, s1, hone])
      (by simp [s2]) (by simp [s2, s1, h120]) (by simp [s2, s1, h224])
      (by simp [s2, s1, h240]) (by simp [s2, s1, h241])
      (by simp [s2, s1, h244]) (by simp [s2, s1, h245]) (by simp [s2, s1, h246])
    simpa only [s3, s2, s1, Function.update_of_ne (show (243 : Fin 256) ≠ 222 by decide)] using h
  have h4 : ExecutesIn (callAt multiply 224 227 224) (Km+40*W+50) s3 s4 :=
    callAt_run base encode multiply mulOp Km W hm hwidth s3 g inverse 224 227 224
      (by decide) (by decide) (by decide) hf3 (by simp [s3])
      (by simp [s3, s2, s1, hinv]) (by simp [s3, s2, s1, h120])
      (by simp [s3, s2, s1, h240]) (by simp [s3, s2, s1, h241])
      (by simp [s3, s2, s1, h244]) (by simp [s3, s2, s1, h245])
      (by simpa [s3] using hwidth g)
  have h5 : ExecutesIn (callAt multiply 224 225 224) (Km+40*W+50) s4 s5 :=
    callAt_run base encode multiply mulOp Km W hm hwidth s4 inv jet 224 225 224
      (by decide) (by decide) (by decide) hf4 (by simp [s4])
      (by simp [s4, s3, s2, s1, hjet]) (by simp [s4, s3, s2, s1, h120])
      (by simp [s4, s3, s2, s1, h240]) (by simp [s4, s3, s2, s1, h241])
      (by simp [s4, s3, s2, s1, h244]) (by simp [s4, s3, s2, s1, h245])
      (by simpa [s4] using hwidth inv)
  have h6 : ExecutesIn (replace 224 244) (9*W+8) s5 s6 := by
    simpa [s6, s5] using replace_bounded s5 224 244 W (by decide) (by decide) (by decide)
      (by simp [s5, s4, s3, s2, s1, h120]) (by simpa [s5] using hwidth v)
      (by simp [s5, s4, s3, s2, s1, h244])
  have h7 : ExecutesIn (SubexpLocalCRTSetup.clearMany [222,224]) (2*(2*W+3)) s6
      (Function.update s 244 (encode v)) := by
    have h := SubexpLocalCRTSetup.clearMany_run [222,224] s6 W (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simpa [s6, s5, s4, s3, s2] using hwidth z
      · simpa [s6, s5] using hwidth v)
    have he : SubexpLocalCRTSetup.cleared [222,224] s6 = Function.update s 244 (encode v) := by
      funext i
      by_cases hi : i = 222 <;> by_cases hj : i = 224 <;> by_cases hk : i = 244 <;>
        simp [SubexpLocalCRTSetup.cleared_apply, s6, s5, s4, s3, s2, s1,
 hi, hj, hk, h222, h224]
    simpa only [he, List.length_cons, List.length_nil] using h
  apply (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))).mono
  dsimp [correctionBudget]
  nlinarith

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
