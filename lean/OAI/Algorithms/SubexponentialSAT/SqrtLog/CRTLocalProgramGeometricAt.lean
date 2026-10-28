import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramCall

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def geometricAt (multiply add : Code) : Code :=
  .seq (replace 242 240) (.seq (replace 222 241) (.seq (replace 243 246)
    (.seq (hornerCommand multiply add) (.seq (replace 240 224)
      (SubexpLocalCRTSetup.clearMany [240,241])))))

theorem geometricAt_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (z zero one : C) (hf : LowFrame base s)
    (hzero : s 242 = encode zero) (hone : s 220 = encode one) (hz : s 222 = encode z)
    (h120 : s 120 = []) (h224 : s 224 = []) (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (geometricAt multiply add) (((s 243).length+1)*(Km+Ka+80*W+100)) s
      (Function.update s 224 (encode ((hornerValue mulOp addOp z one)^[(s 243).length] zero))) := by
  let g := (hornerValue mulOp addOp z one)^[(s 243).length] zero
  let s1 := Function.update s 240 (encode zero)
  let s2 := Function.update s1 241 (encode z)
  let s3 := Function.update s2 246 (s 243)
  let s4 := Function.update s2 240 (encode g)
  let s5 := Function.update s4 224 (encode g)
  have hf1 : LowFrame base s1 := lowFrame_update hf 240 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 241 (by decide) _
  have hf3 : LowFrame base s3 := lowFrame_update hf2 246 (by decide) _
  have h1 : ExecutesIn (replace 242 240) (9*W+8) s s1 := by
    simpa [s1, hzero] using replace_bounded s 242 240 W (by decide) (by decide) (by decide)
      h120 (by simpa [hzero] using hwidth zero) (by simp [h240])
  have h2 : ExecutesIn (replace 222 241) (9*W+8) s1 s2 := by
    simpa [s2, s1, hz] using replace_bounded s1 222 241 W (by decide) (by decide) (by decide)
      (by simp [s1, h120]) (by simpa [s1, hz] using hwidth z) (by simp [s1, h241])
  have h3 : ExecutesIn (replace 243 246) (7*(s 243).length+8) s2 s3 := by
    simpa [s3, s2, s1, h246] using replace_run s2 243 246 (by decide) (by decide) (by decide)
      (by simp [s2, s1, h120])
  have h4 : ExecutesIn (hornerCommand multiply add)
      ((s 243).length*(Km+Ka+34*W+36)+2) s3 s4 := by
    have h := hornerCommand_state base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s3 z one zero hf3 (by simp [s3, s2, s1]) (by simp [s3, s2])
      (by simp [s3, s2, s1, hone]) (by simp [s3, s2, s1, hz])
      (by simp [s3, s2, s1, h120]) (by simp [s3, s2, s1, h244])
      (by simp [s3, s2, s1, h245])
    have hc : (s3 246).length = (s 243).length := by simp [s3]
    rw [hc] at h
    have he : Function.update (Function.update s3 240 (encode g)) 246 [] = s4 := by
      funext i
      by_cases hi : i = 240 <;> by_cases hj : i = 246 <;>
        simp [s4, s3, s2, s1, Function.update_apply, hi, hj, h246]
    change ExecutesIn _ _ s3 (Function.update (Function.update s3 240 (encode g)) 246 []) at h
    rw [he] at h
    exact h
  have h5 : ExecutesIn (replace 240 224) (9*W+8) s4 s5 := by
    simpa [s5, s4] using replace_bounded s4 240 224 W (by decide) (by decide) (by decide)
      (by simp [s4, s2, s1, h120]) (by simpa [s4] using hwidth g)
      (by simp [s4, s2, s1, h224])
  have h6 : ExecutesIn (SubexpLocalCRTSetup.clearMany [240,241]) (2*(2*W+3)) s5
      (Function.update s 224 (encode g)) := by
    have h := SubexpLocalCRTSetup.clearMany_run [240,241] s5 W (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simpa [s5, s4] using hwidth g
      · simpa [s5, s4, s2] using hwidth z)
    have he : SubexpLocalCRTSetup.cleared [240,241] s5 = Function.update s 224 (encode g) := by
      funext i
      by_cases hi : i = 240 <;> by_cases hj : i = 241 <;> by_cases hk : i = 224 <;>
        simp [SubexpLocalCRTSetup.cleared_apply, s5, s4, s2, s1,
 hi, hj, hk, h240, h241]
    simpa only [he, List.length_cons, List.length_nil] using h
  apply (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).mono
  nlinarith

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
