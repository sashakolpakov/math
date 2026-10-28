import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramInverse

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def defectValue {C : Type*} (mulOp addOp : C → C → C) (a b minusOne one : C) : C :=
  addOp (mulOp (mulOp b a) minusOne) one

def defectState {C : Type*} (s : Store) (encode : C → List Bool) (z one : C) : Store :=
  Function.update (Function.update (Function.update s 240 (encode z)) 241 (encode one))
    222 (encode z)

theorem defectCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a b minusOne one : C) (hf : LowFrame base s)
    (hacc : s 240 = encode b) (hright : s 241 = encode a)
    (hone : s 207 = encode one) (hminus : s 211 = encode minusOne)
    (h120 : s 120 = []) (h222 : s 222 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (defectCommand multiply add) (2*Km + Ka + 60*W + 60) s
      (defectState s encode (defectValue mulOp addOp a b minusOne one) one) := by
  let p := mulOp b a
  let n := mulOp p minusOne
  let z := addOp n one
  let s1 := Function.update s 240 (encode p)
  let s2 := Function.update s1 241 (encode minusOne)
  let s3 := Function.update s2 240 (encode n)
  let s4 := Function.update s3 241 (encode one)
  let s5 := Function.update s4 240 (encode z)
  have hf1 : LowFrame base s1 := lowFrame_update hf 240 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 241 (by decide) _
  have hf3 : LowFrame base s3 := lowFrame_update hf2 240 (by decide) _
  have hf4 : LowFrame base s4 := lowFrame_update hf3 241 (by decide) _
  have h1 : ExecutesIn (binaryStep multiply) (Km+8*W+9) s s1 :=
    binaryStep_run base encode multiply mulOp Km W hm hwidth s b a hf
      hacc hright h244 h245
  have h2 : ExecutesIn (replace 211 241) (9*W+8) s1 s2 := by
    simpa [s2, s1, hminus] using replace_bounded s1 211 241 W
      (by decide) (by decide) (by decide) (by simp [s1, h120])
      (by simpa [s1, hminus] using hwidth minusOne)
      (by simpa [s1, hright] using hwidth a)
  have h3 : ExecutesIn (binaryStep multiply) (Km+8*W+9) s2 s3 :=
    binaryStep_run base encode multiply mulOp Km W hm hwidth s2 p minusOne hf2
      (by simp [s2, s1]) (by simp [s2])
      (by simp [s2, s1, h244]) (by simp [s2, s1, h245])
  have h4 : ExecutesIn (replace 207 241) (9*W+8) s3 s4 := by
    simpa [s4, s3, s2, s1, hone] using replace_bounded s3 207 241 W
      (by decide) (by decide) (by decide) (by simp [s3, s2, s1, h120])
      (by simpa [s3, s2, s1, hone] using hwidth one)
      (by simpa [s3, s2] using hwidth minusOne)
  have h5 : ExecutesIn (binaryStep add) (Ka+8*W+9) s4 s5 :=
    binaryStep_run base encode add addOp Ka W ha hwidth s4 n one hf4
      (by simp [s4, s3]) (by simp [s4])
      (by simp [s4, s3, s2, s1, h244]) (by simp [s4, s3, s2, s1, h245])
  have h6 : ExecutesIn (replace 240 222) (9*W+8) s5
      (defectState s encode z one) := by
    have h := replace_bounded s5 240 222 W
      (by decide) (by decide) (by decide) (by simp [s5, s4, s3, s2, s1, h120])
      (by simpa [s5] using hwidth z) (by simp [s5, s4, s3, s2, s1, h222])
    have he : Function.update s5 222 (s5 240) = defectState s encode z one := by
      funext i
      by_cases h240 : i = 240 <;> by_cases h241 : i = 241 <;> by_cases h222 : i = 222 <;>
        simp [s5, s4, s3, s2, s1, defectState, h240, h241, h222]
    rw [he] at h
    exact h
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).mono (by omega)

def repairState {C : Type*} (s : Store) (encode : C → List Bool) (value : C) : Store :=
  SubexpLocalCRTSetup.cleared [220,222,240,241] (Function.update s 208 (encode value))

theorem repairCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (z b zero one : C) (hf : LowFrame base s)
    (hacc : s 240 = encode z) (hright : s 241 = encode one)
    (hone : s 207 = encode one) (hzero : s 104 = encode zero)
    (hb : s 208 = encode b) (hz : s 222 = encode z)
    (h120 : s 120 = []) (h220 : s 220 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (repairCommand multiply add)
      (((s 212).length+1)*(Km+Ka+150*W+200)) s
      (repairState s encode
        (mulOp ((hornerValue mulOp addOp z one)^[(s 212).length] zero) b)) := by
  let g := ((hornerValue mulOp addOp z one)^[(s 212).length] zero)
  let v := mulOp g b
  let s1 := Function.update s 240 (encode zero)
  let s2 := Function.update s1 241 (encode z)
  let s3 := Function.update s2 220 (encode one)
  let s4 := Function.update s3 246 (s 212)
  let s5 := Function.update s3 240 (encode g)
  let s6 := Function.update s5 241 (encode b)
  let s7 := Function.update s6 240 (encode v)
  let s8 := Function.update s7 208 (encode v)
  have hf1 : LowFrame base s1 := lowFrame_update hf 240 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 241 (by decide) _
  have hf3 : LowFrame base s3 := lowFrame_update hf2 220 (by decide) _
  have hf4 : LowFrame base s4 := lowFrame_update hf3 246 (by decide) _
  have hf5 : LowFrame base s5 := lowFrame_update hf3 240 (by decide) _
  have hf6 : LowFrame base s6 := lowFrame_update hf5 241 (by decide) _
  have h1 : ExecutesIn (replace 104 240) (9*W+8) s s1 := by
    simpa [s1, hzero] using replace_bounded s 104 240 W
      (by decide) (by decide) (by decide) h120
      (by simpa [hzero] using hwidth zero) (by simpa [hacc] using hwidth z)
  have h2 : ExecutesIn (replace 222 241) (9*W+8) s1 s2 := by
    simpa [s2, s1, hz] using replace_bounded s1 222 241 W
      (by decide) (by decide) (by decide) (by simp [s1, h120])
      (by simpa [s1, hz] using hwidth z) (by simpa [s1, hright] using hwidth one)
  have h3 : ExecutesIn (replace 207 220) (9*W+8) s2 s3 := by
    simpa [s3, s2, s1, hone] using replace_bounded s2 207 220 W
      (by decide) (by decide) (by decide) (by simp [s2, s1, h120])
      (by simpa [s2, s1, hone] using hwidth one) (by simp [s2, s1, h220])
  have h4 : ExecutesIn (replace 212 246) (7*(s 212).length+8) s3 s4 := by
    simpa [s4, s3, s2, s1, h246] using replace_run s3 212 246
      (by decide) (by decide) (by decide) (by simp [s3, s2, s1, h120])
  have h5 : ExecutesIn (hornerCommand multiply add)
      ((s 212).length*(Km+Ka+34*W+36)+2) s4 s5 := by
    have h := hornerCommand_state base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s4 z one zero hf4 (by simp [s4, s3, s2, s1]) (by simp [s4, s3, s2])
      (by simp [s4, s3]) (by simp [s4, s3, s2, s1, hz])
      (by simp [s4, s3, s2, s1, h120]) (by simp [s4, s3, s2, s1, h244])
      (by simp [s4, s3, s2, s1, h245])
    have hc : (s4 246).length = (s 212).length := by simp [s4]
    rw [hc] at h
    have he : Function.update (Function.update s4 240 (encode g)) 246 [] = s5 := by
      funext i
      by_cases hi : i = 240 <;> by_cases hj : i = 246 <;>
        simp [s5, s4, s3, s2, s1, Function.update_apply, hi, hj, h246]
    change ExecutesIn _ _ s4 (Function.update (Function.update s4 240 (encode g)) 246 []) at h
    rw [he] at h
    exact h
  have h6 : ExecutesIn (replace 208 241) (9*W+8) s5 s6 := by
    simpa [s6, s5, s3, s2, s1, hb] using replace_bounded s5 208 241 W
      (by decide) (by decide) (by decide) (by simp [s5, s3, s2, s1, h120])
      (by simpa [s5, s3, s2, s1, hb] using hwidth b)
      (by simpa [s5, s3, s2] using hwidth z)
  have h7 : ExecutesIn (binaryStep multiply) (Km+8*W+9) s6 s7 :=
    binaryStep_run base encode multiply mulOp Km W hm hwidth s6 g b hf6
      (by simp [s6, s5]) (by simp [s6])
      (by simp [s6, s5, s3, s2, s1, h244]) (by simp [s6, s5, s3, s2, s1, h245])
  have h8 : ExecutesIn (replace 240 208) (9*W+8) s7 s8 := by
    simpa [s8, s7] using replace_bounded s7 240 208 W
      (by decide) (by decide) (by decide) (by simp [s7, s6, s5, s3, s2, s1, h120])
      (by simpa [s7] using hwidth v)
      (by simpa [s7, s6, s5, s3, s2, s1, hb] using hwidth b)
  have h9 : ExecutesIn (SubexpLocalCRTSetup.clearMany [220,222,240,241]) (4*(2*W+3))
      s8 (repairState s encode v) := by
    have h := SubexpLocalCRTSetup.clearMany_run [220,222,240,241] s8 W (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · simpa [s8, s7, s6, s5, s3] using hwidth one
      · simpa [s8, s7, s6, s5, s3, s2, s1, hz] using hwidth z
      · simpa [s8, s7] using hwidth v
      · simpa [s8, s7, s6] using hwidth b)
    have he : SubexpLocalCRTSetup.cleared [220,222,240,241] s8 = repairState s encode v := by
      funext i
      simp only [repairState, SubexpLocalCRTSetup.cleared_apply]
      by_cases hi : i ∈ ([220,222,240,241] : List (Fin 256))
      · simp [hi]
      · simp only [ite_eq_right hi]
        have h220 : i ≠ 220 := by intro h; exact hi (by simp [h])
        have h222 : i ≠ 222 := by intro h; exact hi (by simp [h])
        have h240 : i ≠ 240 := by intro h; exact hi (by simp [h])
        have h241 : i ≠ 241 := by intro h; exact hi (by simp [h])
        simp [s8, s7, s6, s5, s3, s2, s1, Function.update_apply, h220, h240, h241]
    rw [he] at h
    exact h
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))
  apply h.mono
  nlinarith

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
