import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramDifference
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramConstructor

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def linearFactorCommand (multiply add : Code) : Code :=
  .seq (differenceCommand multiply add)
    (.seq (SubexpPolynomialConstructor.construct 205 207 241) (clear 205))

theorem linearFactorCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W J : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka) (hwidth : ∀ a, (encode a).length = W)
    (s : Store) (theta other one minusOne : C) (hf : LowFrame base s)
    (htheta : s 213 = encode theta) (hother : s 218 = encode other)
    (hone : s 207 = encode one) (hminus : s 211 = encode minusOne)
    (hJ : s 243 = List.replicate J true) (hzero : s 104 = List.replicate W false)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h107 : s 107 = []) (h108 : s 108 = []) (h120 : s 120 = [])
    (h205 : s 205 = []) (h219 : s 219 = []) (h240 : s 240 = [])
    (h241 : s 241 = []) (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (linearFactorCommand multiply add)
      (Km+Ka+102*W+113 + 220*(J+1)*(W+1)) s
      (Function.update s 241 (DensePolynomialProgram.Constructor.Counter.paddedBits W
        (encode (differenceValue mulOp addOp theta other minusOne)) (encode one) J)) := by
  let delta := differenceValue mulOp addOp theta other minusOne
  let bits := DensePolynomialProgram.Constructor.Counter.paddedBits W (encode delta) (encode one) J
  let s1 := Function.update s 205 (encode delta)
  let s2 := Function.update s1 241 bits
  have h1 : ExecutesIn (differenceCommand multiply add) (Km+Ka+100*W+110) s s1 :=
    differenceCommand_run base encode multiply add mulOp addOp Km Ka W hm ha
      (fun a => (hwidth a).le) s theta other minusOne hf htheta hother hminus h120
      h205 h219 h240 h241 h244 h245
  have h2 : ExecutesIn (SubexpPolynomialConstructor.construct 205 207 241)
      (220*(J+1)*(W+1)) s1 s2 := by
    have h := DensePolynomialProgram.Constructor.construct_run s1 205 207 241
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) J W
      (by simp [s1, hwidth]) (by simp [s1, hone, hwidth])
      (by simp [s1, hJ]) (by simp [s1, hzero])
      (by simp [s1, h100]) (by simp [s1, h101]) (by simp [s1, h102])
      (by simp [s1, h107]) (by simp [s1, h108]) (by simp [s1, h120])
      (by simp [s1, h245]) (by simp [s1, h241])
    simpa only [s2, s1, Function.update_same,
      Function.update_of_ne (show (207 : Fin 256) ≠ 205 by decide), hone] using h
  have h3 : ExecutesIn (clear 205) (2*W+3) s2 (Function.update s 241 bits) := by
    have h := clear_run 205 s2
    have he : Function.update s2 205 [] = Function.update s 241 bits := by
      funext i
      by_cases hi : i = 205 <;> simp [s2, s1, Function.update_apply, hi, h205]
    rw [he] at h
    simpa [s2, s1, hwidth] using h
  exact (h1.seq (h2.seq h3)).mono (by omega)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
