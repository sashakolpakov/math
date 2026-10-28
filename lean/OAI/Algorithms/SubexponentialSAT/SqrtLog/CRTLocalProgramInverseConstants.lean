import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramConstant
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramConstructor

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def inverseConstantsBudget (e t J Km Ka W : ℕ) : ℕ :=
  inverseBudget e t Km Ka W + Km+44*W+56+440*(J+1)*(W+1)

theorem inverseConstantsCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (sm sa : Code) (cm ca : C → C → C) (Km Ka W J : ℕ)
    (hm : ServiceSpec base encode sm cm Km) (ha : ServiceSpec base encode sa ca Ka)
    (hw : ∀ a, (encode a).length = W)
    (s : Store) (c zero one minusOne : C) (hf : LowFrame base s)
    (hc : s 205 = encode c) (hz : s 104 = encode zero)
    (hzbits : encode zero = List.replicate W false)
    (ho : s 207 = encode one) (hn : s 211 = encode minusOne)
    (hJ : s 243 = List.replicate J true)
    (hclean : ∀ i ∈ ([100,101,102,107,108,120,208,220,222,227,228,240,241,244,245,246] : List (Fin 256)),
      s i = []) :
    let a := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
    ExecutesIn (inverseConstantsCommand sm sa)
      (inverseConstantsBudget (s 209).length (s 212).length J Km Ka W) s
      (Function.update (Function.update (Function.update s 205 []) 227
        (DensePolynomialProgram.Constructor.Counter.paddedBits W (encode a) (encode zero) J)) 228
        (DensePolynomialProgram.Constructor.Counter.paddedBits W (encode (cm a minusOne)) (encode zero) J)) := by
  let a := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
  let neg := cm a minusOne
  let bits := DensePolynomialProgram.Constructor.Counter.paddedBits W (encode a) (encode zero) J
  let negbits := DensePolynomialProgram.Constructor.Counter.paddedBits W (encode neg) (encode zero) J
  let s1 := Function.update s 208 (encode a)
  let s2 := Function.update s1 205 (encode neg)
  let s3 := Function.update s2 227 bits
  let s4 := Function.update s3 228 negbits
  have hf1 : LowFrame base s1 := lowFrame_update hf 208 (by decide) _
  have h1 : ExecutesIn (inverseCommand sm sa)
      (inverseBudget (s 209).length (s 212).length Km Ka W) s s1 :=
    inverseCommand_run base encode sm sa cm ca Km Ka W hm ha (fun a => (hw a).le)
      s c zero one minusOne hf hc hz ho hn
      (hclean 120 (by simp)) (hclean 208 (by simp))
      (hclean 220 (by simp)) (hclean 222 (by simp))
      (hclean 240 (by simp)) (hclean 241 (by simp))
      (hclean 244 (by simp)) (hclean 245 (by simp)) (hclean 246 (by simp))
  have h2 : ExecutesIn (callAt sm 208 211 205) (Km+40*W+50) s1 s2 :=
    callAt_run base encode sm cm Km W hm (fun a => (hw a).le) s1 a minusOne 208 211 205
      (by decide) (by decide) (by decide) hf1 (by simp [s1]) (by simp [s1, hn])
      (by simp [s1, hclean 120 (by simp)]) (by simp [s1, hclean 240 (by simp)])
      (by simp [s1, hclean 241 (by simp)]) (by simp [s1, hclean 244 (by simp)])
      (by simp [s1, hclean 245 (by simp)]) (by simp [s1, hc, hw])
  have h3 : ExecutesIn (SubexpPolynomialConstructor.construct 208 104 227)
      (220*(J+1)*(W+1)) s2 s3 := by
    have h := DensePolynomialProgram.Constructor.construct_run s2 208 104 227
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) J W
      (by simp [s2, s1, hw]) (by simp [s2, s1, hz, hw])
      (by simp [s2, s1, hJ]) (by simp [s2, s1, hz, hzbits])
      (by simp [s2, s1, hclean 100 (by simp)]) (by simp [s2, s1, hclean 101 (by simp)])
      (by simp [s2, s1, hclean 102 (by simp)]) (by simp [s2, s1, hclean 107 (by simp)])
      (by simp [s2, s1, hclean 108 (by simp)]) (by simp [s2, s1, hclean 120 (by simp)])
      (by simp [s2, s1, hclean 245 (by simp)]) (by simp [s2, s1, hclean 227 (by simp)])
    simpa [s3, s2, s1, bits, hz] using h
  have h4 : ExecutesIn (SubexpPolynomialConstructor.construct 205 104 228)
      (220*(J+1)*(W+1)) s3 s4 := by
    have h := DensePolynomialProgram.Constructor.construct_run s3 205 104 228
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) J W
      (by simp [s3, s2, s1, hw]) (by simp [s3, s2, s1, hz, hw])
      (by simp [s3, s2, s1, hJ]) (by simp [s3, s2, s1, hz, hzbits])
      (by simp [s3, s2, s1, hclean 100 (by simp)]) (by simp [s3, s2, s1, hclean 101 (by simp)])
      (by simp [s3, s2, s1, hclean 102 (by simp)]) (by simp [s3, s2, s1, hclean 107 (by simp)])
      (by simp [s3, s2, s1, hclean 108 (by simp)]) (by simp [s3, s2, s1, hclean 120 (by simp)])
      (by simp [s3, s2, s1, hclean 245 (by simp)]) (by simp [s3, s2, s1, hclean 228 (by simp)])
    simpa [s4, s3, s2, s1, negbits, hz] using h
  have h5 : ExecutesIn (SubexpLocalCRTSetup.clearMany [205,208]) (2*(2*W+3)) s4
      (Function.update (Function.update (Function.update s 205 []) 227 bits) 228 negbits) := by
    have h := SubexpLocalCRTSetup.clearMany_run [205,208] s4 W (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simp [s4, s3, s2, hw]
      · simp [s4, s3, s2, s1, hw])
    have he : SubexpLocalCRTSetup.cleared [205,208] s4 =
        Function.update (Function.update (Function.update s 205 []) 227 bits) 228 negbits := by
      funext i
      by_cases h205 : i = 205 <;> by_cases h208 : i = 208 <;>
        by_cases h227 : i = 227 <;> by_cases h228 : i = 228 <;>
        simp [SubexpLocalCRTSetup.cleared_apply, s4, s3, s2, s1,
 h205, h208, h227, h228, hclean 208 (by simp)]
    simpa only [he, List.length_cons, List.length_nil] using h
  exact (h1.seq (h2.seq (h3.seq (h4.seq h5)))).mono (by
    dsimp [inverseConstantsBudget]
    ring_nf
    omega)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
