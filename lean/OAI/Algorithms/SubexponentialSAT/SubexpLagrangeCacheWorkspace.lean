import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeScalarCalls
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialMultiplyService
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialIterationControl

namespace OAI.Algorithms

/-! Concrete clean-workspace facts shared by the Lagrange product loop. -/

namespace SubexponentialSAT.SubexpLagrangeCacheWorkspace

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

def layout (modulus width reduction : List Bool) (B : ℕ) (i : Fin 256) : List Bool :=
  if i = 5 ∨ i = 194 then modulus else
  if i = 10 ∨ i = 202 then width else
  if i = 201 then reduction else
  if i = 104 then List.replicate (4 * B) false else []

def Ready (modulus width reduction : List Bool) (B : ℕ) (s : Store) : Prop :=
  ∀ i, i.val < 205 → s i = layout modulus width reduction B i

theorem Ready.update {modulus width reduction : List Bool} {B : ℕ} {s : Store}
    (h : Ready modulus width reduction B s) (dst : Fin 256)
    (hdst : 205 ≤ dst.val) (bits : List Bool) :
    Ready modulus width reduction B (Function.update s dst bits) := by
  intro i hi
  have hne : i ≠ dst := by intro he; subst i; omega
  simpa only [Function.update_of_ne hne] using h i hi

theorem layout_low (modulus width reduction : List Bool) (B : ℕ) (i : Fin 20) :
    layout modulus width reduction B (SubexpLocalLinearFactorProgram.addPorts i) =
      (SubexpFlatAdd.ready (fun _ => false) modulus [] [] width [] (fun _ => [])).stacks i := by
  fin_cases i <;> rfl

theorem layout_high (modulus width reduction : List Bool) (B : ℕ) (i : Fin 77) :
    layout modulus width reduction B (SubexpConvolutionPair.highPort i) =
      SubexpQuarticFlatMul.bankStore (fun _ => []) modulus reduction width [] i := by
  fin_cases i <;> rfl

theorem Ready.low {modulus width reduction : List Bool} {B : ℕ} {s : Store}
    (h : Ready modulus width reduction B s) (i : Fin 20) :
    s (SubexpLocalLinearFactorProgram.addPorts i) =
      (SubexpFlatAdd.ready (fun _ => false) modulus [] [] width [] (fun _ => [])).stacks i := by
  rw [h _ (by change i.val < 205; omega), layout_low]

theorem Ready.high {modulus width reduction : List Bool} {B : ℕ} {s : Store}
    (h : Ready modulus width reduction B s) (i : Fin 77) :
    s (SubexpConvolutionPair.highPort i) =
      SubexpQuarticFlatMul.bankStore (fun _ => []) modulus reduction width [] i := by
  rw [h _ (by change 128 + i.val < 205; omega), layout_high]

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

omit [Fact p.Prime] in
theorem Ready.polynomial {t : Quad (Word (baseWidth p μ))} {width : List Bool} {s : Store}
    (h : Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ) s)
    (hw : width.length = baseWidth p μ) :
    SubexpConvolutionPairSpec.BaseReady p μ M s t width (fun _ => []) := by
  refine ⟨?_, ?_, ?_, hw, ?_⟩
  · intro i _ _
    exact h.high i
  · intro i
    exact h.low i
  · rw [h 104 (by decide)]
    change (List.replicate (4 * baseWidth p μ) false).length = _
    exact List.length_replicate
  · intro j hj hj'
    rw [h j (by omega)]
    have h5 : j ≠ 5 := by intro e; subst j; norm_num [Fin.coe_ofNat_eq_mod] at hj
    have h194 : j ≠ 194 := by intro e; subst j; norm_num [Fin.coe_ofNat_eq_mod] at hj'
    have h10 : j ≠ 10 := by intro e; subst j; norm_num [Fin.coe_ofNat_eq_mod] at hj
    have h202 : j ≠ 202 := by intro e; subst j; norm_num [Fin.coe_ofNat_eq_mod] at hj'
    have h201 : j ≠ 201 := by intro e; subst j; norm_num [Fin.coe_ofNat_eq_mod] at hj'
    have h104 : j ≠ 104 := by intro e; subst j; norm_num [Fin.coe_ofNat_eq_mod] at hj
    simp [layout, h5, h194, h10, h202, h201, h104]

theorem Ready.buffers {modulus width reduction : List Bool} {B : ℕ} {s : Store}
    (h : Ready modulus width reduction B s) :
    ∀ i, s (bufferPorts i) = [] := by
  intro i
  fin_cases i <;> exact h _ (by decide)

omit [Fact p.Prime] in
theorem Ready.negative {t j : Quad (Word (baseWidth p μ))}
    {minusOne : Word (baseWidth p μ)} {width : List Bool} {s : Store}
    (h : Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ) s)
    (hm : s 211 = minusOne.val) (hj : s 218 = SubexpFlatAdd.encode j)
    (hout : s 219 = []) :
    ∀ i, s (SubexpLocalLinearFactorProgram.negatePorts i) =
      SubexpQuarticFlatNeg.initialStore j minusOne M.bits width i := by
  have hj' : s 218 = SubexpQuarticFlatNeg.flat j := by
    simpa only [SubexpLocalLinearFactorProgram.flat_eq_encode] using hj
  intro i
  fin_cases i <;> first | exact hm | exact hj' | exact hout | exact h _ (by decide)

def multiply : Code := .seq SubexpPolynomialMultiplyService.command
  SubexpPolynomialIterationControl.commit

theorem multiply_run (s : Store) (t z : Quad (Word (baseWidth p μ)))
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (h : Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ) s)
    (D : ℕ) (P Q : List (Quad (Word (baseWidth p μ))))
    (hP : P.length = D) (hQ : Q.length = D)
    (hleft : s 240 = SubexpConvolutionEncoding.encodeArray SubexpFlatAdd.encode P)
    (hright : s 241 = SubexpConvolutionEncoding.encodeArray SubexpFlatAdd.encode Q)
    (hzero : s 242 = SubexpConvolutionEncoding.encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hD : (s 243).length = D) (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn multiply (602000 * (D + 1)^3 * (baseWidth p μ + 1)^2) s
      (Function.update s 240 (SubexpConvolutionEncoding.encodeArray SubexpFlatAdd.encode
        (SubexpTruncatedMultiply.result p μ M t z D P Q))) := by
  have h120 : s 120 = [] := h _ (by decide)
  have h121 : s 121 = [] := h _ (by decide)
  have h122 : s 122 = [] := h _ (by decide)
  have hs := SubexpPolynomialMultiplyService.command_value p μ M s t z width (fun _ => [])
    (Ready.polynomial p μ M h hw) h.buffers h120 h121 h122 h244 h245 D P Q hP hQ hleft hright hzero hD
  have hr := SubexpPolynomialIterationControl.step_run SubexpPolynomialMultiplyService.command
    (601000 * (D + 1)^3 * (baseWidth p μ + 1)^2) s
    (SubexpConvolutionEncoding.encodeArray SubexpFlatAdd.encode
      (SubexpTruncatedMultiply.result p μ M t z D P Q)) h244 h245 hs
  apply hr.mono
  have hlen (xs : List (Quad (Word (baseWidth p μ)))) :
      (SubexpConvolutionEncoding.encodeArray SubexpFlatAdd.encode xs).length =
        xs.length * (4 * baseWidth p μ) :=
    SubexpConvolutionControl.encodeArray_length _ _ (fun a => SubexpFlatAdd.encode_length a) xs
  rw [hleft, hlen, hP, hlen, SubexpTruncatedMultiply.result_length]
  ring_nf
  omega

end SubexponentialSAT.SubexpLagrangeCacheWorkspace

end OAI.Algorithms
