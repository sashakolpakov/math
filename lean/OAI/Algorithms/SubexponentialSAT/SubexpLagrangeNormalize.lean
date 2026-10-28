import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeInverseCall
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheWorkspace

namespace OAI.Algorithms

/-! Actual Lagrange-row normalization. The computed scalar inverse is
marshalled into a padded constant polynomial, multiplied by the row, and
all temporary scalar and polynomial cells are cleared. -/

namespace SubexponentialSAT.SubexpLagrangeNormalize

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpLagrangeCacheWorkspace

abbrev Coefficient (p μ : ℕ) := Quad (Word (baseWidth p μ))

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def scale : Code :=
  clear 205 ;; copy 214 100 ;; copy 104 101 ;;
    SubexpPolynomialConstructor.constructAtInputs 241 ;;
    clear 214 ;; SubexpLagrangeCacheWorkspace.multiply ;; clear 241

def command : Code := SubexpLagrangeInverseCall.command ;; scale

abbrev program : Program 16 256 (size command + 1) := compiled command 205 240

theorem flat_eq_encode {B : ℕ} (a : Quad (Word B)) :
    SubexpQuarticFlatMul.flat a = SubexpFlatAdd.encode a :=
  (SubexpLagrangeInverseCall.flat_eq a).symm.trans
    (SubexpQuarticFlatInverse.flat_eq_encode a)

private theorem power_native (i : Fin 77) :
    SubexpLagrangeInverseCall.powerPorts (SubexpQuarticPowerCore.native i) =
      SubexpConvolutionPair.highPort i := by
  have hne (j : Fin 83) (hj : 77 ≤ j.val) : SubexpQuarticPowerCore.native i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = j.val at hv
    omega
  simp only [SubexpLagrangeInverseCall.powerPorts,
    ite_eq_right (hne 78 (by decide)), ite_eq_right (hne 80 (by decide)),
    ite_eq_right (hne 81 (by decide)), ite_eq_right (hne 82 (by decide))]
  rfl

theorem powerReady {B : ℕ} {modulus width exponent : List Bool}
    {t a one : Quad (Word B)} {s : Store}
    (H : Ready modulus width (SubexpQuarticFlatMul.flat t) B s)
    (h205 : s 205 = SubexpFlatAdd.encode a)
    (h207 : s 207 = SubexpFlatAdd.encode one) (h225 : s 225 = exponent)
    (h215 : s 215 = []) (h216 : s 216 = []) (h219 : s 219 = []) :
    SubexpLagrangeInverseCall.PowerReady modulus width exponent t a one s := by
  refine ⟨?_, ?_, h225, ?_, h215, h216, h219⟩
  · intro i
    rw [power_native]
    exact H.high i
  · simpa only [flat_eq_encode] using h205
  · simpa only [flat_eq_encode] using h207

theorem inverseReady {B : ℕ} {modulus width counter : List Bool}
    {t a one : Quad (Word B)} {minusOne : Word B} {s : Store}
    (H : Ready modulus width (SubexpQuarticFlatMul.flat t) B s)
    (h205 : s 205 = SubexpFlatAdd.encode a)
    (h207 : s 207 = SubexpFlatAdd.encode one) (h211 : s 211 = minusOne.val)
    (h224 : s 224 = counter) (h214 : s 214 = []) (h215 : s 215 = []) :
    SubexpLagrangeInverseCall.InverseReady modulus width counter t a one minusOne s := by
  have ha : s 205 = SubexpQuarticFlatMul.flat a := by simpa only [flat_eq_encode] using h205
  have ho : s 207 = SubexpQuarticFlatMul.flat one := by simpa only [flat_eq_encode] using h207
  intro i
  fin_cases i <;>
    first | exact ha | exact ho | exact h211 | exact h224 | exact h214 | exact h215 |
      exact H _ (by decide)

def encode (p μ : ℕ) (P : List (Coefficient p μ)) : List Bool :=
  SubexpConvolutionEncoding.encodeArray SubexpFlatAdd.encode P

theorem encode_length (p μ : ℕ) (P : List (Coefficient p μ)) :
    (encode p μ P).length = P.length * (4 * baseWidth p μ) :=
  SubexpConvolutionControl.encodeArray_length _ _ (fun a => SubexpFlatAdd.encode_length a) P

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def polynomial (t zero inverse : Coefficient p μ) (D : ℕ)
    (P : List (Coefficient p μ)) : List (Coefficient p μ) :=
  SubexpTruncatedMultiply.result p μ M t zero D P
    (SubexpLocalCorrectionAlgebra.padded zero inverse zero D)

omit [Fact p.Prime] in
@[simp] theorem polynomial_length (t zero inverse : Coefficient p μ) (D : ℕ)
    (P : List (Coefficient p μ)) : (polynomial p μ M t zero inverse D P).length = D :=
  SubexpTruncatedMultiply.result_length p μ M t zero D P _

def scaleStore (s : Store) (bits : List Bool) : Store :=
  Function.update (Function.update (Function.update s 205 []) 214 []) 240 bits

def finalStore (s : Store) (bits : List Bool) : Store :=
  Function.update (Function.update s 205 []) 240 bits

theorem finalStore_frame (s : Store) (bits : List Bool) (i : Fin 256)
    (h205 : i ≠ 205) (h240 : i ≠ 240) : finalStore s bits i = s i := by
  simp only [finalStore, Function.update_of_ne h240, Function.update_of_ne h205]

theorem finalStore_ready {modulus width reduction : List Bool} {B : ℕ} {s : Store}
    (H : Ready modulus width reduction B s) (bits : List Bool) :
    Ready modulus width reduction B (finalStore s bits) :=
  (H.update 205 (by decide) []).update 240 (by decide) bits

/-- The physical post-inversion work, with the actual inverse coefficient
as input. Its padded constant includes exactly D coefficients. -/
theorem scale_run (s : Store) (D : ℕ) (P : List (Coefficient p μ))
    (t zero a inverse : Coefficient p μ) (width : List Bool)
    (hw : width.length = baseWidth p μ)
    (H : Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ) s)
    (hz : SubexpFlatAdd.encode zero = List.replicate (4 * baseWidth p μ) false)
    (h205 : s 205 = SubexpFlatAdd.encode a)
    (h214 : s 214 = SubexpFlatAdd.encode inverse)
    (hP : P.length = D) (h240 : s 240 = encode p μ P)
    (h241 : s 241 = [])
    (h242 : s 242 = encode p μ (List.replicate D zero))
    (h243 : s 243 = List.replicate D true)
    (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn scale (603000 * (D + 1)^3 * (baseWidth p μ + 1)^2) s
      (scaleStore s (encode p μ (polynomial p μ M t zero inverse D P))) := by
  let B := baseWidth p μ
  let Q := SubexpLocalCorrectionAlgebra.padded zero inverse zero D
  let bits := encode p μ (polynomial p μ M t zero inverse D P)
  let s1 := Function.update s 205 []
  let s2 := Function.update s1 100 (SubexpFlatAdd.encode inverse)
  let s3 := Function.update s2 101 (List.replicate (4 * B) false)
  let s4 := Function.update s1 241 (encode p μ Q)
  let s5 := Function.update s4 214 []
  let s6 := Function.update s5 240 bits
  have H1 : Ready M.bits width (SubexpQuarticFlatMul.flat t) B s1 :=
    H.update 205 (by decide) []
  have H4 : Ready M.bits width (SubexpQuarticFlatMul.flat t) B s4 :=
    H1.update 241 (by decide) _
  have H5 : Ready M.bits width (SubexpQuarticFlatMul.flat t) B s5 :=
    H4.update 214 (by decide) []
  have hQ : encode p μ Q = SubexpLinearFactorProgram.paddedBits B
      (SubexpFlatAdd.encode inverse) (List.replicate (4 * B) false) D := by
    simpa only [encode, hz] using
      SubexpLinearFactorEncoding.encode_padded SubexpFlatAdd.encode zero inverse zero B D hz
  have h1 : ExecutesIn (clear 205) (8 * B + 3) s s1 := by
    simpa [s1, h205, SubexpFlatAdd.encode_length, B, ← Nat.mul_assoc] using clear_run 205 s
  have h2 : ExecutesIn (copy 214 100) (28 * B + 5) s1 s2 := by
    simpa [s2, s1, h214, SubexpFlatAdd.encode_length, ← Nat.mul_assoc,
      show s 100 = [] from H 100 (by decide)] using
      copy_run 214 100 s1 (by decide) (by decide) (by decide) (H1 120 (by decide))
  have h3 : ExecutesIn (copy 104 101) (28 * B + 5) s2 s3 := by
    simpa [s3, s2, s1, ← Nat.mul_assoc,
      show s 104 = List.replicate (4 * B) false from H 104 (by decide),
      show s 101 = [] from H 101 (by decide)] using
      copy_run 104 101 s2 (by decide) (by decide) (by decide)
        (by simpa [s2, layout] using H1 120 (by decide))
  have h4 : ExecutesIn (SubexpPolynomialConstructor.constructAtInputs 241)
      (150 * (D + 1) * (B + 1)) s3 s4 := by
    have he := SubexpPolynomialConstructor.constructAtInputs_run s3 241
      (by decide) (by decide) D B (SubexpFlatAdd.encode inverse)
      (List.replicate (4 * B) false)
      (by simp [s3, s2]) (by simp [s3]) (SubexpFlatAdd.encode_length inverse)
      List.length_replicate (by simp [s3, s2, s1, h243])
      (by simpa [s3, s2, layout] using H1 104 (by decide))
      (by simpa [s3, s2, layout] using H1 102 (by decide))
      (by simpa [s3, s2, layout] using H1 107 (by decide))
      (by simpa [s3, s2, layout] using H1 108 (by decide))
      (by simpa [s3, s2, layout] using H1 120 (by decide))
      (by simp [s3, s2, s1, h245]) (by simp [s3, s2, s1, h241])
    have hs : Function.update (Function.update (Function.update s3 100 []) 101 []) 241
        (SubexpLinearFactorProgram.paddedBits B (SubexpFlatAdd.encode inverse)
          (List.replicate (4 * B) false) D) = s4 := by
      rw [← hQ]
      funext j
      by_cases h100 : j = 100
      · subst j; simp [s4, H1 100 (by decide), layout]
      · by_cases h101 : j = 101
        · subst j; simp [s4, H1 101 (by decide), layout]
        · simp [s4, s3, s2, Function.update_apply, h100, h101]
    rwa [hs] at he
  have h5 : ExecutesIn (clear 214) (8 * B + 3) s4 s5 := by
    simpa [s5, s4, s1, h214, SubexpFlatAdd.encode_length, B, ← Nat.mul_assoc] using clear_run 214 s4
  have h6 : ExecutesIn SubexpLagrangeCacheWorkspace.multiply
      (602000 * (D + 1)^3 * (B + 1)^2) s5 s6 := by
    exact SubexpLagrangeCacheWorkspace.multiply_run p μ M s5 t zero width hw H5 D P Q hP
      (SubexpLocalCorrectionAlgebra.padded_length zero inverse zero D)
      (by simpa [s5, s4, s1, encode] using h240) (by simp [s5, s4, encode])
      (by simpa [s5, s4, s1, encode] using h242) (by simp [s5, s4, s1, h243])
      (by simp [s5, s4, s1, h244]) (by simp [s5, s4, s1, h245])
  have hfinal : Function.update s6 241 [] = scaleStore s bits := by
    funext j
    by_cases hj : j = 241
    · subst j; simp [scaleStore, h241]
    · simp [s6, s5, s4, s1, scaleStore, Function.update_apply, hj]
  have h7 : ExecutesIn (clear 241) (8 * D * B + 3) s6 (scaleStore s bits) := by
    have he := clear_run 241 s6
    rw [hfinal] at he
    convert he using 1
    simp [s6, s5, s4, encode_length, Q]
    ring
  have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))
  apply he.mono
  dsimp only [B]
  ring_nf
  omega

def runtimeBound (D B : ℕ) (exponent counter : List Bool) : ℕ :=
  SubexpLagrangeInverseCall.runtimeBound B exponent counter +
    603000 * (D + 1)^3 * (B + 1)^2

/-- Complete physical normalization from the clean cache workspace.
Neither an inverse byte string nor a polynomial result is an input premise. -/
theorem command_correct (hμ : 0 < μ) (d : Data) (D : ℕ)
    (P : List (Coefficient p μ)) (t zero a one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ)) (width exponent counter : List Bool)
    (hw : width.length = baseWidth p μ)
    (H : Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ) d.stacks)
    (hz : SubexpFlatAdd.encode zero = List.replicate (4 * baseWidth p μ) false)
    (h205 : d.stacks 205 = SubexpFlatAdd.encode a)
    (h207 : d.stacks 207 = SubexpFlatAdd.encode one)
    (h211 : d.stacks 211 = minusOne.val) (h224 : d.stacks 224 = counter)
    (h225 : d.stacks 225 = exponent)
    (h214 : d.stacks 214 = []) (h215 : d.stacks 215 = [])
    (h216 : d.stacks 216 = []) (h219 : d.stacks 219 = [])
    (hP : P.length = D) (h240 : d.stacks 240 = encode p μ P)
    (h241 : d.stacks 241 = [])
    (h242 : d.stacks 242 = encode p μ (List.replicate D zero))
    (h243 : d.stacks 243 = List.replicate D true)
    (h244 : d.stacks 244 = []) (h245 : d.stacks 245 = [])
    (ht : t.map (wordValue p μ) = reductionData (QuarticSearch.liftedCoefficients p μ))
    (hu : SubexpLagrangeInverseCall.denote p μ one = 1)
    (hm : wordValue p μ minusOne = -1)
    (he : BinaryArithmetic.toNat exponent = p^4 - 2)
    (hc : CounterPrograms.value counter = μ)
    (ha : SubexpActualRing.rho p μ hμ (SubexpLagrangeInverseCall.denote p μ a) ≠ 0) :
    ∃ n rf inverse, n ≤ runtimeBound D (baseWidth p μ) exponent counter ∧
      Eval command n d ⟨rf, finalStore d.stacks
        (encode p μ (polynomial p μ M t zero inverse D P))⟩ ∧
      SubexpLagrangeInverseCall.denote p μ inverse *
        SubexpLagrangeInverseCall.denote p μ a = 1 ∧
      (polynomial p μ M t zero inverse D P).length = D ∧
      Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ)
        (finalStore d.stacks (encode p μ (polynomial p μ M t zero inverse D P))) := by
  obtain ⟨n, ri, inverse, hn, hi, hv, hlen⟩ :=
    SubexpLagrangeInverseCall.command_correct p μ hμ M t a one minusOne width exponent counter hw d
      (powerReady H h205 h207 h225 h215 h216 h219)
      (inverseReady H h205 h207 h211 h224 h214 h215) ht hu hm he hc ha
  let s1 := Function.update d.stacks 214 (SubexpQuarticFlatMul.flat inverse)
  have H1 : Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ) s1 :=
    H.update 214 (by decide) _
  have hs := scale_run p μ M s1 D P t zero a inverse width hw H1 hz
    (by simp [s1, h205]) (by simp [s1, flat_eq_encode]) hP
    (by simp [s1, h240]) (by simp [s1, h241]) (by simp [s1, h242])
    (by simp [s1, h243]) (by simp [s1, h244]) (by simp [s1, h245])
  obtain ⟨k, rf, hk, hs⟩ := hs ri
  have hfinal : scaleStore s1 (encode p μ (polynomial p μ M t zero inverse D P)) =
      finalStore d.stacks (encode p μ (polynomial p μ M t zero inverse D P)) := by
    funext j
    by_cases hj : j = 214
    · subst j; simp [scaleStore, finalStore, h214]
    · simp [scaleStore, finalStore, s1, Function.update_apply, hj]
  rw [hfinal] at hs
  refine ⟨n + k, rf, inverse, ?_, hi.seq hs, hv,
    polynomial_length p μ M t zero inverse D P, finalStore_ready H _⟩
  exact Nat.add_le_add hn hk

theorem runtimeBound_le (D B W : ℕ) (exponent counter : List Bool)
    (hD : D ≤ W) (hB : B ≤ W) (he : exponent.length ≤ W) (hc : counter.length ≤ W)
    (hpower : BinaryArithmetic.toNat exponent ≤ W) (hcount : CounterPrograms.value counter ≤ W) :
    runtimeBound D B exponent counter ≤ 4000000 * (W + 1)^5 := by
  have hinv := SubexpLagrangeInverseCall.runtimeBound_le B W exponent counter hB he hc hpower hcount
  have h35 : (W + 1)^3 ≤ (W + 1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hs : 603000 * (D + 1)^3 * (B + 1)^2 ≤ 603000 * (W + 1)^5 := by
    calc
      _ ≤ 603000 * (W + 1)^3 * (W + 1)^2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
          (Nat.pow_le_pow_left (by omega) 2)
      _ = _ := by ring
  have hi := hinv.trans (Nat.mul_le_mul_left 3000000 h35)
  unfold runtimeBound
  omega

theorem program_trace {n : ℕ} {d e : Data} (h : Eval command n d e) :
    Trace program (n + 1) (d.withPC (some program.entry)) (e.withPC none) :=
  compiled_halt_trace h 205 240

end SubexponentialSAT.SubexpLagrangeNormalize

end OAI.Algorithms
