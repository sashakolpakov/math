import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheControl
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheWorkspace

namespace OAI.Algorithms

/-! One fully implemented off-diagonal Lagrange-product iteration. -/

namespace SubexponentialSAT.SubexpLagrangeCacheProduct

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpLagrangeCacheWorkspace

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

abbrev Coefficient := Quad (Word (baseWidth p μ))

def neg (minusOne : Word (baseWidth p μ)) (j : Coefficient p μ) : Coefficient p μ :=
  SubexpQuarticNegMachine.negateWords p μ M minusOne j

def difference (minusOne : Word (baseWidth p μ)) (i j : Coefficient p μ) : Coefficient p μ :=
  (SubexpPreparedQuartic.binaryAdd p μ M i (neg p μ M minusOne j)).1

def factor (minusOne : Word (baseWidth p μ)) (z j one : Coefficient p μ) (D : ℕ) :=
  SubexpLocalLinearFactorProgram.factor p μ M minusOne z z j one D

def denominator (t : Coefficient p μ) (minusOne : Word (baseWidth p μ))
    (a i j : Coefficient p μ) : Coefficient p μ :=
  (SubexpPreparedQuartic.binaryMul p μ M t a (difference p μ M minusOne i j)).1

def polynomial (t z one : Coefficient p μ) (minusOne : Word (baseWidth p μ))
    (j : Coefficient p μ) (D : ℕ) (P : List (Coefficient p μ)) :=
  SubexpTruncatedMultiply.result p μ M t z D P (factor p μ M minusOne z j one D)

abbrev encode := @SubexpConvolutionEncoding.encodeArray (Coefficient p μ) SubexpFlatAdd.encode

theorem product_run (s : Store) (D : ℕ) (t z one a i j : Coefficient p μ)
    (minusOne : Word (baseWidth p μ)) (width : List Bool)
    (hw : width.length = baseWidth p μ)
    (H : Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ) s)
    (hz : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p μ) false)
    (h205 : s 205 = SubexpFlatAdd.encode a)
    (h207 : s 207 = SubexpFlatAdd.encode one)
    (h211 : s 211 = minusOne.val) (h213 : s 213 = SubexpFlatAdd.encode z)
    (h217 : s 217 = SubexpFlatAdd.encode i) (h218 : s 218 = SubexpFlatAdd.encode j)
    (P : List (Coefficient p μ)) (hP : P.length = D)
    (h240 : s 240 = encode p μ P)
    (h242 : s 242 = encode p μ (List.replicate D z))
    (h243 : s 243 = List.replicate D true)
    (h214 : s 214 = []) (h219 : s 219 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn SubexpLagrangeCacheControl.innerProduct
      (2000000 * (D + 1)^3 * (baseWidth p μ + 1)^2) s
      (Function.update (Function.update s 205
        (SubexpFlatAdd.encode (denominator p μ M t minusOne a i j))) 240
        (encode p μ (polynomial p μ M t z one minusOne j D P))) := by
  let B := baseWidth p μ
  let negative := neg p μ M minusOne j
  let delta := difference p μ M minusOne i j
  let Q := factor p μ M minusOne z j one D
  let den := denominator p μ M t minusOne a i j
  let R := polynomial p μ M t z one minusOne j D P
  let s1 := Function.update (Function.update s 219 (SubexpFlatAdd.encode negative)) 241 (encode p μ Q)
  let s2 := Function.update s1 214 (SubexpFlatAdd.encode delta)
  let s3 := Function.update s2 205 (SubexpFlatAdd.encode den)
  let s4 := Function.update s1 205 (SubexpFlatAdd.encode den)
  let s5 := Function.update s4 240 (encode p μ R)
  let s6 := Function.update s5 241 []
  have H1 : Ready M.bits width (SubexpQuarticFlatMul.flat t) B s1 :=
    (H.update 219 (by decide) _).update 241 (by decide) _
  have H2 : Ready M.bits width (SubexpQuarticFlatMul.flat t) B s2 :=
    H1.update 214 (by decide) _
  have H4 : Ready M.bits width (SubexpQuarticFlatMul.flat t) B s4 :=
    H1.update 205 (by decide) _
  have hQ : Q.length = D := SubexpLocalLinearFactorProgram.factor_length p μ M _ _ _ _ _ _
  have encQ : encode p μ Q =
      SubexpLinearFactorProgram.paddedBits B
        (SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.difference p μ M minusOne z j))
        (SubexpFlatAdd.encode one) D :=
    SubexpLocalLinearFactorProgram.factor_encode p μ M minusOne z z j one D hz
  have h1 : ExecutesIn SubexpLocalLinearFactorProgram.command
      (51000 * (D + 1) * (B + 1)^2) s s1 := by
    have he := SubexpLocalLinearFactorProgram.command_run p μ M s D z j one minusOne width
      (fun _ => []) hw (Ready.negative p μ M H h211 h218 h219) H.low h213 h207 h243
      (H 104 (by decide)) (H 100 (by decide)) (H 101 (by decide))
      (H 102 (by decide)) (H 107 (by decide)) (H 108 (by decide))
      (H 120 (by decide)) h241 h245
    simpa only [s1, encQ, negative, neg, SubexpLocalLinearFactorProgram.negative] using he
  have h2 : ExecutesIn (SubexpLagrangeScalarCalls.addTo 217 219 214)
      (26000 * (B + 1)^2) s1 s2 := by
    have he := SubexpLagrangeScalarCalls.addTo_run p μ M s1 217 219 214
      (by decide) (by decide) (by decide) (by decide)
      i negative width (fun _ => []) hw
      (by simp [s1, h217]) (by simp [s1]) H1.low
      (H1 120 (by decide)) (by simp [s1, h245])
    simpa [s2, s1, h214, delta, difference, negative, neg] using he
  have h3 : ExecutesIn (SubexpLagrangeScalarCalls.multiplyTo 205 214 205)
      (401000 * (B + 1)^2 + 8 * B) s2 s3 := by
    have he := SubexpLagrangeScalarCalls.multiplyTo_run p μ M s2 205 214 205
      (by decide) (by decide) (by decide) (by decide) t a delta width hw
      (by simp [s2, s1, h205, SubexpConvolutionPair.flat_eq_encode])
      (by simp [s2, SubexpConvolutionPair.flat_eq_encode]) H2.high
      (H2 120 (by decide)) (by simp [s2, s1, h245])
    simpa [s3, s2, s1, h205, SubexpConvolutionPair.flat_eq_encode,
      SubexpFlatAdd.encode_length, den, denominator, delta, B, ← Nat.mul_assoc] using he
  have hs4 : Function.update s3 214 [] = s4 := by
    funext u
    by_cases hu : u = 214
    · subst u; simp [s4, s1, h214]
    · by_cases h205u : u = 205
      · subst u; simp [s4, s3]
      · simp [s4, s3, s2, hu, h205u]
  have h4 : ExecutesIn (clear 214) (8 * B + 3) s3 s4 := by
    have he := clear_run 214 s3
    rw [hs4] at he
    simpa [s3, s2, SubexpFlatAdd.encode_length, B, ← Nat.mul_assoc] using he
  have h5 : ExecutesIn SubexpLagrangeCacheWorkspace.multiply
      (602000 * (D + 1)^3 * (B + 1)^2) s4 s5 := by
    apply SubexpLagrangeCacheWorkspace.multiply_run p μ M s4 t z width hw H4 D P Q hP hQ
    · simp [s4, s1, h240]
    · simp [s4, s1]
    · simp [s4, s1, h242]
    · simp [s4, s1, h243]
    · simp [s4, s1, h244]
    · simp [s4, s1, h245]
  have hlen (xs : List (Coefficient p μ)) :
      (encode p μ xs).length = xs.length * (4 * B) :=
    SubexpConvolutionControl.encodeArray_length _ _ (fun x => SubexpFlatAdd.encode_length x) xs
  have h6 : ExecutesIn (clear 241) (8 * D * B + 3) s5 s6 := by
    have he := clear_run 241 s5
    have hc : 2 * (s5 241).length + 3 = 8 * D * B + 3 := by
      simp only [s5, s4, s1, Function.update_of_ne (by decide : (241 : Fin 256) ≠ 240),
        Function.update_of_ne (by decide : (241 : Fin 256) ≠ 205),
        Function.update_same, hlen, hQ]
      ring
    rw [hc] at he
    exact he
  have hs7 : Function.update s6 219 [] =
      Function.update (Function.update s 205 (SubexpFlatAdd.encode den)) 240 (encode p μ R) := by
    funext u
    by_cases h219u : u = 219
    · subst u; simp [h219]
    · by_cases h241u : u = 241
      · subst u; simp [s6, s5, s4, s1, h241]
      · by_cases h205u : u = 205
        · subst u; simp [s6, s5, s4, s1]
        · by_cases h240u : u = 240
          · subst u; simp [s6, s5, s4, s1]
          · simp [s6, s5, s4, s1, h219u, h241u, h205u, h240u]
  have h7 : ExecutesIn (clear 219) (8 * B + 3) s6
      (Function.update (Function.update s 205 (SubexpFlatAdd.encode den)) 240 (encode p μ R)) := by
    have he := clear_run 219 s6
    rw [hs7] at he
    simpa [s6, s5, s4, s1, SubexpFlatAdd.encode_length, B, ← Nat.mul_assoc] using he
  have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))
  apply he.mono
  dsimp only [B]
  ring_nf
  omega

end SubexponentialSAT.SubexpLagrangeCacheProduct

end OAI.Algorithms
