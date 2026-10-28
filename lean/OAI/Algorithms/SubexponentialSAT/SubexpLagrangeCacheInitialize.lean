import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheState

namespace OAI.Algorithms

/-! The actual initial scalar and polynomial accumulators of each cache row. -/

namespace SubexponentialSAT.SubexpLagrangeCacheInitialize

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpLagrangeCacheWorkspace
open SubexpLagrangeCacheState

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def initial (D : ℕ) (zero one : Coefficient p μ) : Partial p μ D :=
  ⟨one, SubexpLocalCorrectionAlgebra.padded zero one zero D,
    SubexpLocalCorrectionAlgebra.padded_length zero one zero D⟩

omit [Fact p.Prime] in
theorem initialize_run (s : Store) (D : ℕ) (t zero one : Coefficient p μ)
    (width : List Bool)
    (H : Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ) s)
    (hz : SubexpFlatAdd.encode zero = List.replicate (4 * baseWidth p μ) false)
    (h207 : s 207 = SubexpFlatAdd.encode one)
    (h213 : s 213 = SubexpFlatAdd.encode zero)
    (h243 : s 243 = List.replicate D true)
    (h205 : s 205 = []) (h218 : s 218 = []) (h240 : s 240 = [])
    (h245 : s 245 = []) (h247 : s 247 = []) (h249 : s 249 = []) :
    ExecutesIn SubexpLagrangeCacheControl.initializeRow
      (300 * (D + 1) * (baseWidth p μ + 1)) s
      (view p μ M D s zero one 0 (initial p μ D zero one) (List.replicate D true)) := by
  let B := baseWidth p μ
  let P := (initial p μ D zero one).polynomial
  let s1 := Function.update s 205 (SubexpFlatAdd.encode one)
  let s2 := Function.update s1 240 (encode p μ P)
  let s3 := Function.update s2 218 (SubexpFlatAdd.encode zero)
  let s4 := Function.update s3 247 (List.replicate D true)
  have H1 : Ready M.bits width (SubexpQuarticFlatMul.flat t) B s1 :=
    H.update 205 (by decide) _
  have h1 : ExecutesIn (copy 207 205) (28 * B + 5) s s1 := by
    simpa [s1, h205, h207, SubexpFlatAdd.encode_length, ← Nat.mul_assoc] using
      copy_run 207 205 s (by decide) (by decide) (by decide) (H 120 (by decide))
  have hp : encode p μ P = SubexpLinearFactorProgram.paddedBits B
      (SubexpFlatAdd.encode one) (List.replicate (4 * B) false) D := by
    simpa only [P, initial, encode, hz] using
      SubexpLinearFactorEncoding.encode_padded SubexpFlatAdd.encode zero one zero B D hz
  have h2 : ExecutesIn (SubexpPolynomialConstructor.construct 207 104 240)
      (220 * (D + 1) * (B + 1)) s1 s2 := by
    have he := SubexpPolynomialConstructor.construct_run s1 207 104 240
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) D B
      (by simp [s1, h207, SubexpFlatAdd.encode_length, B])
      (by rw [H1 104 (by decide)]; exact List.length_replicate)
      (by simp [s1, h243]) (H1 104 (by decide)) (H1 100 (by decide))
      (H1 101 (by decide)) (H1 102 (by decide)) (H1 107 (by decide))
      (H1 108 (by decide)) (H1 120 (by decide))
      (by simp [s1, h245]) (by simp [s1, h240])
    simpa only [s2, hp, show s1 207 = SubexpFlatAdd.encode one from by simp [s1, h207],
      show s1 104 = List.replicate (4 * B) false from H1 104 (by decide)] using he
  have h3 : ExecutesIn (copy 213 218) (28 * B + 5) s2 s3 := by
    simpa [s3, s2, s1, h213, h218, SubexpFlatAdd.encode_length, ← Nat.mul_assoc] using
      copy_run 213 218 s2 (by decide) (by decide) (by decide)
        (by simpa [s2, s1, layout] using H 120 (by decide))
  have h4 : ExecutesIn (copy 243 247) (7 * D + 5) s3 s4 := by
    simpa [s4, s3, s2, s1, h243, h247] using
      copy_run 243 247 s3 (by decide) (by decide) (by decide)
        (by simpa [s3, s2, s1, layout] using H 120 (by decide))
  have hs : s4 = view p μ M D s zero one 0 (initial p μ D zero one) (List.replicate D true) := by
    funext k
    by_cases h : k = 249
    · subst k
      simp [s4, s3, s2, s1, view, h249]
    · by_cases h218k : k = 218
      · subst k; simp [s4, s3, s2, s1, view, initial, label]
      · by_cases h240k : k = 240
        · subst k; simp [s4, s3, s2, s1, view, initial, label, P]
        · simp [s4, s3, s2, s1, view, Function.update_apply,
            initial, label, P, h, h218k, h240k]
  rw [hs] at h4
  have he := h1.seq (h2.seq (h3.seq h4))
  apply he.mono
  dsimp only [B]
  ring_nf
  omega

end SubexponentialSAT.SubexpLagrangeCacheInitialize

end OAI.Algorithms
