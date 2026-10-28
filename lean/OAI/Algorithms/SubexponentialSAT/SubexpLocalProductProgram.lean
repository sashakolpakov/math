import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalLinearFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialPowerProgram

namespace OAI.Algorithms

/-! One concrete included-node iteration of the local cofactor product.
It builds the shifted factor from actual scalar inputs, then executes D
truncated multiplications and restores the factor cache and loop counter.
-/

namespace SubexponentialSAT.SubexpLocalProductProgram

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpPolynomialPowerProgram

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def command : Code := SubexpLocalLinearFactorProgram.command ;;
  copy 243 246 ;; SubexpPolynomialPowerProgram.command ;; clear 241

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def factor (minusOne : Word (baseWidth p μ))
    (zero theta c one : Coefficient p μ) (D : ℕ) : FixedPolynomial p μ D :=
  ⟨SubexpLocalLinearFactorProgram.factor p μ M minusOne zero theta c one D,
    SubexpLocalLinearFactorProgram.factor_length p μ M minusOne zero theta c one D⟩

def value (t zero theta c one : Coefficient p μ) (minusOne : Word (baseWidth p μ))
    {D : ℕ} (P : FixedPolynomial p μ D) : FixedPolynomial p μ D :=
  ((next p μ M t zero (factor p μ M minusOne zero theta c one D))^[D]) P

theorem command_value (s : Store) (D : ℕ) (P : FixedPolynomial p μ D)
    (t zero theta c one : Coefficient p μ) (minusOne : Word (baseWidth p μ))
    (width : List Bool) (frame : Fin 6 → List Bool)
    (hw : width.length = baseWidth p μ)
    (hneg : ∀ i, s (SubexpLocalLinearFactorProgram.negatePorts i) =
      SubexpQuarticFlatNeg.initialStore c minusOne M.bits width i)
    (hadd : ∀ i, s (SubexpLocalLinearFactorProgram.addPorts i) =
      (SubexpFlatAdd.ready (fun _ => false) M.bits [] [] width [] frame).stacks i)
    (H : SubexpConvolutionPairSpec.BaseReady p μ M s t width frame)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h107 : s 107 = []) (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = [])
    (h241 : s 241 = [])
    (htheta : s 213 = SubexpFlatAdd.encode theta)
    (hone : s 207 = SubexpFlatAdd.encode one)
    (hD : s 243 = List.replicate D true)
    (hzero : s 104 = List.replicate (4 * baseWidth p μ) false)
    (hz : SubexpFlatAdd.encode zero = List.replicate (4 * baseWidth p μ) false)
    (hzeroArray : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D zero))
    (hleft : s 240 = encode p μ P) :
    ExecutesIn command (700000 * (D + 1)^4 * (baseWidth p μ + 1)^2) s
      (Function.update (Function.update s 219
        (SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.negative p μ M minusOne c)))
        240 (encode p μ (value p μ M t zero theta c one minusOne P))) := by
  let B := baseWidth p μ
  let neg := SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.negative p μ M minusOne c)
  let Q := factor p μ M minusOne zero theta c one D
  let P' := value p μ M t zero theta c one minusOne P
  let s₁ := Function.update (Function.update s 219 neg) 241 (encode p μ Q)
  let s₂ := Function.update s₁ 246 (List.replicate D true)
  let s₃ := Function.update s₁ 240 (encode p μ P')
  have hQ : encode p μ Q = SubexpLinearFactorProgram.paddedBits B
      (SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.difference p μ M minusOne theta c))
      (SubexpFlatAdd.encode one) D := by
    exact SubexpLocalLinearFactorProgram.factor_encode p μ M minusOne zero theta c one D hz
  have h₁ : ExecutesIn SubexpLocalLinearFactorProgram.command
      (51000 * (D + 1) * (B + 1)^2) s s₁ := by
    rw [show s₁ = Function.update (Function.update s 219 neg) 241 (encode p μ Q) from rfl, hQ]
    exact SubexpLocalLinearFactorProgram.command_run p μ M s D theta c one minusOne width frame
      hw hneg hadd htheta hone hD hzero (hempty 0) (hempty 1) (hempty 2)
      h107 (hempty 6) h120 h241 h245
  have h₂ : ExecutesIn (copy 243 246) (7 * D + 5) s₁ s₂ := by
    simpa [s₁, s₂, hD, h246] using copy_run 243 246 s₁
      (by decide) (by decide) (by decide) (by simp [s₁, h120])
  have below : ∀ j : Fin 256, j.val < 205 → s₁ j = s j := by
    intro j hj
    have h219 : j ≠ 219 := by intro h; subst j; norm_num [Fin.coe_ofNat_eq_mod] at hj
    have h241' : j ≠ 241 := by intro h; subst j; norm_num [Fin.coe_ofNat_eq_mod] at hj
    simp [s₁, h219, h241']
  have ready_in : SubexpPolynomialIterationControl.ready s₁ (encode p μ) P
      (List.replicate D true) = s₂ := by
    have hcurrent : s₁ 240 = encode p μ P := by simp [s₁, hleft]
    simp [SubexpPolynomialIterationControl.ready, s₂, ← hcurrent]
  have ready_out : SubexpPolynomialIterationControl.ready s₁ (encode p μ) P' [] = s₃ := by
    funext j
    by_cases hj : j = 246 <;>
      simp [SubexpPolynomialIterationControl.ready, s₃, s₁, hj, h246, Function.update_apply]
  have h₃ : ExecutesIn SubexpPolynomialPowerProgram.command
      (D * (602000 * (D + 1)^3 * (B + 1)^2 + 2) + 2) s₂ s₃ := by
    have h := SubexpPolynomialPowerProgram.command_value p μ M s₁ t zero width frame
      (baseReady_congr p μ M s s₁ t width frame below H)
      (fun i => by rw [below _ (bufferPorts_lt i)]; exact hempty i)
      (by rw [below 120 (by decide)]; exact h120)
      (by rw [below 121 (by decide)]; exact h121)
      (by rw [below 122 (by decide)]; exact h122)
      (by simp [s₁, h244]) (by simp [s₁, h245]) D P Q
      (by simp [s₁]) (by simp [s₁, hzeroArray])
      (by simp [s₁, hD]) (List.replicate D true)
    simp only [List.length_replicate] at h
    change ExecutesIn _ _ _
      (SubexpPolynomialIterationControl.ready s₁ (encode p μ) P' []) at h
    rw [ready_in, ready_out] at h
    simpa only [List.length_replicate] using h
  have hfinal : Function.update s₃ 241 [] =
      Function.update (Function.update s 219 neg) 240 (encode p μ P') := by
    funext j
    by_cases hj : j = 241 <;> simp [s₃, s₁, hj, h241, Function.update_apply]
  have h₄ : ExecutesIn (clear 241) (8 * D * B + 3) s₃
      (Function.update (Function.update s 219 neg) 240 (encode p μ P')) := by
    have h := clear_run 241 s₃
    rw [hfinal] at h
    convert h using 1
    simp [s₃, s₁, SubexpPolynomialPowerProgram.encode_length]
    ring
  have h := h₁.seq (h₂.seq (h₃.seq h₄))
  apply h.mono
  dsimp only [B]
  ring_nf
  omega

end SubexponentialSAT.SubexpLocalProductProgram

end OAI.Algorithms
