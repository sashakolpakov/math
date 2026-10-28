import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl
import OAI.Algorithms.SubexponentialSAT.SubexpLinearFactorCall

namespace OAI.Algorithms

/-! Reusable physical construction of a padded polynomial from two scalar
cells and a cached unary dimension. The native constructor buffers are
cleared on return; an order-preserving move writes the chosen cache slot. -/

namespace SubexponentialSAT.SubexpPolynomialConstructor

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpPolynomialServiceControl (transfer transfer_run)

def move (src dst : Fin 256) : Code := .seq (transfer src 245) (transfer 245 dst)

theorem move_run (s : Store) (src dst : Fin 256)
    (hs : src ≠ 245) (hd : dst ≠ 245) (hsd : src ≠ dst)
    (htmp : s 245 = []) (hout : s dst = []) :
    ExecutesIn (move src dst) (6 * (s src).length + 6) s
      (Function.update (Function.update s src []) dst (s src)) := by
  let middle := Function.update (Function.update s src []) 245 (s src).reverse
  have h₁ : ExecutesIn (transfer src 245) (3 * (s src).length + 3) s middle := by
    simpa [middle, htmp] using transfer_run src 245 s hs
  have he : Function.update (Function.update middle 245 []) dst
      ((middle 245).reverse ++ middle dst) =
      Function.update (Function.update s src []) dst (s src) := by
    funext j
    by_cases hj : j = 245 <;>
      simp [middle, Function.update_apply, hd, Ne.symm hs, Ne.symm hd, Ne.symm hsd, htmp, hout, hj]
  have h₂ : ExecutesIn (transfer 245 dst) (3 * (s src).length + 3) middle
      (Function.update (Function.update s src []) dst (s src)) := by
    have h := transfer_run 245 dst middle (Ne.symm hd)
    rw [he] at h
    simpa [middle] using h
  have h := h₁.seq h₂
  have hcost : (3 * (s src).length + 3) + (3 * (s src).length + 3) =
      6 * (s src).length + 6 := by omega
  simpa only [move, hcost] using h

def constructAtInputs (dst : Fin 256) : Code :=
  .seq (copy 243 108) (.seq SubexpLinearFactorCall.command
    (.seq (clear 100) (.seq (clear 101) (move 102 dst))))

def construct (low high dst : Fin 256) : Code :=
  .seq (copy low 100) (.seq (copy high 101) (constructAtInputs dst))

/-- Low and high scalar inputs are consumed; D and the zero coefficient are
retained. This is the actual tape constructor used for constants and linear
factors, including all native-buffer cleanup and output movement. -/
theorem constructAtInputs_run (s : Store) (dst : Fin 256) (hdst : 205 ≤ dst.val)
    (hdtmp : dst ≠ 245) (D B : ℕ) (low high : List Bool)
    (hlow : s 100 = low) (hhigh : s 101 = high)
    (hllen : low.length = 4 * B) (hhlen : high.length = 4 * B)
    (hD : s 243 = List.replicate D true)
    (hzero : s 104 = List.replicate (4 * B) false)
    (h102 : s 102 = []) (h107 : s 107 = []) (h108 : s 108 = [])
    (h120 : s 120 = []) (h245 : s 245 = []) (hout : s dst = []) :
    ExecutesIn (constructAtInputs dst) (150 * (D + 1) * (B + 1)) s
      (Function.update (Function.update (Function.update s 100 []) 101 []) dst
        (SubexpLinearFactorProgram.paddedBits B low high D)) := by
  have hsmall : ∀ i : Fin 256, i.val < 205 → i ≠ dst := by
    intro i hi he
    subst i
    omega
  have h100 := hsmall 100 (by decide)
  have h101 := hsmall 101 (by decide)
  have h102d := hsmall 102 (by decide)
  let bits := SubexpLinearFactorProgram.paddedBits B low high D
  let s₁ := Function.update s 108 (List.replicate D true)
  let s₂ := Function.update s 102 bits
  let s₃ := Function.update s₂ 100 []
  let s₄ := Function.update s₃ 101 []
  have h₁ : ExecutesIn (copy 243 108) (7 * D + 5) s s₁ := by
    simpa [s₁, hD, h108] using copy_run 243 108 s
      (by decide) (by decide) (by decide) h120
  have he₂ : Function.update (Function.update s₁ 108 []) 102 bits = s₂ := by
    funext j
    by_cases hj : j = 108 <;> simp [s₁, s₂, Function.update_apply, h108, hj]
  have h₂ : ExecutesIn SubexpLinearFactorCall.command
      (101 * (D + 1) * (B + 1)) s₁ s₂ := by
    have h := SubexpLinearFactorCall.command_run s₁ D B low high
      (by simp [s₁, hlow]) (by simp [s₁, hhigh]) hllen hhlen
      (by simp [s₁]) (by simp [s₁, hzero]) (by simp [s₁, h102]) (by simp [s₁, h107])
    rw [he₂] at h
    exact h
  have h₃ : ExecutesIn (clear 100) (8 * B + 3) s₂ s₃ := by
    simpa [s₂, s₃, hlow, hllen, ← Nat.mul_assoc] using clear_run 100 s₂
  have h₄ : ExecutesIn (clear 101) (8 * B + 3) s₃ s₄ := by
    simpa [s₂, s₃, s₄, hhigh, hhlen, ← Nat.mul_assoc] using clear_run 101 s₃
  have he₅ : Function.update (Function.update s₄ 102 []) dst (s₄ 102) =
      Function.update (Function.update (Function.update s 100 []) 101 []) dst bits := by
    funext j
    by_cases hj : j = 102 <;>
      simp [s₂, s₃, s₄, Function.update_apply, hj, h102, h102d ]
  have hbits : bits.length = D * (4 * B) :=
    SubexpLinearFactorProgram.paddedBits_length D B low high hllen hhlen
  have h₅ : ExecutesIn (move 102 dst) (24 * D * B + 6) s₄
      (Function.update (Function.update (Function.update s 100 []) 101 []) dst bits) := by
    have h := move_run s₄ 102 dst (by decide) hdtmp h102d
      (by simp [s₄, s₃, s₂, h245])
      (by simp [s₄, s₃, s₂, Ne.symm h100, Ne.symm h101, Ne.symm h102d, hout])
    rw [he₅] at h
    convert h using 1
    simp [s₄, s₃, s₂, hbits]
    ring
  have h := h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))
  apply h.mono
  ring_nf
  omega

theorem construct_run (s : Store) (low high dst : Fin 256)
    (hl100 : low ≠ 100) (hl120 : low ≠ 120)
    (hh100 : high ≠ 100) (hh101 : high ≠ 101) (hh120 : high ≠ 120)
    (hdst : 205 ≤ dst.val) (hdtmp : dst ≠ 245) (D B : ℕ)
    (hllen : (s low).length = 4 * B) (hhlen : (s high).length = 4 * B)
    (hD : s 243 = List.replicate D true)
    (hzero : s 104 = List.replicate (4 * B) false)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h107 : s 107 = []) (h108 : s 108 = []) (h120 : s 120 = [])
    (h245 : s 245 = []) (hout : s dst = []) :
    ExecutesIn (construct low high dst) (220 * (D + 1) * (B + 1)) s
      (Function.update s dst (SubexpLinearFactorProgram.paddedBits B (s low) (s high) D)) := by
  let s₁ := Function.update s 100 (s low)
  let s₂ := Function.update s₁ 101 (s high)
  have hd100 : dst ≠ 100 := by intro h; subst dst; norm_num [Fin.coe_ofNat_eq_mod] at hdst
  have hd101 : dst ≠ 101 := by intro h; subst dst; norm_num [Fin.coe_ofNat_eq_mod] at hdst
  have h₁ : ExecutesIn (copy low 100) (7 * (s low).length + 5) s s₁ := by
    simpa [s₁, h100] using copy_run low 100 s hl100 hl120 (by decide) h120
  have h₂ : ExecutesIn (copy high 101) (7 * (s high).length + 5) s₁ s₂ := by
    simpa [s₁, s₂, hh100, h101] using copy_run high 101 s₁ hh101 hh120
      (by decide) (by simp [s₁, h120])
  have h₃ := constructAtInputs_run s₂ dst hdst hdtmp D B (s low) (s high)
    (by simp [s₂, s₁]) (by simp [s₂]) hllen hhlen
    (by simp [s₂, s₁, hD]) (by simp [s₂, s₁, hzero])
    (by simp [s₂, s₁, h102]) (by simp [s₂, s₁, h107])
    (by simp [s₂, s₁, h108]) (by simp [s₂, s₁, h120])
    (by simp [s₂, s₁, h245]) (by simp [s₂, s₁, hd100, hd101, hout])
  have he : Function.update (Function.update (Function.update s₂ 100 []) 101 []) dst
      (SubexpLinearFactorProgram.paddedBits B (s low) (s high) D) =
      Function.update s dst (SubexpLinearFactorProgram.paddedBits B (s low) (s high) D) := by
    funext j
    by_cases h100' : j = 100 <;> by_cases h101' : j = 101 <;>
      simp [s₂, s₁, Function.update_apply, h100, h101, h100', h101']
  rw [he] at h₃
  apply (h₁.seq (h₂.seq h₃)).mono
  rw [hllen, hhlen]
  ring_nf
  omega

end SubexponentialSAT.SubexpPolynomialConstructor

end OAI.Algorithms
