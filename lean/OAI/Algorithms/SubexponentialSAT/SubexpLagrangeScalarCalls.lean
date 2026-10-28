import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalLinearFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionPair

namespace OAI.Algorithms

/-! Preserving arithmetic calls for the Lagrange-cache controller. The
operands and destination are high cache ports; the low native workspaces
are restored by real clear and move operations. -/

namespace SubexponentialSAT.SubexpLagrangeScalarCalls

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing
open SubexpLocalLinearFactorProgram (registers addPorts)

abbrev Store := Fin 256 → List Bool
abbrev Code := Cmd 16 256

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def addTo (left right dst : Fin 256) : Code :=
  copy left 8 ;; copy right 9 ;; SubexpLocalLinearFactorProgram.scalarAdd ;;
    clear dst ;; SubexpPolynomialConstructor.move 8 dst

def multiplyTo (left right dst : Fin 256) : Code :=
  copy left 198 ;; copy right 199 ;; SubexpConvolutionPair.multiply ;;
    clear dst ;; SubexpPolynomialConstructor.move 200 dst

private theorem high_ne (i j : Fin 256) (hi : 205 ≤ i.val) (hj : j.val < 205) : i ≠ j := by
  intro h
  subst i
  omega

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem addTo_run (s : Store) (left right dst : Fin 256)
    (hl : 205 ≤ left.val) (hr : 205 ≤ right.val) (hd : 205 ≤ dst.val)
    (hdd : dst ≠ 245)
    (a b : Quad (Word (baseWidth p μ))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hw : width.length = baseWidth p μ)
    (ha : s left = SubexpFlatAdd.encode a) (hb : s right = SubexpFlatAdd.encode b)
    (hbase : ∀ i, s (addPorts i) =
      (SubexpFlatAdd.ready (fun _ => false) M.bits [] [] width [] frame).stacks i)
    (h120 : s 120 = []) (h245 : s 245 = []) :
    ExecutesIn (addTo left right dst)
      (26000 * (baseWidth p μ + 1)^2 + 2 * (s dst).length) s
      (Function.update s dst
        (SubexpFlatAdd.encode (SubexpPreparedQuartic.binaryAdd p μ M a b).1)) := by
  let B := baseWidth p μ
  let out := SubexpFlatAdd.encode (SubexpPreparedQuartic.binaryAdd p μ M a b).1
  let s1 := Function.update s 8 (SubexpFlatAdd.encode a)
  let s2 := Function.update s1 9 (SubexpFlatAdd.encode b)
  let s3 := Function.update s 8 out
  let s4 := Function.update s3 dst []
  have h8 : s 8 = [] := by
    have h := hbase (8 : Fin 20)
    change s 8 = [] at h
    exact h
  have h9 : s 9 = [] := by
    have h := hbase (9 : Fin 20)
    change s 9 = [] at h
    exact h
  have hl8 := high_ne left 8 hl (by decide)
  have hl120 := high_ne left 120 hl (by decide)
  have hr8 := high_ne right 8 hr (by decide)
  have hr9 := high_ne right 9 hr (by decide)
  have hr120 := high_ne right 120 hr (by decide)
  have hd8 := high_ne dst 8 hd (by decide)
  have hd9 := high_ne dst 9 hd (by decide)
  have h1 : ExecutesIn (copy left 8) (28 * B + 5) s s1 := by
    simpa [s1, ha, h8, SubexpFlatAdd.encode_length, B, ← Nat.mul_assoc] using
      copy_run left 8 s hl8 hl120 (by decide) h120
  have h2 : ExecutesIn (copy right 9) (28 * B + 5) s1 s2 := by
    simpa [s1, s2, hb, h9, hr8, SubexpFlatAdd.encode_length, B, ← Nat.mul_assoc] using
      copy_run right 9 s1 hr9 hr120 (by decide) (by simp [s1, h120])
  have hready : ∀ i, s2 (addPorts i) =
      (SubexpFlatAdd.ready (fun _ => false) M.bits
        (SubexpFlatAdd.encode a) (SubexpFlatAdd.encode b) width [] frame).stacks i := by
    intro i
    have hi := hbase i
    fin_cases i <;>
      simp [s2, s1, addPorts, SubexpFlatAdd.ready, SubexpFlatAdd.state,
        SubexpFlatAdd.stacks, Fin.addCases, Fin.coe_ofNat_eq_mod] at hi ⊢ <;> assumption
  have h3 : ExecutesIn SubexpLocalLinearFactorProgram.scalarAdd
      (25000 * (B + 1)^2) s2 s3 := by
    intro regs
    obtain ⟨n, rf, hn, he⟩ := SubexpFlatAddCall.callAt_eval registers addPorts
      p μ M a b width hw (⟨regs, s2⟩ : Data) frame hready
    have hs : SubexpFlatAddCall.resultStacks addPorts out s2 = s3 := by
      funext j
      by_cases hj9 : j = 9
      · subst j; simp [SubexpFlatAddCall.resultStacks, addPorts, s3, h9]
      · by_cases hj8 : j = 8
        · subst j; simp [SubexpFlatAddCall.resultStacks, addPorts, s3, s2, s1]
        · simp [SubexpFlatAddCall.resultStacks, addPorts, s3, s2, s1, hj9, hj8]
    rw [hs] at he
    exact ⟨n, _, hn, he⟩
  have h4 : ExecutesIn (clear dst) (2 * (s dst).length + 3) s3 s4 := by
    simpa [s4, s3, hd8] using clear_run dst s3
  have h5 := SubexpPolynomialConstructor.move_run s4 8 dst (by decide) hdd
    (Ne.symm hd8) (by simp [s4, s3, Ne.symm hdd, h245]) (by simp [s4])
  have hs5 : Function.update (Function.update s4 8 []) dst (s4 8) =
      Function.update s dst out := by
    funext j
    by_cases hj : j = dst
    · subst j; simp [s4, s3, Ne.symm hd8]
    · by_cases hj8 : j = 8
      · subst j; simp [s4, s3, h8, Ne.symm hd8]
      · simp [s4, s3, hj, hj8, Ne.symm hd8]
  rw [hs5] at h5
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  apply h.mono
  have hout : out.length = 4 * B := SubexpFlatAdd.encode_length _
  simp only [s4, Function.update_of_ne (Ne.symm hd8), s3, Function.update_self,
    hout]
  dsimp only [B]
  ring_nf
  omega

theorem multiplyTo_run (s : Store) (left right dst : Fin 256)
    (hl : 205 ≤ left.val) (hr : 205 ≤ right.val) (hd : 205 ≤ dst.val)
    (hdd : dst ≠ 245)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ)
    (ha : s left = SubexpQuarticFlatMul.flat a) (hb : s right = SubexpQuarticFlatMul.flat b)
    (hbase : ∀ i, s (SubexpConvolutionPair.highPort i) =
      SubexpQuarticFlatMul.bankStore (fun _ => []) M.bits (SubexpQuarticFlatMul.flat t) width [] i)
    (h120 : s 120 = []) (h245 : s 245 = []) :
    ExecutesIn (multiplyTo left right dst)
      (401000 * (baseWidth p μ + 1)^2 + 2 * (s dst).length) s
      (Function.update s dst
        (SubexpQuarticFlatMul.flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1)) := by
  let B := baseWidth p μ
  let out := SubexpQuarticFlatMul.flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1
  let s1 := Function.update s 198 (SubexpQuarticFlatMul.flat a)
  let s2 := Function.update s1 199 (SubexpQuarticFlatMul.flat b)
  let s3 := Function.update s 200 out
  let s4 := Function.update s3 dst []
  have h198 : s 198 = [] := by simpa [SubexpConvolutionPair.highPort,
    SubexpQuarticFlatMul.bankStore] using hbase 70
  have h199 : s 199 = [] := by simpa [SubexpConvolutionPair.highPort,
    SubexpQuarticFlatMul.bankStore] using hbase 71
  have h200 : s 200 = [] := by simpa [SubexpConvolutionPair.highPort] using hbase 72
  have hl198 := high_ne left 198 hl (by decide)
  have hl120 := high_ne left 120 hl (by decide)
  have hr198 := high_ne right 198 hr (by decide)
  have hr199 := high_ne right 199 hr (by decide)
  have hr120 := high_ne right 120 hr (by decide)
  have hd198 := high_ne dst 198 hd (by decide)
  have hd199 := high_ne dst 199 hd (by decide)
  have hd200 := high_ne dst 200 hd (by decide)
  have h1 : ExecutesIn (copy left 198) (28 * B + 5) s s1 := by
    simpa [s1, ha, h198, SubexpQuarticFlatMul.flat_length, B, ← Nat.mul_assoc] using
      copy_run left 198 s hl198 hl120 (by decide) h120
  have h2 : ExecutesIn (copy right 199) (28 * B + 5) s1 s2 := by
    simpa [s1, s2, hb, h199, hr198, SubexpQuarticFlatMul.flat_length, B, ← Nat.mul_assoc] using
      copy_run right 199 s1 hr199 hr120 (by decide) (by simp [s1, h120])
  have hready : ∀ i, s2 (SubexpConvolutionPair.highPort i) =
      SubexpQuarticFlatMul.initialStore M.bits width t a b i := by
    intro i
    have h70 : SubexpConvolutionPair.highPort i = 198 ↔ i = 70 := by
      simp only [SubexpConvolutionPair.highPort, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
      omega
    have h71 : SubexpConvolutionPair.highPort i = 199 ↔ i = 71 := by
      simp only [SubexpConvolutionPair.highPort, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
      omega
    simp only [s2, s1, Function.update_apply, h70, h71,
      SubexpQuarticFlatMul.initialStore, hbase]
  have h3 : ExecutesIn SubexpConvolutionPair.multiply (400000 * (B + 1)^2) s2 s3 := by
    intro regs
    obtain ⟨n, rf, hn, he⟩ := SubexpConvolutionPair.multiply_eval p μ M
      (⟨regs, s2⟩ : Data) t a b width hw hready
    have hs : (SubexpConvolutionPair.mulOut (⟨regs, s2⟩ : Data) rf
        (SubexpPreparedQuartic.binaryMul p μ M t a b).1).stacks = s3 := by
      change Function.update (Function.update (Function.update s2 198 []) 199 []) 200 out = s3
      funext j
      by_cases hj198 : j = 198
      · subst j; simp [s3, h198]
      · by_cases hj199 : j = 199
        · subst j; simp [s3, h199]
        · by_cases hj200 : j = 200
          · subst j; simp [s3]
          · simp [s3, s2, s1, hj198, hj199, hj200]
    have heq : SubexpConvolutionPair.mulOut (⟨regs, s2⟩ : Data) rf
        (SubexpPreparedQuartic.binaryMul p μ M t a b).1 =
        (⟨SubexpConvolutionPair.replaceRegs (⟨regs, s2⟩ : Data) rf, s3⟩ : Data) :=
      congrArg (StructuredProgram.State.mk _) hs
    rw [heq] at he
    exact ⟨n, _, hn, he⟩
  have h4 : ExecutesIn (clear dst) (2 * (s dst).length + 3) s3 s4 := by
    simpa [s4, s3, hd200] using clear_run dst s3
  have h5 := SubexpPolynomialConstructor.move_run s4 200 dst (by decide) hdd
    (Ne.symm hd200) (by simp [s4, s3, Ne.symm hdd, h245]) (by simp [s4])
  have hs5 : Function.update (Function.update s4 200 []) dst (s4 200) =
      Function.update s dst out := by
    funext j
    by_cases hj : j = dst
    · subst j; simp [s4, s3, Ne.symm hd200]
    · by_cases hj200 : j = 200
      · subst j; simp [s4, s3, h200, Ne.symm hd200]
      · simp [s4, s3, hj, hj200, Ne.symm hd200]
  rw [hs5] at h5
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  apply h.mono
  have hout : out.length = 4 * B := SubexpQuarticFlatMul.flat_length _
  simp only [s4, Function.update_of_ne (Ne.symm hd200), s3, Function.update_self,
    hout]
  dsimp only [B]
  ring_nf
  omega

end SubexponentialSAT.SubexpLagrangeScalarCalls

end OAI.Algorithms
