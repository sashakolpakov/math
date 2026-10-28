import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionStore

namespace OAI.Algorithms

/-! Physical marshalling for a reusable truncated-product service. Cached
operands, a zero array, and the unary dimension occupy 240--243. The native
convolution buffers are restored after each invocation and the result goes
to 244. All copying, clearing, and reversal is performed by fixed programs. -/

namespace SubexponentialSAT.SubexpPolynomialServiceControl

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpConvolutionControl

def prepare : Code :=
  .seq (copy 240 100) (.seq (copy 241 101) (.seq (copy 242 102) (copy 243 106)))

def transfer (src dst : Fin 256) : Code :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 16) 1)

def finish : Code :=
  .seq (clear 101) (.seq (transfer 102 245) (transfer 245 244))

def command (multiply : Code) : Code := .seq prepare (.seq multiply finish)

def prepared (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update s
    100 (s 240)) 101 (s 241)) 102 (s 242)) 106 (s 243)

def multiplied (s : Store) (out : List Bool) : Store :=
  Function.update (Function.update s 101 (s 241)) 102 out

theorem prepare_run (s : Store)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h106 : s 106 = []) (h120 : s 120 = []) :
    ExecutesIn prepare
      (7 * ((s 240).length + (s 241).length + (s 242).length + (s 243).length) + 20)
      s (prepared s) := by
  let s₁ := Function.update s 100 (s 240)
  let s₂ := Function.update s₁ 101 (s 241)
  let s₃ := Function.update s₂ 102 (s 242)
  have h₁ : ExecutesIn (copy 240 100) (7 * (s 240).length + 5) s s₁ := by
    simpa [s₁, h100] using copy_run 240 100 s (by decide) (by decide) (by decide) h120
  have h₂ : ExecutesIn (copy 241 101) (7 * (s 241).length + 5) s₁ s₂ := by
    simpa [s₁, s₂, h101] using copy_run 241 101 s₁
      (by decide) (by decide) (by decide) (by simp [s₁, h120])
  have h₃ : ExecutesIn (copy 242 102) (7 * (s 242).length + 5) s₂ s₃ := by
    simpa [s₁, s₂, s₃, h102] using copy_run 242 102 s₂
      (by decide) (by decide) (by decide) (by simp [s₂, s₁, h120])
  have h₄ : ExecutesIn (copy 243 106) (7 * (s 243).length + 5) s₃ (prepared s) := by
    simpa [s₁, s₂, s₃, prepared, h106] using copy_run 243 106 s₃
      (by decide) (by decide) (by decide) (by simp [s₃, s₂, s₁, h120])
  have h := h₁.seq (h₂.seq (h₃.seq h₄))
  convert h using 1
  · rfl
  · ring

theorem transfer_run (src dst : Fin 256) (s : Store) (hne : src ≠ dst) :
    ExecutesIn (transfer src dst) (3 * (s src).length + 3) s
      (Function.update (Function.update s src []) dst ((s src).reverse ++ s dst)) := by
  intro regs
  refine ⟨_, readRegs regs 0 1 none, le_rfl, ?_⟩
  simpa [transfer, afterTransfer, StackRoutines.transferStacks] using
    SubexpScanPrimitives.transfer_eval (⟨regs, s⟩ : Data) src dst 0 1 hne (by decide)

theorem finish_run (s : Store) (out : List Bool)
    (h101 : s 101 = []) (h102 : s 102 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn finish (2 * (s 241).length + 6 * out.length + 9)
      (multiplied s out) (Function.update s 244 out) := by
  let s₁ := Function.update s 102 out
  let s₂ := Function.update s 245 out.reverse
  have he₁ : Function.update (multiplied s out) 101 [] = s₁ := by
    funext i
    by_cases h : i = 101 <;> simp [multiplied, s₁, h, h101, Function.update_apply]
  have h₁ : ExecutesIn (clear 101) (2 * (s 241).length + 3) (multiplied s out) s₁ := by
    have h := clear_run 101 (multiplied s out)
    rw [he₁] at h
    simpa [multiplied] using h
  have he₂ : Function.update (Function.update s₁ 102 []) 245
      ((s₁ 102).reverse ++ s₁ 245) = s₂ := by
    funext i
    by_cases h : i = 102 <;> simp [s₁, s₂, h, h102, h245, Function.update_apply]
  have h₂ : ExecutesIn (transfer 102 245) (3 * out.length + 3) s₁ s₂ := by
    have h := transfer_run 102 245 s₁ (by decide)
    rw [he₂] at h
    simpa [s₁] using h
  have he₃ : Function.update (Function.update s₂ 245 []) 244
      ((s₂ 245).reverse ++ s₂ 244) = Function.update s 244 out := by
    funext i
    by_cases h : i = 245 <;> simp [s₂, h, h245, h244, Function.update_apply]
  have h₃ : ExecutesIn (transfer 245 244) (3 * out.length + 3) s₂
      (Function.update s 244 out) := by
    have h := transfer_run 245 244 s₂ (by decide)
    rw [he₃] at h
    simpa [s₂] using h
  have h := h₁.seq (h₂.seq h₃)
  convert h using 1
  · rfl
  · ring

/-- This composition theorem charges the actual native multiplication
execution and every bit moved around it. The multiplication premise is an
execution of the supplied fixed command, not a polynomial-result oracle. -/
theorem command_run (multiply : Code) (K : ℕ) (s : Store) (out : List Bool)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h106 : s 106 = []) (h120 : s 120 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (hmul : ExecutesIn multiply K (prepared s) (multiplied s out)) :
    ExecutesIn (command multiply)
      (K + 7 * ((s 240).length + (s 242).length + (s 243).length) +
        9 * (s 241).length + 6 * out.length + 29)
      s (Function.update s 244 out) := by
  have h := (prepare_run s h100 h101 h102 h106 h120).seq
    (hmul.seq (finish_run s out h101 h102 h244 h245))
  convert h using 1
  · rfl
  · ring

theorem command_run_uniform (multiply : Code) (K D B : ℕ) (s : Store) (out : List Bool)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h106 : s 106 = []) (h120 : s 120 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (hleft : (s 240).length = D * (4 * B))
    (hright : (s 241).length = D * (4 * B))
    (hzero : (s 242).length = D * (4 * B))
    (hD : (s 243).length = D) (hout : out.length = D * (4 * B))
    (hmul : ExecutesIn multiply K (prepared s) (multiplied s out)) :
    ExecutesIn (command multiply) (K + 150 * (D + 1) * (B + 1))
      s (Function.update s 244 out) := by
  apply (command_run multiply K s out h100 h101 h102 h106 h120 h244 h245 hmul).mono
  rw [hleft, hright, hzero, hD, hout]
  nlinarith

end SubexponentialSAT.SubexpPolynomialServiceControl

end OAI.Algorithms
