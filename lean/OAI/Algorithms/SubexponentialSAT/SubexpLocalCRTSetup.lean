import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialConstructor

namespace OAI.Algorithms

/-! Actual cache initialization for one local CRT correction. The zero and
one arrays are physically built from scalar cells and the runtime dimension;
the complete node stream and unary skip index are then copied into work.
-/

namespace SubexponentialSAT.SubexpLocalCRTSetup

open BitProgram StructuredCalls SubexpConvolutionControl

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def clearMany : List (Fin 256) → Code
  | [] => .base .skip
  | i :: rest => clear i ;; clearMany rest

def cleared : List (Fin 256) → Store → Store
  | [], s => s
  | i :: rest, s => cleared rest (Function.update s i [])

theorem cleared_apply (slots : List (Fin 256)) (s : Store) (j : Fin 256) :
    cleared slots s j = if j ∈ slots then [] else s j := by
  induction slots generalizing s with
  | nil => simp [cleared]
  | cons i rest ih =>
      rw [cleared, ih]
      by_cases hi : j = i <;> by_cases hr : j ∈ rest <;>
        simp [hi, hr ]

theorem clearMany_run (slots : List (Fin 256)) (s : Store) (L : ℕ)
    (hsize : ∀ j ∈ slots, (s j).length ≤ L) :
    ExecutesIn (clearMany slots) (slots.length * (2 * L + 3)) s (cleared slots s) := by
  induction slots generalizing s with
  | nil =>
      intro regs
      exact ⟨0, regs, by simp, .base (.skip _)⟩
  | cons i rest ih =>
      have h₁ := (clear_run i s).mono
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hsize i (by simp))) 3)
      have h₂ := ih (Function.update s i []) (by
        intro j hj
        by_cases hji : j = i
        · subst j
          simp
        · simpa [hji] using hsize j (List.mem_cons_of_mem i hj))
      have h := h₁.seq h₂
      convert h using 1 <;>
        first | rfl | omega | simp [Nat.add_mul, Nat.add_comm]

def token (dst : Fin 256) : Code :=
  .base (.seq (.atom (.set 0 true)) (.atom (.push dst 0)))

theorem token_run (s : Store) (dst : Fin 256) :
    ExecutesIn (token dst) 2 s (Function.update s dst (true :: s dst)) := by
  intro regs
  let d : Data := ⟨regs, s⟩
  have h₁ := StructuredProgram.Eval.atom (StructuredProgram.Atom.set 0 true) d
  have h₂ := StructuredProgram.Eval.atom (StructuredProgram.Atom.push dst 0)
    ((StructuredProgram.Atom.set 0 true).eval d)
  refine ⟨2, Function.update regs 0 true, le_rfl, ?_⟩
  simpa [token, d, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using
    Eval.base (h₁.seq h₂)

def initializeCaches : Code :=
  SubexpPolynomialConstructor.construct 104 104 242 ;;
    SubexpPolynomialConstructor.construct 207 104 220 ;;
    copy 220 240 ;; copy 214 215 ;; copy 216 217 ;; token 229

def zeroArray (D B : ℕ) : List Bool :=
  SubexpLinearFactorProgram.paddedBits B
    (List.replicate (4 * B) false) (List.replicate (4 * B) false) D

def oneArray (D B : ℕ) (one : List Bool) : List Bool :=
  SubexpLinearFactorProgram.paddedBits B one (List.replicate (4 * B) false) D

def initialized (s : Store) (D B : ℕ) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update s 242 (zeroArray D B)) 220 (oneArray D B (s 207)))
      240 (oneArray D B (s 207))) 215 (s 214)) 217 (s 216)) 229 [true]

theorem initialize_run (s : Store) (D B : ℕ)
    (hD : s 243 = List.replicate D true)
    (hzero : s 104 = List.replicate (4 * B) false)
    (hone : (s 207).length = 4 * B)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h107 : s 107 = []) (h108 : s 108 = []) (h120 : s 120 = [])
    (h215 : s 215 = []) (h217 : s 217 = []) (h220 : s 220 = [])
    (h229 : s 229 = []) (h240 : s 240 = []) (h242 : s 242 = []) (h245 : s 245 = []) :
    ExecutesIn initializeCaches
      (500 * (D + 1) * (B + 1) + 7 * ((s 214).length + (s 216).length) + 20)
      s (initialized s D B) := by
  let s₁ := Function.update s 242 (zeroArray D B)
  let s₂ := Function.update s₁ 220 (oneArray D B (s 207))
  let s₃ := Function.update s₂ 240 (oneArray D B (s 207))
  let s₄ := Function.update s₃ 215 (s 214)
  let s₅ := Function.update s₄ 217 (s 216)
  have h₁ : ExecutesIn (SubexpPolynomialConstructor.construct 104 104 242)
      (220 * (D + 1) * (B + 1)) s s₁ := by
    simpa [s₁, zeroArray, hzero] using SubexpPolynomialConstructor.construct_run
      s 104 104 242 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) D B (by simp [hzero]) (by simp [hzero])
      hD hzero h100 h101 h102 h107 h108 h120 h245 h242
  have h₂ : ExecutesIn (SubexpPolynomialConstructor.construct 207 104 220)
      (220 * (D + 1) * (B + 1)) s₁ s₂ := by
    simpa [s₂, s₁, oneArray, hzero] using SubexpPolynomialConstructor.construct_run
      s₁ 207 104 220 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) D B (by simpa [s₁] using hone) (by simp [s₁, hzero])
      (by simp [s₁, hD]) (by simp [s₁, hzero]) (by simp [s₁, h100])
      (by simp [s₁, h101]) (by simp [s₁, h102]) (by simp [s₁, h107])
      (by simp [s₁, h108]) (by simp [s₁, h120]) (by simp [s₁, h245]) (by simp [s₁, h220])
  have hlen : (oneArray D B (s 207)).length = D * (4 * B) :=
    SubexpLinearFactorProgram.paddedBits_length D B (s 207) _ hone (by simp)
  have h₃ : ExecutesIn (copy 220 240) (7 * (D * (4 * B)) + 5) s₂ s₃ := by
    simpa [s₃, s₂, s₁, h240, hlen] using copy_run 220 240 s₂
      (by decide) (by decide) (by decide) (by simp [s₂, s₁, h120])
  have h₄ : ExecutesIn (copy 214 215) (7 * (s 214).length + 5) s₃ s₄ := by
    simpa [s₄, s₃, s₂, s₁, h215] using copy_run 214 215 s₃
      (by decide) (by decide) (by decide) (by simp [s₃, s₂, s₁, h120])
  have h₅ : ExecutesIn (copy 216 217) (7 * (s 216).length + 5) s₄ s₅ := by
    simpa [s₅, s₄, s₃, s₂, s₁, h217] using copy_run 216 217 s₄
      (by decide) (by decide) (by decide) (by simp [s₄, s₃, s₂, s₁, h120])
  have h₆ : ExecutesIn (token 229) 2 s₅ (initialized s D B) := by
    simpa [s₅, s₄, s₃, s₂, s₁, initialized, h229] using token_run s₅ 229
  have h := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq h₆))))
  apply h.mono
  ring_nf
  omega

@[simp] theorem zeroArray_eq (D B : ℕ) :
    zeroArray D B = List.replicate (D * (4 * B)) false := by
  cases D with
  | zero => simp [zeroArray, SubexpLinearFactorProgram.paddedBits]
  | succ D =>
    cases D with
    | zero => simp [zeroArray, SubexpLinearFactorProgram.paddedBits]
    | succ D =>
      simp only [zeroArray, SubexpLinearFactorProgram.paddedBits]
      rw [← List.replicate_add, ← List.replicate_add]
      congr 1
      ring

end SubexponentialSAT.SubexpLocalCRTSetup

end OAI.Algorithms
