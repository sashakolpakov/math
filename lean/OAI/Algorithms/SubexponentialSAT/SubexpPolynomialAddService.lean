import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionStore
import OAI.Algorithms.SubexponentialSAT.DensePolynomialPrograms

namespace OAI.Algorithms

/-! Cached dense addition for the local CRT controller. The fixed service
copies operands 240/241, invokes the actual dense-add instruction table, and
moves its output to 244. All native workspace is restored. -/

namespace SubexponentialSAT.SubexpPolynomialAddService

open BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

def registers : Fin 8 ↪ Fin 16 := ⟨Fin.castAdd 8, Fin.castAdd_injective _ _⟩
def ports : Fin 20 ↪ Fin 256 := ⟨Fin.castAdd 236, Fin.castAdd_injective _ _⟩
def add : Code := DensePolynomialPrograms.callAt registers ports
def transfer (src dst : Fin 256) : Code :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 16) 1)
def finish : Code := .seq (transfer 8 245) (transfer 245 244)
def command : Code := .seq (copy 240 8) (.seq (copy 241 9) (.seq add finish))
def program := compiled command 240 244

def prepared (s : Store) : Store :=
  Function.update (Function.update s 8 (s 240)) 9 (s 241)

theorem encodePolynomial_eq_flatten_map {B : ℕ} (P : List (Quad (Word B))) :
    DensePolynomialPrograms.encodePolynomial P = (P.map SubexpFlatAdd.encode).flatten := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simpa [DensePolynomialPrograms.encodePolynomial, DensePolynomialPrograms.polynomialWords,
        DensePolynomialLoop.flatten, SubexpFlatAdd.encode, SubexpFlatAdd.flatten] using
        congrArg (fun xs => SubexpFlatAdd.encode a ++ xs) ih

private theorem transfer_run (src dst : Fin 256) (s : Store) (hne : src ≠ dst) :
    ExecutesIn (transfer src dst) (3 * (s src).length + 3) s
      (Function.update (Function.update s src []) dst ((s src).reverse ++ s dst)) := by
  intro regs
  refine ⟨_, readRegs regs 0 1 none, le_rfl, ?_⟩
  simpa [transfer, afterTransfer, StackRoutines.transferStacks] using
    SubexpScanPrimitives.transfer_eval (⟨regs, s⟩ : Data) src dst 0 1 hne (by decide)

theorem finish_run (s : Store) (out : List Bool)
    (h8 : s 8 = []) (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn finish (6 * out.length + 6) (Function.update s 8 out)
      (Function.update s 244 out) := by
  let middle := Function.update s 245 out.reverse
  have he₁ : Function.update (Function.update (Function.update s 8 out) 8 []) 245
      (((Function.update s 8 out) 8).reverse ++ (Function.update s 8 out) 245) = middle := by
    funext i
    by_cases h : i = 8 <;> simp [middle, Function.update_apply, h, h8, h245]
  have h₁ : ExecutesIn (transfer 8 245) (3 * out.length + 3) (Function.update s 8 out) middle := by
    have h := transfer_run 8 245 (Function.update s 8 out) (by decide)
    rw [he₁] at h
    simpa using h
  have he₂ : Function.update (Function.update middle 245 []) 244
      ((middle 245).reverse ++ middle 244) = Function.update s 244 out := by
    funext i
    by_cases h : i = 245 <;> simp [middle, Function.update_apply, h, h245, h244]
  have h₂ : ExecutesIn (transfer 245 244) (3 * out.length + 3) middle
      (Function.update s 244 out) := by
    have h := transfer_run 245 244 middle (by decide)
    rw [he₂] at h
    simpa [middle] using h
  convert h₁.seq h₂ using 1
  · rfl
  · omega

theorem addProgram_length {C : Type*} (ops : SubexpSymbolicCost.RingProgram C)
    (P Q : List C) :
    (SubexpDensePolynomial.addProgram ops P Q).1.length = max P.length Q.length := by
  induction P generalizing Q with
  | nil => simp [SubexpDensePolynomial.addProgram]
  | cons a P ih =>
      cases Q with
      | nil => simp [SubexpDensePolynomial.addProgram]
      | cons b Q =>
          have h := ih Q
          change (SubexpDensePolynomial.addProgram ops P Q).1.length + 1 =
            max (P.length + 1) (Q.length + 1)
          omega

private theorem addProgram_length_le {C : Type*} (ops : SubexpSymbolicCost.RingProgram C)
    (P Q : List C) : (SubexpDensePolynomial.addProgram ops P Q).1.length ≤ P.length + Q.length := by
  rw [addProgram_length]
  omega

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem command_value (s : Store) (hB : 0 < baseWidth p μ)
    (ops : SubexpSymbolicCost.RingProgram (Quad (Word (baseWidth p μ))))
    (hadd : ∀ a b, (ops.addRun a b).1 = (SubexpPreparedQuartic.binaryAdd p μ M a b).1)
    (P Q : List (Quad (Word (baseWidth p μ))))
    (width : List Bool) (frame : Fin 6 → List Bool) (hw : width.length = baseWidth p μ)
    (hstore : ∀ i, s (ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i)
    (h120 : s 120 = []) (h244 : s 244 = []) (h245 : s 245 = [])
    (hleft : s 240 = DensePolynomialPrograms.encodePolynomial P)
    (hright : s 241 = DensePolynomialPrograms.encodePolynomial Q) :
    ExecutesIn command (31000 * (P.length + Q.length + 1) * (baseWidth p μ + 1)^2)
      s (Function.update s 244
        (DensePolynomialPrograms.encodePolynomial (SubexpDensePolynomial.addProgram ops P Q).1)) := by
  let out := DensePolynomialPrograms.encodePolynomial (SubexpDensePolynomial.addProgram ops P Q).1
  let s₁ := Function.update s 8 (s 240)
  let K := 30000 * (P.length + Q.length + 1) * (baseWidth p μ + 1)^2
  have h8 : s 8 = [] := by simpa [ports, DensePolynomialLoop.ready,
    DensePolynomialLoop.state, DensePolynomialLoop.stackArray,
    Fin.addCases, Fin.coe_ofNat_eq_mod] using hstore 8
  have h9 : s 9 = [] := by simpa [ports, DensePolynomialLoop.ready,
    DensePolynomialLoop.state, DensePolynomialLoop.stackArray,
    Fin.addCases, Fin.coe_ofNat_eq_mod] using hstore 9
  have h₁ : ExecutesIn (copy 240 8) (7 * (s 240).length + 5) s s₁ := by
    simpa [s₁, h8] using copy_run 240 8 s (by decide) (by decide) (by decide) h120
  have h₂ : ExecutesIn (copy 241 9) (7 * (s 241).length + 5) s₁ (prepared s) := by
    simpa [s₁, prepared, h9] using copy_run 241 9 s₁
      (by decide) (by decide) (by decide) (by simp [s₁, h120])
  have hs : ∀ i, (prepared s) (ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits
        (DensePolynomialPrograms.encodePolynomial P) (DensePolynomialPrograms.encodePolynomial Q)
        width [] frame).stacks i := by
    intro i
    have hi := hstore i
    fin_cases i <;>
      simp [prepared, ports, DensePolynomialLoop.ready, DensePolynomialLoop.state,
        DensePolynomialLoop.stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod, hleft, hright] at hi ⊢
      <;> assumption
  have hout : Function.update (Function.update (prepared s) (ports 8) out) (ports 9) [] =
      Function.update s 8 out := by
    funext i
    by_cases h : i = 9 <;> by_cases h' : i = 8 <;>
      simp [ports, prepared, Function.update_apply, h, h', h9]
  have h₃ : ExecutesIn add K (prepared s) (Function.update s 8 out) := by
    intro regs
    obtain ⟨n, rf, hn, he⟩ := DensePolynomialPrograms.callAt_eval p μ M registers ports
      hB ops hadd P Q width frame hw (⟨regs, prepared s⟩ : Data) hs
    refine ⟨n, Function.extend registers rf regs, hn, ?_⟩
    simpa only [add, out, hout] using he
  have h₄ := finish_run s out h8 h244 h245
  have h := h₁.seq (h₂.seq (h₃.seq h₄))
  apply h.mono
  rw [hleft, hright, DensePolynomialPrograms.encodePolynomial_length,
    DensePolynomialPrograms.encodePolynomial_length]
  have hlen : out.length ≤ 4 * (P.length + Q.length) * baseWidth p μ := by
    dsimp [out]
    rw [DensePolynomialPrograms.encodePolynomial_length]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (addProgram_length_le ops P Q))
  have hsq : baseWidth p μ + 1 ≤ (baseWidth p μ + 1)^2 := by
    nlinarith [Nat.zero_le ((baseWidth p μ)^2)]
  have hscale := Nat.mul_le_mul_left (52 * (P.length + Q.length + 1)) hsq
  change _ ≤ 31000 * (P.length + Q.length + 1) * (baseWidth p μ + 1)^2
  dsimp [K]
  nlinarith [Nat.zero_le ((P.length + Q.length + 1) * (baseWidth p μ + 1)^2)]

theorem prepared_command_value (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (t z o : SubexpSymbolicCost.QuarticCode p D)
    (s : Store) (hB : 0 < baseWidth p (D + 1))
    (P Q : List (SubexpSymbolicCost.QuarticCode p D))
    (width : List Bool) (frame : Fin 6 → List Bool) (hw : width.length = baseWidth p (D + 1))
    (hstore : ∀ i, s (ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i)
    (h120 : s 120 = []) (h244 : s 244 = []) (h245 : s 245 = [])
    (hleft : s 240 = DensePolynomialPrograms.encodePolynomial P)
    (hright : s 241 = DensePolynomialPrograms.encodePolynomial Q) :
    ExecutesIn command (31000 * (P.length + Q.length + 1) * (baseWidth p (D + 1) + 1)^2)
      s (Function.update s 244
        (DensePolynomialPrograms.encodePolynomial
          (SubexpDensePolynomial.addProgram (SubexpSymbolicCost.preparedProgram p D M t z o) P Q).1)) :=
  command_value p (D + 1) M s hB (SubexpSymbolicCost.preparedProgram p D M t z o)
    (fun _ _ => rfl) P Q width frame hw hstore h120 h244 h245 hleft hright

end SubexponentialSAT.SubexpPolynomialAddService

end OAI.Algorithms
