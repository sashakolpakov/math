import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramAdd
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialAddService

namespace OAI.Algorithms

/-! The arbitrary-degree native adder relocated into a caller, with all
untouched stacks preserved. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)

/-- Relocate the fixed addition program into a caller's physical workspace. -/
abbrev callAt {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 20 ↪ Fin s) : Cmd r s :=
  .call (ProgramLinking.liftProgram addProgram registers ports)

private theorem extend_agree {α β γ : Type*} (f : α ↪ β) (values : α → γ)
    (frame : β → γ) (h : ∀ i, frame (f i) = values i) :
    Function.extend f values frame = frame := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply, h]
  · exact Function.extend_apply' _ _ _ hj

/-- The relocated call changes only its two input/output ports. The complete
bit-level addition trace, including its return instruction, is retained. -/
theorem callAt_eval {degree r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 20 ↪ Fin s)
    (hB : 0 < baseWidth p t)
    (ops : SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (hadd : ∀ a b, (ops.addRun a b).1 = (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (P Q : List (Coeff (baseWidth p t) degree)) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p t) (d : State r s)
    (hstore : ∀ i, d.stacks (ports i) =
      (ready (fun _ => false) M.bits (encode P) (encode Q) width [] frame).stacks i) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool),
      n ≤ 7000 * (degree * (P.length + Q.length) + 1) * (baseWidth p t + 1)^2 + 1 ∧
      Eval (callAt registers ports) n d
        ⟨Function.extend registers rf d.regs,
          Function.update (Function.update d.stacks (ports 8)
            (encode (SubexpDensePolynomial.addProgram ops P Q).1)) (ports 9) []⟩ := by
  let start := ready (fun i => d.regs (registers i)) M.bits
    (encode P) (encode Q) width [] frame
  obtain ⟨n, hn, rf, ht⟩ := add_trace p t M cache hB (fun i => d.regs (registers i))
    ops hadd P Q width frame hwidth
  have hp : projectState registers ports d = start := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      exact hstore i
  have hc := eval_call_from_state addProgram registers ports d registers.injective ports.injective
    (by simpa only [hp] using ht)
  have hout :
      (ready rf M.bits (encode (SubexpDensePolynomial.addProgram ops P Q).1)
        [] width [] frame).stacks =
      Function.update (Function.update start.stacks 8
        (encode (SubexpDensePolynomial.addProgram ops P Q).1)) 9 [] := by
    funext i
    fin_cases i <;> simp [ready, DensePolynomialLoop.state, stackArray, start,
      Fin.addCases, Fin.coe_ofNat_eq_mod]
  have hi : Function.extend ports start.stacks d.stacks = d.stacks :=
    extend_agree ports start.stacks d.stacks hstore
  have he : embedState registers ports d
      (ready rf M.bits (encode (SubexpDensePolynomial.addProgram ops P Q).1)
        [] width [] frame) =
      (⟨Function.extend registers rf d.regs,
        Function.update (Function.update d.stacks (ports 8)
          (encode (SubexpDensePolynomial.addProgram ops P Q).1)) (ports 9) []⟩ : State r s) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · change Function.extend ports _ d.stacks = _
      rw [hout, ProgramLinking.extend_update ports.injective,
        ProgramLinking.extend_update ports.injective, hi]
  exact ⟨n, rf, hn, by simpa only [he, callAt] using hc⟩


namespace AddService
open SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpPolynomialAddService

def command : Code := .seq (copy 240 8) (.seq (copy 241 9)
  (.seq (DensePolynomialProgram.callAt registers ports) finish))
def program := compiled command 240 244

def budget (degree B a b : ℕ) : ℕ :=
  7000 * (degree * (a + b) + 1) * (B + 1)^2 + 1 +
    13 * degree * B * (a + b) + 16

theorem command_value {degree : ℕ} (s : Store) (hB : 0 < baseWidth p t)
    (ops : SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (hadd : ∀ a b, (ops.addRun a b).1 = (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (P Q : List (Coeff (baseWidth p t) degree))
    (width : List Bool) (frame : Fin 6 → List Bool) (hw : width.length = baseWidth p t)
    (hstore : ∀ i, s (ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i)
    (h120 : s 120 = []) (h244 : s 244 = []) (h245 : s 245 = [])
    (hleft : s 240 = encode P)
    (hright : s 241 = encode Q) :
    ExecutesIn command (budget degree (baseWidth p t) P.length Q.length)
      s (Function.update s 244
        (encode (SubexpDensePolynomial.addProgram ops P Q).1)) := by
  let out := encode (SubexpDensePolynomial.addProgram ops P Q).1
  let s₁ := Function.update s 8 (s 240)
  let K := 7000 * (degree * (P.length + Q.length) + 1) * (baseWidth p t + 1)^2 + 1
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
        (encode P) (encode Q)
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
  have h₃ : ExecutesIn (DensePolynomialProgram.callAt registers ports) K (prepared s) (Function.update s 8 out) := by
    intro regs
    obtain ⟨n, rf, hn, he⟩ := DensePolynomialProgram.callAt_eval p t M cache registers ports
      hB ops hadd P Q width frame hw (⟨regs, prepared s⟩ : SubexponentialSAT.SubexpConvolutionControl.Data) hs
    refine ⟨n, Function.extend registers rf regs, hn, ?_⟩
    simpa only [out, hout] using he
  have h₄ := finish_run s out h8 h244 h245
  have h := h₁.seq (h₂.seq (h₃.seq h₄))
  apply h.mono
  rw [hleft, hright, encode_length, encode_length]
  have hlen : out.length ≤ (P.length + Q.length) * (degree * baseWidth p t) := by
    dsimp [out]
    rw [encode_length, addProgram_length]
    exact Nat.mul_le_mul_right _ (by omega)
  change _ ≤ budget degree (baseWidth p t) P.length Q.length
  dsimp [K, budget]
  nlinarith

end AddService
end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
