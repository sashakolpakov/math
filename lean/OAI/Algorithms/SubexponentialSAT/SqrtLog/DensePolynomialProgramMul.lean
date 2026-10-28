import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramAdd
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialMultiplyService
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionAlgebra

namespace OAI.Algorithms

/-! Runtime-sized dense convolution and old-compatible cached-array services.
The local pair premise is an actual fixed-command trace; all scans, writes,
copies, counter steps, and final halts are included by the audited controller.
A concrete native ring-pair instantiation is supplied separately. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost

variable {C R : Type*}

def result (ops : RingProgram C) (J : ℕ) (P Q : List C) : List C :=
  SubexponentialSAT.TruncatedConvolution.run ops.zeroRun.1
    (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1) J P Q

@[simp] theorem result_length (ops : RingProgram C) (J : ℕ) (P Q : List C) :
    (result ops J P Q).length = J := SubexponentialSAT.TruncatedConvolution.run_length _ _ _ _ _ _

theorem result_correct [CommRing R] (ops : RepresentedRing C R)
    (J : ℕ) (P Q : List C) :
    SubexponentialSAT.PolynomialAlgorithm.denote ((result ops.program J P Q).map ops.decode) =
      SubexponentialSAT.Truncation.trunc J (SubexponentialSAT.PolynomialAlgorithm.denote (P.map ops.decode) *
        SubexponentialSAT.PolynomialAlgorithm.denote (Q.map ops.decode)) := by
  apply SubexponentialSAT.SubexpConvolutionAlgebra.run_correct
  · exact ops.add_correct
  · exact ops.mul_correct
  · exact ops.zero_correct

/-- The fixed cached-array wrapper uses 240/241 operands, 242 zero array,
243 unary length, and 244 output. The pair program is fixed independently
of all runtime dimensions. -/
def mulCommand (pair : Code) : Code :=
  SubexponentialSAT.SubexpPolynomialServiceControl.command (SubexponentialSAT.SubexpConvolutionControl.command pair)

def mulProgram (pair : Code) := compiled (mulCommand pair) 240 244

def mulBudget (J W pairCost : ℕ) : ℕ :=
  convolutionBudget J W pairCost + 29 * J * W + 7 * J + 30

/-- Actual native execution conditional only on the separately checked local
ring multiply-and-accumulate command. No array operation is free. -/
theorem mul_service_eval {B degree : ℕ}
    (pair : Code) (s : Store) (ops : RingProgram (Coeff B degree))
    (J pairCost : ℕ) (P Q : List (Coeff B degree))
    (hpair : PairSpec pair s RingProgram.flat
      (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1) J pairCost)
    (hwidth : (s 104).length = degree * B)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (hP : P.length = J) (hQ : Q.length = J)
    (hleft : s 240 = encode P) (hright : s 241 = encode Q)
    (hzero : s 242 = encode (List.replicate J ops.zeroRun.1))
    (hJ : (s 243).length = J) :
    ExecutesIn (mulCommand pair) (mulBudget J (degree * B) pairCost - 1) s
      (Function.update s 244 (encode (result ops J P Q))) := by
  let out := encode (result ops J P Q)
  let K := convolutionBudget J (degree * B) pairCost
  have hmul : ExecutesIn (SubexponentialSAT.SubexpConvolutionControl.command pair) K
      (SubexponentialSAT.SubexpPolynomialServiceControl.prepared s)
      (SubexponentialSAT.SubexpPolynomialServiceControl.multiplied s out) := by
    rw [SubexponentialSAT.SubexpPolynomialMultiplyService.prepared_eq_buffers s hempty,
      SubexponentialSAT.SubexpPolynomialMultiplyService.multiplied_eq_buffers s out hempty]
    exact initialized_command_run pair s RingProgram.flat ops.zeroRun.1
      (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1)
      J (degree * B) pairCost hpair RingProgram.flat_length hwidth h120 h121 h122
      (SubexponentialSAT.SubexpPolynomialMultiplyService.nativeInput s) P Q hP hQ
      hleft hright hzero hJ rfl rfl rfl rfl rfl rfl rfl
  have h := SubexponentialSAT.SubexpPolynomialServiceControl.command_run
    (SubexponentialSAT.SubexpConvolutionControl.command pair) K s out
    (hempty 0) (hempty 1) (hempty 2) (hempty 5) h120 h244 h245 hmul
  convert h using 1
  · rfl
  · rw [hleft, hright, hzero, hJ]
    simp only [out, encode_length, result_length, List.length_replicate, hP, hQ]
    dsimp only [K, mulBudget]
    simp only [Nat.mul_assoc]
    omega

theorem mul_service_trace {B degree : ℕ}
    (pair : Code) (s : Store) (ops : RingProgram (Coeff B degree))
    (J pairCost : ℕ) (P Q : List (Coeff B degree))
    (hpair : PairSpec pair s RingProgram.flat
      (fun a b => (ops.addRun a b).1) (fun a b => (ops.mulRun a b).1) J pairCost)
    (hwidth : (s 104).length = degree * B)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (hP : P.length = J) (hQ : Q.length = J)
    (hleft : s 240 = encode P) (hright : s 241 = encode Q)
    (hzero : s 242 = encode (List.replicate J ops.zeroRun.1))
    (hJ : (s 243).length = J) (regs : Fin 16 → Bool) :
    ∃ n ≤ mulBudget J (degree * B) pairCost, ∃ regs',
      Trace (mulProgram pair) n
        ((⟨regs,s⟩ : Data).withPC (some (mulProgram pair).entry))
        ((⟨regs',Function.update s 244 (encode (result ops J P Q))⟩ : Data).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := mul_service_eval pair s ops J pairCost P Q hpair hwidth hempty
    h120 h121 h122 h244 h245 hP hQ hleft hright hzero hJ regs
  refine ⟨n+1, ?_, rf, compiled_halt_trace he 240 244⟩
  have hp : 0 < mulBudget J (degree * B) pairCost := by unfold mulBudget; omega
  omega

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
