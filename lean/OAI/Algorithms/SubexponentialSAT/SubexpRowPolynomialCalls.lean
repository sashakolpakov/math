import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices
import OAI.Algorithms.SubexponentialSAT.SubexpRowArithmeticRelocation
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialAddService
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialMultiplyService

namespace OAI.Algorithms

/-! Concrete dense-field arithmetic inside the framed row interpreter.
All hypotheses below describe encoded data, fixed-width operands, or empty
scratch stacks. The arithmetic traces are supplied by the actual published
addition and convolution programs. -/

namespace SubexponentialSAT.SubexpRowPolynomialCalls

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing
open SubexpConvolutionControl (Code Store Data ExecutesIn encodeArray bufferPorts)
open SubexpRowPostfixServices (prepared)

def addCommand : Code := SubexpPolynomialAddService.command
def mulCommand : Code := SubexpRowArithmeticRelocation.relocated
  SubexpPolynomialMultiplyService.command SubexpRowArithmeticRelocation.bank

def addProgram := SubexpRowPostfixServices.program addCommand
def mulProgram := SubexpRowPostfixServices.program mulCommand

abbrev Coefficient (p μ : ℕ) := Quad (Word (baseWidth p μ))

def encode {p μ : ℕ} (P : List (Coefficient p μ)) : List Bool :=
  encodeArray SubexpFlatAdd.encode P

theorem encode_eq (p μ : ℕ) (P : List (Coefficient p μ)) :
    encode P = DensePolynomialPrograms.encodePolynomial P :=
  (SubexpPolynomialAddService.encodePolynomial_eq_flatten_map P).symm

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

/-- The native add service receives the two parsed arrays and no semantic
oracle. Its output is reinserted into the original framed operand stack. -/
theorem add_runsIn (s : Store) (regs : Fin 16 → Bool)
    (ops : SubexpSymbolicCost.RingProgram (Coefficient p μ))
    (hadd : ∀ a b, (ops.addRun a b).1 = (SubexpPreparedQuartic.binaryAdd p μ M a b).1)
    (P Q : List (Coefficient p μ)) (tail width : List Bool)
    (frame : Fin 6 → List Bool) (hB : 0 < baseWidth p μ)
    (hw : width.length = baseWidth p μ)
    (hin : s 27 = true :: (Encoding.frame (encode Q) ++
      (true :: (Encoding.frame (encode P) ++ tail))))
    (h21 : s 21 = []) (h29 : s 29 = []) (h120 : s 120 = [])
    (h240 : s 240 = []) (h241 : s 241 = []) (h244 : s 244 = []) (h245 : s 245 = [])
    (hstore : ∀ i, (prepared s (encode P) (encode Q) tail)
        (SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i) :
    let out := encode (SubexpDensePolynomial.addProgram ops P Q).1
    RunsIn addProgram
      (31000 * (P.length + Q.length + 1) * (baseWidth p μ + 1)^2 +
        20 * ((encode P).length + (encode Q).length) + 8 * out.length + 69)
      ((⟨regs, s⟩ : Data).withPC (some addProgram.entry))
      ((⟨fun _ => false, Function.update s 27
        (true :: (Encoding.frame out ++ tail))⟩ : Data).withPC none) := by
  have ha := SubexpPolynomialAddService.command_value p μ M
    (prepared s (encode P) (encode Q) tail) hB ops hadd P Q width frame hw hstore
    (by simpa [prepared] using h120) (by simpa [prepared] using h244)
    (by simpa [prepared] using h245)
    (by simp [prepared, encode_eq]) (by simp [prepared, encode_eq])
  simp only [← encode_eq] at ha
  exact SubexpRowPostfixServices.program_runsIn addCommand _ s regs
    (encode P) (encode Q) tail (encode (SubexpDensePolynomial.addProgram ops P Q).1)
    hin h21 h29 h120 h240 h241 h244 ha

/-- Multiplication uses the statically relocated native bank, so persistent
source-cache data on 128--137 is untouched. All array lengths are runtime
data, and the service returns exactly D coefficient cells. -/
theorem mul_runsIn (s : Store) (regs : Fin 16 → Bool)
    (t z : Coefficient p μ) (D : ℕ) (P Q : List (Coefficient p μ))
    (tail scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hP : P.length = D) (hQ : Q.length = D)
    (hin : s 27 = true :: (Encoding.frame (encode Q) ++
      (true :: (Encoding.frame (encode P) ++ tail))))
    (h21 : s 21 = []) (h29 : s 29 = []) (h120 : s 120 = [])
    (h240 : s 240 = []) (h241 : s 241 = []) (h244 : s 244 = [])
    (H : SubexpConvolutionPairSpec.BaseReady p μ M
      ((prepared s (encode P) (encode Q) tail) ∘ SubexpRowArithmeticRelocation.bank)
      t scalarWidth frame)
    (hempty : ∀ i, ((prepared s (encode P) (encode Q) tail) ∘
      SubexpRowArithmeticRelocation.bank) (bufferPorts i) = [])
    (h121 : s 121 = []) (h122 : s 122 = []) (h245 : s 245 = [])
    (hzero : s 242 = encode (List.replicate D z)) (hD : (s 243).length = D) :
    let out := encode (SubexpTruncatedMultiply.result p μ M t z D P Q)
    RunsIn mulProgram
      (601000 * (D + 1)^3 * (baseWidth p μ + 1)^2 + 1 +
        20 * ((encode P).length + (encode Q).length) + 8 * out.length + 69)
      ((⟨regs, s⟩ : Data).withPC (some mulProgram.entry))
      ((⟨fun _ => false, Function.update s 27
        (true :: (Encoding.frame out ++ tail))⟩ : Data).withPC none) := by
  let ps := prepared s (encode P) (encode Q) tail
  have hn := SubexpPolynomialMultiplyService.command_value p μ M
    (ps ∘ SubexpRowArithmeticRelocation.bank) t z scalarWidth frame H hempty
    (by simpa [ps, prepared, Function.comp_def,
      SubexpRowArithmeticRelocation.bank_low _ (by decide : (120 : Fin 256).val < 128)] using h120)
    (by simpa [ps, prepared, Function.comp_def,
      SubexpRowArithmeticRelocation.bank_low _ (by decide : (121 : Fin 256).val < 128)] using h121)
    (by simpa [ps, prepared, Function.comp_def,
      SubexpRowArithmeticRelocation.bank_low _ (by decide : (122 : Fin 256).val < 128)] using h122)
    (by simpa [ps, prepared, Function.comp_def] using h244)
    (by simpa [ps, prepared, Function.comp_def] using h245)
    D P Q hP hQ
    (by simp [ps, prepared, encode])
    (by simp [ps, prepared, encode])
    (by simpa [ps, prepared, Function.comp_def, encode] using hzero)
    (by simpa [ps, prepared, Function.comp_def] using hD)
  have hm := SubexpRowArithmeticRelocation.bank_run
    SubexpPolynomialMultiplyService.command _ ps
    (encode (SubexpTruncatedMultiply.result p μ M t z D P Q)) hn
  exact SubexpRowPostfixServices.program_runsIn mulCommand _ s regs
    (encode P) (encode Q) tail (encode (SubexpTruncatedMultiply.result p μ M t z D P Q))
    hin h21 h29 h120 h240 h241 h244 hm

end SubexponentialSAT.SubexpRowPolynomialCalls

end OAI.Algorithms
