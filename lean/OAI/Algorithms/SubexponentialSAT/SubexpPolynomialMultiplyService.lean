import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl
import OAI.Algorithms.SubexponentialSAT.SubexpTruncatedMultiply

namespace OAI.Algorithms

/-! A reusable concrete multiplication service for local CRT loops. The
native convolution workspace is empty again on return; only output 244 is
changed. Runtime polynomial arrays and the unary dimension are cached in
240--243. This module composes physical copy/clear loops with the actual
quartic convolution program. -/

namespace SubexponentialSAT.SubexpPolynomialMultiplyService

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

def command : Code := SubexpPolynomialServiceControl.command SubexpTruncatedMultiply.command
def program := compiled command 240 244

def nativeInput (s : Store) : Buffers :=
  ![s 240, s 241, s 242, [], [], s 243, [], [], [], [], []]

theorem empty_buffers (s : Store) (hempty : ∀ i, s (bufferPorts i) = []) :
    buffers s (fun _ => []) = s := by
  classical
  funext j
  by_cases hj : ∃ i, bufferPorts i = j
  · obtain ⟨i, rfl⟩ := hj
    simp [hempty]
  · exact buffers_frame s _ j hj

theorem prepared_eq_buffers (s : Store) (hempty : ∀ i, s (bufferPorts i) = []) :
    SubexpPolynomialServiceControl.prepared s = buffers s (nativeInput s) := by
  have hw : nativeInput s = Function.update (Function.update (Function.update
      (Function.update (fun _ : Fin 11 => []) 0 (s 240)) 1 (s 241)) 2 (s 242)) 5 (s 243) := by
    funext i
    fin_cases i <;> simp [nativeInput]
  rw [hw, buffers_update, buffers_update, buffers_update, buffers_update, empty_buffers s hempty]
  rfl

theorem multiplied_eq_buffers (s : Store) (out : List Bool)
    (hempty : ∀ i, s (bufferPorts i) = []) :
    SubexpPolynomialServiceControl.multiplied s out =
      buffers s (finishedBuffers (nativeInput s) out) := by
  have hw : finishedBuffers (nativeInput s) out =
      Function.update (Function.update (fun _ : Fin 11 => []) 1 (s 241)) 2 out := by
    funext i
    fin_cases i <;> simp [nativeInput, finishedBuffers]
  rw [hw, buffers_update, buffers_update, empty_buffers s hempty]
  rfl

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

/-- All hypotheses describe actual stored words and empty scratch stacks.
The command is fixed independently of p, μ, and D. -/
theorem command_value (s : Store) (t z : SubexpTruncatedMultiply.Coefficient p μ)
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : SubexpConvolutionPairSpec.BaseReady p μ M s t scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (D : ℕ) (P Q : List (SubexpTruncatedMultiply.Coefficient p μ))
    (hP : P.length = D) (hQ : Q.length = D)
    (hleft : s 240 = encodeArray SubexpFlatAdd.encode P)
    (hright : s 241 = encodeArray SubexpFlatAdd.encode Q)
    (hzero : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hD : (s 243).length = D) :
    ExecutesIn command (601000 * (D + 1)^3 * (baseWidth p μ + 1)^2) s
      (Function.update s 244
        (encodeArray SubexpFlatAdd.encode (SubexpTruncatedMultiply.result p μ M t z D P Q))) := by
  let B := baseWidth p μ
  let out := encodeArray SubexpFlatAdd.encode (SubexpTruncatedMultiply.result p μ M t z D P Q)
  let K := convolutionBudget D (4 * B) (500000 * (D + 1) * (B + 1)^2)
  have hmul : ExecutesIn SubexpTruncatedMultiply.command K
      (SubexpPolynomialServiceControl.prepared s)
      (SubexpPolynomialServiceControl.multiplied s out) := by
    rw [prepared_eq_buffers s hempty, multiplied_eq_buffers s out hempty]
    exact SubexpTruncatedMultiply.command_value p μ M s t z scalarWidth frame H
      h120 h121 h122 D (nativeInput s) P Q hP hQ hleft hright hzero hD
      rfl rfl rfl rfl rfl rfl rfl
  have hlen (xs : List (SubexpTruncatedMultiply.Coefficient p μ)) :
      (encodeArray SubexpFlatAdd.encode xs).length = xs.length * (4 * B) := by
    exact encodeArray_length _ (4 * B) (fun a => SubexpFlatAdd.encode_length a) xs
  have h := SubexpPolynomialServiceControl.command_run_uniform
    SubexpTruncatedMultiply.command K D B s out
    (hempty 0) (hempty 1) (hempty 2) (hempty 5) h120 h244 h245
    (by rw [hleft, hlen, hP]) (by rw [hright, hlen, hQ])
    (by rw [hzero, hlen, List.length_replicate]) hD
    (by dsimp [out]; rw [hlen, SubexpTruncatedMultiply.result_length]) hmul
  apply h.mono
  have hK := convolutionBudget_quartic_le D B
  change K + 1 ≤ 600000 * (D + 1)^3 * (B + 1)^2 at hK
  calc
    K + 150 * (D + 1) * (B + 1) ≤
        600000 * (D + 1)^3 * (B + 1)^2 + 150 * (D + 1) * (B + 1) := by omega
    _ ≤ 601000 * (D + 1)^3 * (B + 1)^2 := by ring_nf; omega

theorem program_value (s : Store) (t z : SubexpTruncatedMultiply.Coefficient p μ)
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : SubexpConvolutionPairSpec.BaseReady p μ M s t scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (D : ℕ) (P Q : List (SubexpTruncatedMultiply.Coefficient p μ))
    (hP : P.length = D) (hQ : Q.length = D)
    (hleft : s 240 = encodeArray SubexpFlatAdd.encode P)
    (hright : s 241 = encodeArray SubexpFlatAdd.encode Q)
    (hzero : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hD : (s 243).length = D) (regs : Fin 16 → Bool) :
    ∃ n regs', n ≤ 601000 * (D + 1)^3 * (baseWidth p μ + 1)^2 + 1 ∧
      Trace program n ((⟨regs, s⟩ : Data).withPC (some program.entry))
        ((⟨regs', Function.update s 244
          (encodeArray SubexpFlatAdd.encode (SubexpTruncatedMultiply.result p μ M t z D P Q))⟩
            : Data).withPC none) := by
  obtain ⟨n, regs', hn, he⟩ := command_value p μ M s t z scalarWidth frame H hempty
    h120 h121 h122 h244 h245 D P Q hP hQ hleft hright hzero hD regs
  exact ⟨n + 1, regs', Nat.add_le_add_right hn 1, compiled_halt_trace he 240 244⟩

end SubexponentialSAT.SubexpPolynomialMultiplyService

end OAI.Algorithms
