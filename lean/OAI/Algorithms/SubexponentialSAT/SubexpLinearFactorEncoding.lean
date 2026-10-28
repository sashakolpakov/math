import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLinearFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCorrectionAlgebra
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionEncoding

namespace OAI.Algorithms

/-! Exact coefficient-list meaning of the fixed padded-linear constructor.
The output is constant first, with each coefficient in the caller's flat
encoding; no conversion or serialization step is omitted. -/

namespace SubexponentialSAT.SubexpLinearFactorEncoding

open Polynomial BitProgram StructuredCalls
open SubexpLinearFactorProgram

theorem flatten_replicate_false (n W : ℕ) :
    (List.replicate n (List.replicate W false)).flatten = List.replicate (n * W) false := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.flatten_cons, ih]
      rw [← List.replicate_add]
      congr 1
      ring

theorem encode_padded {C : Type*} (encode : C → List Bool) (zero low high : C)
    (B D : ℕ) (hz : encode zero = List.replicate (4 * B) false) :
    SubexpConvolutionEncoding.encodeArray encode
      (SubexpLocalCorrectionAlgebra.padded zero low high D) =
        paddedBits B (encode low) (encode high) D := by
  cases D with
  | zero => rfl
  | succ D =>
      cases D with
      | zero => simp [SubexpConvolutionEncoding.encodeArray,
          SubexpLocalCorrectionAlgebra.padded, paddedBits]
      | succ n =>
          simp [SubexpConvolutionEncoding.encodeArray, SubexpLocalCorrectionAlgebra.padded,
            paddedBits, hz, List.append_assoc]

/-- The fixed constructor's actual output is exactly the encoded dense
linear polynomial, including the cases D=0 and D=1. -/
theorem command_encodes_padded {C : Type*} (encode : C → List Bool)
    (zero low high : C) (d : Data) (D B : ℕ)
    (hz : encode zero = List.replicate (4 * B) false)
    (hlow : d.stacks 100 = encode low) (hhigh : d.stacks 101 = encode high)
    (hllen : (encode low).length = 4 * B) (hhlen : (encode high).length = 4 * B)
    (hD : d.stacks 109 = List.replicate D true) (hB : (d.stacks 10).length = B)
    (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    ∃ n ≤ 200 * (D + 1) * (B + 1), ∃ regs,
      Eval command n d
        ⟨regs, Function.update (Function.update d.stacks 104 (encode zero)) 102
          (SubexpConvolutionEncoding.encodeArray encode
            (SubexpLocalCorrectionAlgebra.padded zero low high D))⟩ := by
  obtain ⟨n, hn, regs, he⟩ := command_eval d D B (encode low) (encode high)
    hlow hhigh hllen hhlen hD hB h102 h104 h106 h107 h108
  exact ⟨n, hn, regs, by simpa only [result, hz, encode_padded encode zero low high B D hz] using he⟩

/-- The encoded coefficient array produced by the machine denotes precisely
the truncated linear polynomial used by the local-factor product. -/
theorem constructed_polynomial {C R : Type*} [CommRing R]
    (decode : C → R) (zero low high : C) (hz : decode zero = 0) (D : ℕ) :
    PolynomialAlgorithm.denote
      ((SubexpLocalCorrectionAlgebra.padded zero low high D).map decode) =
        Truncation.trunc D (Polynomial.C (decode low) + X * Polynomial.C (decode high)) :=
  SubexpLocalCorrectionAlgebra.padded_denote decode zero low high hz D

end SubexponentialSAT.SubexpLinearFactorEncoding

end OAI.Algorithms
