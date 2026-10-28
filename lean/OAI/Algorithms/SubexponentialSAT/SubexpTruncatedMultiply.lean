import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionExecution
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionPairSpec
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionAlgebra

namespace OAI.Algorithms

/-! The actual fixed truncated-polynomial multiplication service. Its code
contains no size-dependent control or mathematical scalar callback. The
physical input layout supplies the stored modulus, reduction coefficients,
and scalar width; every coefficient operation is executed by the concrete
quartic service. -/

namespace SubexponentialSAT.SubexpTruncatedMultiply

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

abbrev Coefficient (p μ : ℕ) := Quad (Word (baseWidth p μ))

def command : Code := SubexpConvolutionControl.command SubexpConvolutionPair.command

def program := SubexpConvolutionControl.program SubexpConvolutionPair.command

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def result (t z : Coefficient p μ) (D : ℕ) (P Q : List (Coefficient p μ)) :
    List (Coefficient p μ) :=
  TruncatedConvolution.run z (SubexpConvolutionPairSpec.add p μ M)
    (SubexpConvolutionPairSpec.mul p μ M t) D P Q

omit [Fact (Nat.Prime p)] in
@[simp] theorem result_length (t z : Coefficient p μ) (D : ℕ)
    (P Q : List (Coefficient p μ)) : (result p μ M t z D P Q).length = D :=
  TruncatedConvolution.run_length _ _ _ _ _ _

/-- This is an actual command execution contract. `BaseReady` describes the
stored arithmetic inputs and scratch cells, rather than assuming a scalar
result or a scalar runtime. -/
theorem command_value (base : Store) (t z : Coefficient p μ)
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : SubexpConvolutionPairSpec.BaseReady p μ M base t scalarWidth frame)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (D : ℕ) (w : Buffers) (P Q : List (Coefficient p μ))
    (hP : P.length = D) (hQ : Q.length = D)
    (hleft : w 0 = encodeArray SubexpFlatAdd.encode P)
    (hright : w 1 = encodeArray SubexpFlatAdd.encode Q)
    (hacc : w 2 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hcount : (w 5).length = D) (h4 : w 4 = [])
    (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
    (h9 : w 9 = []) (h10 : w 10 = []) :
    ExecutesIn command
      (convolutionBudget D (4 * baseWidth p μ) (500000 * (D + 1) * (baseWidth p μ + 1)^2))
      (buffers base w)
      (buffers base (finishedBuffers w (encodeArray SubexpFlatAdd.encode (result p μ M t z D P Q)))) := by
  exact initialized_command_run SubexpConvolutionPair.command base SubexpFlatAdd.encode z
    (SubexpConvolutionPairSpec.add p μ M) (SubexpConvolutionPairSpec.mul p μ M t)
    D (4 * baseWidth p μ) (500000 * (D + 1) * (baseWidth p μ + 1)^2)
    (SubexpConvolutionPairSpec.pairSpec p μ M base t scalarWidth frame H D)
    (fun c => SubexpFlatAdd.encode_length c) H.width h120 h121 h122
    w P Q hP hQ hleft hright hacc hcount h4 h3 h6 h7 h8 h9 h10

/-- The source program is fixed while D and the field data remain on its
stacks. The final halt is included in the displayed polynomial bound. -/
theorem program_value (base : Store) (t z : Coefficient p μ)
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : SubexpConvolutionPairSpec.BaseReady p μ M base t scalarWidth frame)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (D : ℕ) (w : Buffers) (P Q : List (Coefficient p μ))
    (hP : P.length = D) (hQ : Q.length = D)
    (hleft : w 0 = encodeArray SubexpFlatAdd.encode P)
    (hright : w 1 = encodeArray SubexpFlatAdd.encode Q)
    (hacc : w 2 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hcount : (w 5).length = D) (h4 : w 4 = [])
    (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
    (h9 : w 9 = []) (h10 : w 10 = []) (regs : Fin 16 → Bool) :
    ∃ n regs', n ≤ 600000 * (D + 1)^3 * (baseWidth p μ + 1)^2 ∧
      Trace program n
        ((⟨regs, buffers base w⟩ : Data).withPC (some program.entry))
        ((⟨regs', buffers base (finishedBuffers w
          (encodeArray SubexpFlatAdd.encode (result p μ M t z D P Q)))⟩ : Data).withPC none) := by
  have h := command_value p μ M base t z scalarWidth frame H h120 h121 h122
    D w P Q hP hQ hleft hright hacc hcount h4 h3 h6 h7 h8 h9 h10
  obtain ⟨n, regs', hn, he⟩ := compiled_command_run SubexpConvolutionPair.command h regs
  exact ⟨n, regs', hn.trans (convolutionBudget_quartic_le D (baseWidth p μ)), he⟩

/-- The checked primitive compiler contributes one fixed multiplicative
constant, independent of the runtime dimensions and field parameters. -/
theorem primitive_value (base : Store) (t z : Coefficient p μ)
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : SubexpConvolutionPairSpec.BaseReady p μ M base t scalarWidth frame)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (D : ℕ) (w : Buffers) (P Q : List (Coefficient p μ))
    (hP : P.length = D) (hQ : Q.length = D)
    (hleft : w 0 = encodeArray SubexpFlatAdd.encode P)
    (hright : w 1 = encodeArray SubexpFlatAdd.encode Q)
    (hacc : w 2 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hcount : (w 5).length = D) (h4 : w 4 = [])
    (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
    (h9 : w 9 = []) (h10 : w 10 = []) (regs : Fin 16 → Bool) :
    ∃ n regs', n ≤ primitiveOverhead program *
        (600000 * (D + 1)^3 * (baseWidth p μ + 1)^2) ∧
      SubexpQuarticFlatMul.PrimitiveRunsIn program n
        ((⟨regs, buffers base w⟩ : Data).withPC (some program.entry))
        ((⟨regs', buffers base (finishedBuffers w
          (encodeArray SubexpFlatAdd.encode (result p μ M t z D P Q)))⟩ : Data).withPC none) := by
  obtain ⟨n, regs', hn, he⟩ := program_value p μ M base t z scalarWidth frame H
    h120 h121 h122 D w P Q hP hQ hleft hright hacc hcount h4 h3 h6 h7 h8 h9 h10 regs
  exact ⟨primitiveOverhead program * n, regs', Nat.mul_le_mul_left _ hn,
    SubexpQuarticFlatMul.primitiveRunsIn_of_runsIn program ⟨n, le_rfl, he⟩⟩

/-- The exact encoded output of the preceding machine theorems denotes the
truncated polynomial product. -/
theorem result_correct (c : Fin 4 → ZMod (p^μ)) (t z : Coefficient p μ)
    (ht : t.map (wordValue p μ) = reductionData c)
    (hz : quotientDenote c (z.map (wordValue p μ)) = 0)
    (D : ℕ) (P Q : List (Coefficient p μ)) :
    let decode := fun a : Coefficient p μ => quotientDenote c (a.map (wordValue p μ))
    PolynomialAlgorithm.denote ((result p μ M t z D P Q).map decode) =
      Truncation.trunc D (PolynomialAlgorithm.denote (P.map decode) * PolynomialAlgorithm.denote (Q.map decode)) := by
  exact SubexpConvolutionAlgebra.prepared_run_correct p μ M c t z ht hz D P Q

end SubexponentialSAT.SubexpTruncatedMultiply

end OAI.Algorithms
