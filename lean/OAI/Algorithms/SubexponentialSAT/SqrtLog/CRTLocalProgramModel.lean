import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramFixedBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramConstructorSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramScanAlgebra

namespace OAI.Algorithms

/-! Fixed-length array instantiation of the local Hermite algebra. The
constructor and head split are exact identities of physical bit strings. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Model
open Polynomial
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram

abbrev Poly (B d J : ℕ) := Fixed.Array B d J

noncomputable def denote {B d J : ℕ} {R : Type*} [CommRing R]
    (decode : Coeff B d → R) (P : Poly B d J) : R[X] :=
  SubexponentialSAT.PolynomialAlgorithm.denote (P.1.map decode)

def padded {B d : ℕ} (zero low high : Coeff B d) (J : ℕ) : Poly B d J :=
  ⟨Constructor.coefficients zero low high J, Constructor.coefficients_length _ _ _ _⟩

def constant {B d : ℕ} (zero a : Coeff B d) (J : ℕ) : Poly B d J := padded zero a zero J

def linear {B d : ℕ} (zero one a : Coeff B d) (J : ℕ) : Poly B d J := padded zero a one J

def zero {B d : ℕ} (z : Coeff B d) (J : ℕ) : Poly B d J :=
  ⟨List.replicate J z, by simp⟩

theorem padded_encode {B d : ℕ} (z low high : Coeff B d)
    (hz : RingProgram.flat z = List.replicate (d*B) false) (J : ℕ) :
    Fixed.encode (padded z low high J) =
      Constructor.Counter.paddedBits (d*B) (RingProgram.flat low) (RingProgram.flat high) J :=
  Constructor.encode_coefficients z low high hz J

theorem coefficients_eq_padded {C : Type*} (z low high : C) (J : ℕ) :
    Constructor.coefficients z low high J = SubexponentialSAT.SubexpLocalCorrectionAlgebra.padded z low high J := by
  cases J with
  | zero => rfl
  | succ J => cases J <;> rfl

theorem padded_denote {B d : ℕ} {R : Type*} [CommRing R]
    (decode : Coeff B d → R) (z low high : Coeff B d) (hz : decode z = 0) (J : ℕ) :
    denote decode (padded z low high J) =
      Truncation.trunc J (C (decode low) + X*C (decode high)) := by
  change SubexponentialSAT.PolynomialAlgorithm.denote ((Constructor.coefficients z low high J).map decode) = _
  rw [coefficients_eq_padded]
  exact SubexponentialSAT.SubexpLocalCorrectionAlgebra.padded_denote decode z low high hz J

theorem constant_denote {B d : ℕ} {R : Type*} [CommRing R]
    (decode : Coeff B d → R) (z a : Coeff B d) (hz : decode z = 0) (J : ℕ) :
    denote decode (constant z a J) = Truncation.trunc J (C (decode a)) := by
  simpa only [constant, hz, map_zero, mul_zero, add_zero] using padded_denote decode z a z hz J

theorem linear_denote {B d : ℕ} {R : Type*} [CommRing R]
    (decode : Coeff B d → R) (z one a : Coeff B d)
    (hz : decode z = 0) (ho : decode one = 1) (J : ℕ) :
    denote decode (linear z one a J) = Truncation.trunc J (X + C (decode a)) := by
  simpa only [linear, ho, map_one, mul_one, add_comm] using padded_denote decode z a one hz J

theorem zero_denote {B d : ℕ} {R : Type*} [CommRing R]
    (decode : Coeff B d → R) (z : Coeff B d) (hz : decode z = 0) (J : ℕ) :
    denote decode (zero z J) = 0 := by
  simp [denote, zero, List.map_replicate, hz, SubexponentialSAT.SubexpConvolutionAlgebra.denote_replicate_zero]

theorem add_denote {B d J : ℕ} {R : Type*} [CommRing R]
    (ops : RepresentedRing (Coeff B d) R) (P Q : Poly B d J) :
    denote ops.decode (Fixed.add ops.program P Q) = denote ops.decode P + denote ops.decode Q :=
  DensePolynomialProgram.add_correct ops P.1 Q.1

theorem mul_denote {B d J : ℕ} {R : Type*} [CommRing R]
    (ops : RepresentedRing (Coeff B d) R) (P Q : Poly B d J) :
    denote ops.decode (Fixed.mul ops.program P Q) =
      Truncation.trunc J (denote ops.decode P * denote ops.decode Q) :=
  DensePolynomialProgram.result_correct ops J P.1 Q.1

theorem zero_encode {B d : ℕ} (z : Coeff B d)
    (hz : RingProgram.flat z = List.replicate (d*B) false) (J : ℕ) :
    Fixed.encode (zero z J) = List.replicate (J*(d*B)) false := by
  change DensePolynomialProgram.encode (List.replicate J z) = _
  induction J with
  | zero => simp [DensePolynomialProgram.encode]
  | succ J ih =>
      rw [List.replicate_succ, DensePolynomialProgram.encode_cons, hz, ih, ← List.replicate_add]
      congr 1
      ring

theorem head_split {B d J : ℕ} (P : Poly B d J) (hJ : 0 < J) :
    ∃ (c : Coeff B d) (rest : List (Coeff B d)),
      P.1 = c :: rest ∧ Fixed.encode P = RingProgram.flat c ++ DensePolynomialProgram.encode rest ∧
        rest.length + 1 = J := by
  cases hP : P.1 with
  | nil => have h := P.2; rw [hP] at h; simp at h; omega
  | cons c rest =>
      refine ⟨c, rest, rfl, ?_, ?_⟩
      · simp [Fixed.encode, hP, DensePolynomialProgram.encode_cons]
      · have h := P.2
        simpa [hP] using h

theorem head_decode {B d J : ℕ} {R : Type*} [CommRing R]
    (decode : Coeff B d → R) (P : Poly B d J) (c : Coeff B d)
    (rest : List (Coeff B d)) (hP : P.1 = c :: rest) :
    decode c = (denote decode P).coeff 0 := by
  simp [denote, hP, SubexponentialSAT.PolynomialAlgorithm.denote_cons]

theorem constant_zero {B d : ℕ} (z : Coeff B d) (J : ℕ) :
    constant z z J = zero z J := by
  apply Subtype.ext
  cases J with
  | zero => rfl
  | succ J => cases J <;> simp [constant, padded, zero, Constructor.coefficients, List.replicate_succ]

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

end OAI.Algorithms
