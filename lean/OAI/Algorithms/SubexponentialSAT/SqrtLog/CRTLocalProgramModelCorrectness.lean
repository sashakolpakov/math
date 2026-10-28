import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramModel

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Model
open Polynomial
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram

variable {B d J : ℕ} {R : Type*} [CommRing R]

def scalarMul (ops : RepresentedRing (Coeff B d) R) (a b : Coeff B d) : Coeff B d :=
  (ops.program.mulRun a b).1

def scalarAdd (ops : RepresentedRing (Coeff B d) R) (a b : Coeff B d) : Coeff B d :=
  (ops.program.addRun a b).1

def inverseCoefficient (ops : RepresentedRing (Coeff B d) R)
    (minusOne c : Coeff B d) (q t : ℕ) : Coeff B d :=
  inverseValue (scalarMul ops) (scalarAdd ops) ops.zeroRun.1 ops.oneRun.1 minusOne c (q-2) t

def corrected (ops : RepresentedRing (Coeff B d) R) (minusOne c : Coeff B d)
    (q t : ℕ) (factor jet : Poly B d J) : Poly B d J :=
  let z := ops.zeroRun.1
  let a := inverseCoefficient ops minusOne c q t
  correctionValue (Fixed.mul ops.program) (Fixed.add ops.program)
    (zero z J) (constant z ops.oneRun.1 J)
    (constant z (scalarMul ops a minusOne) J) (constant z a J) factor jet J

theorem corrected_denote (ops : RepresentedRing (Coeff B d) R)
    (minusOne c : Coeff B d) (q t : ℕ) (factor jet : Poly B d J)
    (P : R[X]) (hn : ops.decode minusOne = -1)
    (hfactor : denote ops.decode factor = Truncation.trunc J P) :
    denote ops.decode (corrected ops minusOne c q t factor jet) =
      TruncatedInverse.correctedJet P (denote ops.decode jet)
        (ops.decode (inverseCoefficient ops minusOne c q t)) J := by
  apply correctionValue_denote J _ _ _ _ _ _ _ _ (denote ops.decode) P _ _
  · exact zero_denote ops.decode ops.zeroRun.1 ops.zero_correct J
  · simpa only [ops.one_correct, map_one] using
      constant_denote ops.decode ops.zeroRun.1 ops.oneRun.1 ops.zero_correct J
  · have h := constant_denote ops.decode ops.zeroRun.1
      (scalarMul ops (inverseCoefficient ops minusOne c q t) minusOne) ops.zero_correct J
    simpa only [scalarMul, RepresentedRing.program, ops.mul_correct, hn, mul_neg_one] using h
  · exact constant_denote ops.decode ops.zeroRun.1 _ ops.zero_correct J
  · exact hfactor
  · rfl
  · exact add_denote ops
  · exact mul_denote ops

theorem inverseCoefficient_decode (ops : RepresentedRing (Coeff B d) R)
    (minusOne c : Coeff B d) (hn : ops.decode minusOne = -1) (q t : ℕ) :
    ops.decode (inverseCoefficient ops minusOne c q t) =
      (SubexponentialSAT.SubexpResidueInverse.inverseWithCost q t (ops.decode c)).1 := by
  exact inverseValue_decode ops.decode (scalarMul ops) (scalarAdd ops)
    ops.mul_correct ops.add_correct ops.zeroRun.1 ops.oneRun.1 minusOne c
    ops.zero_correct ops.one_correct hn q t

theorem inverseCoefficient_correct {E : Type*} [Field E] [Fintype E]
    (ops : RepresentedRing (Coeff B d) R) (minusOne c : Coeff B d)
    (hn : ops.decode minusOne = -1) (rho : R →+* E) (q : ℕ) (hq : Fintype.card E = q)
    (pi : R) (t : ℕ) (hpi : pi^t = 0) (hker : ∀ x, rho x = 0 → pi ∣ x)
    (P : R[X]) (hc : ops.decode c = P.coeff 0) (hne : rho (P.coeff 0) ≠ 0) :
    ops.decode (inverseCoefficient ops minusOne c q t) * P.coeff 0 = 1 := by
  rw [inverseCoefficient_decode ops minusOne c hn q t, hc]
  exact SubexponentialSAT.SubexpResidueInverse.inverseWithCost_correct rho q hq pi t hpi hker _ hne

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

end OAI.Algorithms
