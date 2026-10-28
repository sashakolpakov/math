import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramModelCorrectness
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCorrectionAlgebra

namespace OAI.Algorithms

/-! The physical local factor and correction have the canonical Hermite
meaning independently of the encoded representative of their head word. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue

open SubexponentialSAT Polynomial
open SubexpSymbolicCost DensePolynomialProgram
open CRTLocalProgram

variable {B d J Q : ℕ} {R : Type*} [CommRing R]

def factorCode (ops : RepresentedRing (Coeff B d) R) (minusOne : Coeff B d)
    (nodes : Fin Q → Coeff B d) (J : ℕ) (i : Fin Q) : Model.Poly B d J :=
  ((List.ofFn nodes).eraseIdx i.val).foldl
    (localUpdate (Model.scalarMul ops) (Model.scalarAdd ops) (Fixed.mul ops.program)
      (fun c => Model.linear ops.zeroRun.1 ops.oneRun.1 c J) (nodes i) minusOne J)
    (Model.constant ops.zeroRun.1 ops.oneRun.1 J)

noncomputable def inverse (theta : Fin Q → R) (q t J : ℕ) (i : Fin Q) : R :=
  (SubexpResidueInverse.inverseWithCost q t
    ((Truncation.trunc J (TruncatedInverse.localFactor theta J i)).coeff 0)).1

theorem factorCode_denote (ops : RepresentedRing (Coeff B d) R) (minusOne : Coeff B d)
    (hn : ops.decode minusOne = -1) (nodes : Fin Q → Coeff B d) (J : ℕ) (i : Fin Q) :
    Model.denote ops.decode (factorCode ops minusOne nodes J i) =
      Truncation.trunc J (TruncatedInverse.localFactor (fun j => ops.decode (nodes j)) J i) := by
  have hone : Model.denote ops.decode (Model.constant ops.zeroRun.1 ops.oneRun.1 J) =
      Truncation.trunc J (1 : R[X]) := by
    simpa [ops.one_correct] using Model.constant_denote ops.decode ops.zeroRun.1 ops.oneRun.1 ops.zero_correct J
  have h := localScan_localFactor ops.decode (Model.denote ops.decode)
    (Model.scalarMul ops) (Model.scalarAdd ops) (Fixed.mul ops.program)
    ops.mul_correct ops.add_correct J
    (fun c => Model.linear ops.zeroRun.1 ops.oneRun.1 c J)
    (Model.mul_denote ops) (fun c => Model.linear_denote ops.decode ops.zeroRun.1 ops.oneRun.1 c
      ops.zero_correct ops.one_correct J) minusOne hn nodes i
    (List.replicate i.val false) (by simp) (Model.constant ops.zeroRun.1 ops.oneRun.1 J) hone
  simpa only [SubexpNodeScanControl.run_skip_index, List.length_replicate, factorCode] using h

theorem corrected_denote (ops : RepresentedRing (Coeff B d) R) (minusOne : Coeff B d)
    (hn : ops.decode minusOne = -1) (nodes : Fin Q → Coeff B d)
    (q t J : ℕ) (jets : Fin Q → Model.Poly B d J) (i : Fin Q)
    (c : Coeff B d) (rest : List (Coeff B d))
    (hhead : (factorCode ops minusOne nodes J i).1 = c :: rest) :
    Model.denote ops.decode (Model.corrected ops minusOne c q t
      (factorCode ops minusOne nodes J i) (jets i)) =
      TruncatedInverse.correction (fun j => ops.decode (nodes j)) J
        (inverse (fun j => ops.decode (nodes j)) q t J)
        (fun j => Model.denote ops.decode (jets j)) i := by
  have hf := factorCode_denote ops minusOne hn nodes J i
  have hc := Model.head_decode ops.decode (factorCode ops minusOne nodes J i) c rest hhead
  rw [hf] at hc
  rw [Model.corrected_denote ops minusOne c q t _ _ _ hn hf,
    Model.inverseCoefficient_decode ops minusOne c hn q t, hc]
  rfl

theorem inverse_correct {E : Type*} [Field E] [Fintype E]
    (rho : R →+* E) (theta : Fin Q → R) (q : ℕ) (hq : Fintype.card E = q)
    (pi : R) (t : ℕ) (hpi : pi^t = 0) (hker : ∀ x, rho x = 0 → pi ∣ x)
    (hnodes : Function.Injective (fun i => rho (theta i))) (J : ℕ) (hJ : 0 < J) (i : Fin Q) :
    inverse theta q t J i * (TruncatedInverse.localFactor theta J i).coeff 0 = 1 :=
  SubexpLocalCorrectionAlgebra.computed_constantInverse rho q hq pi t hpi hker theta hnodes J hJ i

end SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue

end OAI.Algorithms
