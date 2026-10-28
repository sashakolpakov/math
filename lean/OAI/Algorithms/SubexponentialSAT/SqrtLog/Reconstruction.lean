import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTExecution

namespace OAI.Algorithms

/-!
# Explicit reconstruction for independently chosen node and jet counts

This interface reuses the audited dense-list Hermite program. Its inverse
table is computed by finite powers and geometric sums. No interpolation
choice, scalar-inverse oracle, or field assumption on the coefficient ring
occurs in `run`. The represented arithmetic callbacks carry their own costs.
-/

namespace SubexponentialSAT.SqrtLog.Reconstruction

/-- Execute the complete dense reconstruction, including inverse preparation. -/
def run {C : Type*} (ops : SubexpSymbolicCost.RingProgram C)
    {Q : ℕ} (nodes : Fin Q → C) (residueSize precision order : ℕ)
    (jets : Fin Q → List C) : List C × ℕ :=
  SubexpCRTExecution.completeProgram ops nodes residueSize precision order jets

noncomputable section

open Polynomial

variable {C A : Type*} [CommRing A]

/-- The node evaluator can supply either this identity or coefficient identities. -/
def HasJets (ops : SubexpSymbolicCost.RepresentedRing C A)
    {Q : ℕ} (nodes : Fin Q → C) (order : ℕ)
    (jets : Fin Q → List C) (target : Polynomial A) : Prop :=
  ∀ i, Truncation.trunc order
    (PolynomialAlgorithm.denote ((jets i).map ops.decode)) =
      JetCRT.jet (ops.decode (nodes i)) order target

theorem hasJets_of_coefficients (ops : SubexpSymbolicCost.RepresentedRing C A)
    {Q : ℕ} (nodes : Fin Q → C) (order : ℕ)
    (jets : Fin Q → List C) (target : Polynomial A)
    (h : ∀ i n, n < order →
      (PolynomialAlgorithm.denote ((jets i).map ops.decode)).coeff n =
        (target.comp (X + Polynomial.C (ops.decode (nodes i)))).coeff n) :
    HasJets ops nodes order jets target := by
  intro i
  rw [TruncatedInverse.jet_eq_trunc]
  ext n
  by_cases hn : n < order
  · simpa only [Truncation.coeff_trunc, ite_eq_left hn] using h i n hn
  · simp only [Truncation.coeff_trunc, ite_eq_right hn]

/-- Full reconstruction from finite-ring jets; the residue field is used only
to certify the inverses computed inside the executable program. -/
theorem run_correct (ops : SubexpSymbolicCost.RepresentedRing C A)
    {E : Type*} [Field E] [Fintype E]
    {Q : ℕ} [NeZero Q] (nodes : Fin Q → C)
    (rho : A →+* E) (residueSize : ℕ) (hcard : Fintype.card E = residueSize)
    (pi : A) (precision : ℕ) (hnil : pi ^ precision = 0)
    (hker : ∀ x, rho x = 0 → pi ∣ x)
    (hnodes : Function.Injective (fun i => rho (ops.decode (nodes i))))
    (order : ℕ) (horder : 0 < order) (jets : Fin Q → List C)
    (target : Polynomial A) (hdegree : target.natDegree < Q * order)
    (hjets : HasJets ops nodes order jets target)
    (hlength : ∀ i, (jets i).length ≤ order) :
    PolynomialAlgorithm.denote
      ((run ops.program nodes residueSize precision order jets).1.map ops.decode) = target := by
  exact SubexpCRTExecution.completeProgram_correct ops nodes rho residueSize hcard
    pi precision hnil hker hnodes order horder jets target hdegree hjets hlength

/-- The first returned coefficient is the value needed for exact counting. -/
theorem run_head_eq_eval_zero (ops : SubexpSymbolicCost.RepresentedRing C A)
    {Q : ℕ} (nodes : Fin Q → C) (residueSize precision order : ℕ)
    (jets : Fin Q → List C) (target : Polynomial A)
    (h : PolynomialAlgorithm.denote
      ((run ops.program nodes residueSize precision order jets).1.map ops.decode) = target) :
    ops.decode ((run ops.program nodes residueSize precision order jets).1.headD
      ops.zeroRun.1) = target.eval 0 := by
  rw [← coeff_zero_eq_eval_zero]
  exact SubexpCRTExecution.head_decode_of_denote_eq ops _ target h

/-- Only a linear number of output coefficients is retained. -/
theorem run_length (ops : SubexpSymbolicCost.RepresentedRing C A)
    {Q : ℕ} (nodes : Fin Q → C) (residueSize precision order : ℕ)
    (jets : Fin Q → List C) :
    (run ops.program nodes residueSize precision order jets).1.length ≤
      4 * (Q + 1) * (order + 1) :=
  SubexpCRTExecution.completeProgram_length ops nodes residueSize precision order jets

end
end SubexponentialSAT.SqrtLog.Reconstruction

end OAI.Algorithms
