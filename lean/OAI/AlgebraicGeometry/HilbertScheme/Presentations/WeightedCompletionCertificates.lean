import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ControlledCompletionCertificates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedPolynomials

/-! # Weighted Completion Certificates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedCompletionCertificates.GradedHilbert

noncomputable section

/-! Finite certificates for controlled additions of homogeneous ideal elements with genuinely new leading monomials. -/

open _root_.MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}
variable (w : Fin (n + 1) → ℕ) (m : MonomialOrder (Fin (n + 1))) (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (D : ℕ)

structure WeightedCompletionCertificate (k : ℕ) where
  value : Fin k → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n
  nonzero : ∀ i, value i ≠ 0
  mem_ideal : ∀ i, value i ∈ I
  homogeneous : ∀ i, ∃ d ≤ D * 2 ^ (i.val + 1), (value i).IsWeightedHomogeneous w d
  new_leading : ∀ i j, i < j → ¬ m.degree (value i) ≤ m.degree (value j)

variable (hw : ∀ i, w i ≠ 0)

include hw in
theorem WeightedCompletionCertificate.length_lt {k : ℕ} (C : WeightedCompletionCertificate w m I D k) :
    k < ControlledCompletionCertificates.GradedHilbert.polynomialCompletionHorizon n D := by
  apply ControlledExponentBound.MonomialFiniteness.controlled_bad_exponent_length (n + 1) (fun j => D * 2 ^ (j + 1)) k
    (fun i j => m.degree (C.value i) j)
  · intro i j
    obtain ⟨d, hd, hhom⟩ := C.homogeneous i
    have hlead := WeightedPolynomials.GradedHilbert.weighted_leadingDegree w m hhom (C.nonzero i)
    exact (Finsupp.le_weight w (hw j) _).trans (hlead ▸ hd)
  · intro i j hij
    exact C.new_leading i j hij

def WeightedCompletionCertificate.empty : WeightedCompletionCertificate w m I D 0 where
  value := Fin.elim0
  nonzero i := Fin.elim0 i
  mem_ideal i := Fin.elim0 i
  homogeneous i := Fin.elim0 i
  new_leading i := Fin.elim0 i

def WeightedCompletionCertificate.append {k : ℕ} (C : WeightedCompletionCertificate w m I D k)
    (r : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hr0 : r ≠ 0) (hrI : r ∈ I)
    (hrhom : ∃ d ≤ D * 2 ^ (k + 1), r.IsWeightedHomogeneous w d)
    (hrnew : ∀ i, ¬ m.degree (C.value i) ≤ m.degree r) : WeightedCompletionCertificate w m I D (k + 1) where
  value := Fin.lastCases r C.value
  nonzero i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last] using hr0
    · simpa only [Fin.lastCases_castSucc] using C.nonzero j
  mem_ideal i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last] using hrI
    · simpa only [Fin.lastCases_castSucc] using C.mem_ideal j
  homogeneous i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last, Fin.val_last] using hrhom
    · simpa only [Fin.lastCases_castSucc, Fin.val_castSucc] using C.homogeneous j
  new_leading i j := by
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · intro hij
      exact (not_lt_of_ge (Fin.le_last j) hij).elim
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro _
        simpa only [Fin.lastCases_castSucc, Fin.lastCases_last] using hrnew i'
      · intro hij
        simpa only [Fin.lastCases_castSucc] using C.new_leading i' j' hij

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedCompletionCertificates.GradedHilbert
