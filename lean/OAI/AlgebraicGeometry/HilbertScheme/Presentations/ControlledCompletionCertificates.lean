import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ControlledExponentBound
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.Polynomials

/-! # Controlled Completion Certificates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ControlledCompletionCertificates.GradedHilbert

noncomputable section

/-! Finite certificates for controlled additions of homogeneous ideal elements with genuinely new leading monomials. -/

open _root_.MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}
variable (m : MonomialOrder (Fin (n + 1))) (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (D : ℕ)

structure ControlledCompletionCertificate (k : ℕ) where
  value : Fin k → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n
  nonzero : ∀ i, value i ≠ 0
  mem_ideal : ∀ i, value i ∈ I
  homogeneous : ∀ i, ∃ d ≤ D * 2 ^ (i.val + 1), (value i).IsHomogeneous d
  new_leading : ∀ i j, i < j → ¬ m.degree (value i) ≤ m.degree (value j)

def polynomialCompletionHorizon (n D : ℕ) : ℕ :=
  ControlledExponentBound.MonomialFiniteness.controlledExponentHorizon (n + 1) (fun k => D * 2 ^ (k + 1))

theorem ControlledCompletionCertificate.length_lt {k : ℕ} (C : ControlledCompletionCertificate m I D k) :
    k < polynomialCompletionHorizon n D := by
  apply ControlledExponentBound.MonomialFiniteness.controlled_bad_exponent_length (n + 1) (fun j => D * 2 ^ (j + 1)) k
    (fun i j => m.degree (C.value i) j)
  · intro i j
    obtain ⟨d, hd, hhom⟩ := C.homogeneous i
    have hlead := Homogeneous.Polynomials.GradedHilbert.homogeneous_leadingDegree m hhom (C.nonzero i)
    exact (Finsupp.le_degree _ _).trans (hlead ▸ hd)
  · intro i j hij
    exact C.new_leading i j hij

def ControlledCompletionCertificate.empty : ControlledCompletionCertificate m I D 0 where
  value := Fin.elim0
  nonzero i := Fin.elim0 i
  mem_ideal i := Fin.elim0 i
  homogeneous i := Fin.elim0 i
  new_leading i := Fin.elim0 i

def ControlledCompletionCertificate.append {k : ℕ} (C : ControlledCompletionCertificate m I D k)
    (r : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hr0 : r ≠ 0) (hrI : r ∈ I)
    (hrhom : ∃ d ≤ D * 2 ^ (k + 1), r.IsHomogeneous d)
    (hrnew : ∀ i, ¬ m.degree (C.value i) ≤ m.degree r) : ControlledCompletionCertificate m I D (k + 1) where
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

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ControlledCompletionCertificates.GradedHilbert
