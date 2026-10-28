import OAI.AlgebraicGeometry.Comparison.Betti.SplitPolynomialPowers
import OAI.AlgebraicGeometry.Comparison.Betti.CompletionCompatibleEquiv

/-! # Split Coordinate Completion -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SplitCoordinateCompletion.AnalyticLocal

noncomputable section

/-! The completion of a ring with a split regular coordinate agrees
with the completion of the coefficient polynomial ring. -/

open _root_.Polynomial

variable {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
  (s : A →+* B) (r : B →+* A) (hrs : r.comp s = RingHom.id A)
  (t : B) (hrt : r t = 0) (ht : t ≠ 0)
  (hdivision : ∀ y : B, ∃ b : B, y = s (r y) + t * b)

def splitPowerQuotientEquiv (n : ℕ) :
    A[X] ⧸ (Ideal.span {(X : A[X])}) ^ n ≃+* B ⧸ (Ideal.span {t}) ^ n :=
  (Ideal.quotientEquivAlgOfEq A[X] (Ideal.span_singleton_pow (X : A[X]) n)).toRingEquiv.trans
    ((SplitPolynomialPowers.AnalyticLocal.splitPolynomialQuotientEquiv s r hrs t hrt ht hdivision n).trans
      (Ideal.quotientEquivAlgOfEq B (Ideal.span_singleton_pow t n).symm).toRingEquiv)

theorem splitPowerQuotientEquiv_mk (n : ℕ) (P : A[X]) :
    splitPowerQuotientEquiv s r hrs t hrt ht hdivision n (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk ((Ideal.span {t}) ^ n) (P.eval₂ s t) := rfl

theorem splitPowerQuotientEquiv_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {t}) h).comp
      (splitPowerQuotientEquiv s r hrs t hrt ht hdivision n).toRingHom =
    (splitPowerQuotientEquiv s r hrs t hrt ht hdivision m).toRingHom.comp
      (Ideal.Quotient.factorPow (Ideal.span {(X : A[X])}) h) := by
  apply RingHom.ext
  intro z
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

def splitCoordinateCompletionEquiv :
    AdicCompletion (Ideal.span {(X : A[X])}) A[X] ≃+* AdicCompletion (Ideal.span {t}) B :=
  CompletionCompatibleEquiv.AnalyticLocal.completionCompatibleEquiv _ _ (splitPowerQuotientEquiv s r hrs t hrt ht hdivision)
    (splitPowerQuotientEquiv_compatible s r hrs t hrt ht hdivision)

theorem splitCoordinateCompletionEquiv_of (P : A[X]) :
    splitCoordinateCompletionEquiv s r hrs t hrt ht hdivision (AdicCompletion.of _ A[X] P) =
      AdicCompletion.of (Ideal.span {t}) B (P.eval₂ s t) :=
  CompletionCompatibleEquiv.AnalyticLocal.completionCompatibleEquiv_of _ _ _ _ (eval₂RingHom s t) (fun _ _ => rfl) P

def splitCoordinateCompletionAlgEquiv [Algebra A[X] B]
    (hAlg : algebraMap A[X] B = eval₂RingHom s t) :
    AdicCompletion (Ideal.span {(X : A[X])}) A[X] ≃ₐ[A[X]] AdicCompletion (Ideal.span {t}) B :=
  CompletionCompatibleEquiv.AnalyticLocal.completionCompatibleAlgEquiv _ _ (splitPowerQuotientEquiv s r hrs t hrt ht hdivision)
    (splitPowerQuotientEquiv_compatible s r hrs t hrt ht hdivision) (by
      intro n P
      rw [hAlg]
      rfl)

end

end OAI.AlgebraicGeometry.Comparison.Betti.SplitCoordinateCompletion.AnalyticLocal
