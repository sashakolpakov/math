import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotient Points -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.QuotientPoints.PolynomialProjective

noncomputable section

/-! Polynomial quotient algebras represent their actual equation solutions. -/

open _root_.MvPolynomial

universe u v w

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B] {σ : Type w}

theorem quotientAlgHom_aeval (J : Ideal (MvPolynomial σ R))
    (f : (MvPolynomial σ R ⧸ J) →ₐ[R] B) (p : MvPolynomial σ R) :
    aeval (fun i => f (Ideal.Quotient.mk J (X i))) p = f (Ideal.Quotient.mk J p) :=
  AlgHom.congr_fun (aeval_unique (f.comp (Ideal.Quotient.mkₐ R J))).symm p

def polynomialQuotientPointEquiv (J : Ideal (MvPolynomial σ R)) :
    ((MvPolynomial σ R ⧸ J) →ₐ[R] B) ≃ {p : σ → B // ∀ f ∈ J, aeval p f = 0} where
  toFun f := ⟨fun i => f (Ideal.Quotient.mk J (X i)), by
    intro p hp
    rw [quotientAlgHom_aeval, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]⟩
  invFun p := Ideal.Quotient.liftₐ J (aeval p.val) p.property
  left_inv f := by
    apply AlgHom.ext
    intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    change aeval (fun i => f (Ideal.Quotient.mk J (X i))) p = f (Ideal.Quotient.mk J p)
    exact quotientAlgHom_aeval J f p
  right_inv p := by
    apply Subtype.ext
    funext i
    exact aeval_X p.val i

theorem polynomialQuotientPointEquiv_apply (J : Ideal (MvPolynomial σ R))
    (f : (MvPolynomial σ R ⧸ J) →ₐ[R] B) (i : σ) :
    (polynomialQuotientPointEquiv J f).val i = f (Ideal.Quotient.mk J (X i)) := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.QuotientPoints.PolynomialProjective
