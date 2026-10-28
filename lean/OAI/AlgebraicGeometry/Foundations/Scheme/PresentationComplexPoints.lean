import OAI.AlgebraicGeometry.Foundations.Scheme.QuotientComplexPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation
import Mathlib.RingTheory.Nullstellensatz

/-! # Presentation Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.PresentationComplexPoints

noncomputable section

/-!
# Polynomial presentation coordinates for complex points

The points of `ℂ[X] / I` are identified with tuples satisfying the actual ideal
relations. Coordinate and evaluation formulas identify this bijection with the
usual one, and substitution of polynomials is compatible with quotient maps.
The existing polynomial-character equivalence is reused; this file installs no
topology and does not assert any analytification or smooth-chart theorem.
-/

universe u v w

variable {σ : Type u} {τ : Type v} {κ : Type w}

/-- Polynomial characters vanishing on an ideal are exactly tuples in its usual zero locus. -/
def polynomialIdealZeroLocusEquiv (I : Ideal (MvPolynomial σ ℂ)) :
    QuotientComplexPoints.affineIdealZeroLocus I ≃ MvPolynomial.zeroLocus ℂ I where
  toFun x := ⟨ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv σ x.val, by
    intro p hp
    simpa only [MvPolynomial.aeval_eq_eval, ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv_eval] using x.property p hp⟩
  invFun z := ⟨(ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv σ).symm z.val, z.property⟩
  left_inv x := Subtype.ext ((ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv σ).symm_apply_apply x.val)
  right_inv z := Subtype.ext ((ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv σ).apply_symm_apply z.val)

/-- Complex points of a polynomial quotient are precisely the solutions of its ideal. -/
def presentationComplexPointsEquiv (I : Ideal (MvPolynomial σ ℂ)) :
    AffineComplexPoints.affineComplexPoints (MvPolynomial σ ℂ ⧸ I) ≃ MvPolynomial.zeroLocus ℂ I :=
  (QuotientComplexPoints.quotientComplexPointsEquiv I).trans (polynomialIdealZeroLocusEquiv I)

/-- Coordinates are the values of the residue classes of the polynomial variables. -/
@[simp] theorem presentationComplexPointsEquiv_apply
    (I : Ideal (MvPolynomial σ ℂ))
    (x : AffineComplexPoints.affineComplexPoints (MvPolynomial σ ℂ ⧸ I)) (i : σ) :
    (presentationComplexPointsEquiv I x).val i =
      x (Ideal.Quotient.mk I (MvPolynomial.X i)) := rfl

/-- Evaluating any polynomial in the coordinates recovers its residue-class value. -/
@[simp] theorem presentationComplexPointsEquiv_eval
    (I : Ideal (MvPolynomial σ ℂ))
    (x : AffineComplexPoints.affineComplexPoints (MvPolynomial σ ℂ ⧸ I)) (p : MvPolynomial σ ℂ) :
    MvPolynomial.eval (presentationComplexPointsEquiv I x).val p =
      x (Ideal.Quotient.mk I p) :=
  ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointEquiv_eval (QuotientComplexPoints.quotientComplexPointsEquiv I x).val p

/-- The inverse bijection evaluates representatives of quotient elements. -/
@[simp] theorem presentationComplexPointsEquiv_symm_mk
    (I : Ideal (MvPolynomial σ ℂ)) (z : MvPolynomial.zeroLocus ℂ I)
    (p : MvPolynomial σ ℂ) :
    (presentationComplexPointsEquiv I).symm z (Ideal.Quotient.mk I p) =
      MvPolynomial.eval z.val p := by
  simpa only [Equiv.apply_symm_apply] using
    (presentationComplexPointsEquiv_eval I ((presentationComplexPointsEquiv I).symm z) p).symm

/-- Morphisms of polynomial presentations induce the expected polynomial maps on coordinates. -/
theorem presentationComplexPointsEquiv_quotientMap_apply
    (I : Ideal (MvPolynomial σ ℂ)) (J : Ideal (MvPolynomial τ ℂ))
    (f : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ) (h : I ≤ J.comap f)
    (x : AffineComplexPoints.affineComplexPoints (MvPolynomial τ ℂ ⧸ J)) (i : σ) :
    (presentationComplexPointsEquiv I (x.comp (Ideal.quotientMapₐ J f h))).val i =
      MvPolynomial.eval (presentationComplexPointsEquiv J x).val (f (MvPolynomial.X i)) := by
  simp only [presentationComplexPointsEquiv_apply, AlgHom.comp_apply,
    Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
    presentationComplexPointsEquiv_eval]

/-- Replacing a family of equations by its generated ideal does not change its solutions. -/
def relationsZeroLocusEquiv (F : κ → MvPolynomial σ ℂ) :
    MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range F)) ≃
      {z : σ → ℂ // ∀ j, MvPolynomial.eval z (F j) = 0} where
  toFun z := ⟨z.val, by
    intro j
    exact z.property (F j) (Ideal.subset_span ⟨j, rfl⟩)⟩
  invFun z := ⟨z.val, by
    rw [MvPolynomial.zeroLocus_span]
    rintro p ⟨j, rfl⟩
    exact z.property j⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Complex points of an algebra given by specified polynomial relations are their solutions. -/
def equationsComplexPointsEquiv (F : κ → MvPolynomial σ ℂ) :
    AffineComplexPoints.affineComplexPoints (MvPolynomial σ ℂ ⧸ Ideal.span (Set.range F)) ≃
      {z : σ → ℂ // ∀ j, MvPolynomial.eval z (F j) = 0} :=
  (presentationComplexPointsEquiv (Ideal.span (Set.range F))).trans (relationsZeroLocusEquiv F)

/-- The explicit coordinate formula remains unchanged for a family of defining equations. -/
@[simp] theorem equationsComplexPointsEquiv_apply (F : κ → MvPolynomial σ ℂ)
    (x : AffineComplexPoints.affineComplexPoints (MvPolynomial σ ℂ ⧸ Ideal.span (Set.range F))) (i : σ) :
    (equationsComplexPointsEquiv F x).val i =
      x (Ideal.Quotient.mk (Ideal.span (Set.range F)) (MvPolynomial.X i)) := rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme.PresentationComplexPoints
