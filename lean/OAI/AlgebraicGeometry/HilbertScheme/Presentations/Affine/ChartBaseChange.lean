import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartPresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange

/-! # Chart Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartBaseChange.GradedHilbert

noncomputable section

/-!
Affine projective charts commute with arbitrary change of coefficient
ring. The proof uses the concrete equation X_i = 1 and the tensor-product
presentation of polynomial quotients.
-/

open _root_.MvPolynomial TensorProduct _root_.HomogeneousLocalization

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] {n : ℕ}

theorem polynomialIdeal_tensor_map (J : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) :
    J.map (MvPolynomial.map (algebraMap R S)) =
      (J.map (Algebra.TensorProduct.includeRight (A := S) (R := R))).map
        (MvPolynomial.algebraTensorAlgEquiv R S).toRingHom := by
  have h : (MvPolynomial.algebraTensorAlgEquiv (σ := Fin (n + 1)) R S).toRingHom.comp
      (Algebra.TensorProduct.includeRight (A := S) (R := R)).toRingHom =
        MvPolynomial.map (algebraMap R S) := by
    apply RingHom.ext
    intro f
    change MvPolynomial.algebraTensorAlgEquiv R S (1 ⊗ₜ[R] f) = _
    simpa only [one_smul] using MvPolynomial.algebraTensorAlgEquiv_tmul R S 1 f
  exact (congrArg (fun f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n →+* Hilbert.Polynomial.GradedHilbert.CoordinateRing S n => J.map f) h).symm.trans
    (Ideal.map_map (Algebra.TensorProduct.includeRight (A := S) (R := R)).toRingHom
      (MvPolynomial.algebraTensorAlgEquiv R S).toRingHom).symm

def polynomialQuotientBaseChangeEquiv (J : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) :
    S ⊗[R] (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ J) ≃ₐ[S]
      Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ J.map (MvPolynomial.map (algebraMap R S)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) S J).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S) (polynomialIdeal_tensor_map J))

theorem polynomialQuotientBaseChangeEquiv_tmul (J : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n))
    (s : S) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    polynomialQuotientBaseChangeEquiv J (s ⊗ₜ[R] Ideal.Quotient.mk J f) =
      Ideal.Quotient.mk (J.map (MvPolynomial.map (algebraMap R S)))
        (s • MvPolynomial.map (algebraMap R S) f) := by
  change Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S)
    (polynomialIdeal_tensor_map J)
      ((Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) S J)
        (s ⊗ₜ[R] Ideal.Quotient.mk J f)) = _
  erw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlg_mk,
    MvPolynomial.algebraTensorAlgEquiv_tmul]

theorem affineChartIdeal_baseChange (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    ChartPresentation.GradedHilbert.affineChartIdeal (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) i =
      (ChartPresentation.GradedHilbert.affineChartIdeal I i).map (MvPolynomial.map (algebraMap R S)) := by
  change I.toIdeal.map (MvPolynomial.map (algebraMap R S)) ⊔ Ideal.span {X i - 1} =
    (I.toIdeal ⊔ Ideal.span {X i - 1}).map (MvPolynomial.map (algebraMap R S))
  rw [Ideal.map_sup, Ideal.map_span]
  simp only [Set.image_singleton, map_sub, MvPolynomial.map_X, map_one]

/-- Base change of the actual affine coordinate ring of a projective
closed subscheme. No flatness of the coefficient map is required. -/
def affineChartBaseChangeEquiv (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    S ⊗[R] HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) ≃ₐ[S]
      HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I))
        (Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (X i)) := by
  let e₁ := Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
    (ChartPresentation.GradedHilbert.affineChartPresentationAlgEquiv I i).symm
  let e₂ := polynomialQuotientBaseChangeEquiv (S := S) (ChartPresentation.GradedHilbert.affineChartIdeal I i)
  let e₃ := Ideal.quotientEquivAlgOfEq S (affineChartIdeal_baseChange (S := S) I i).symm
  exact e₁.trans (e₂.trans (e₃.trans (ChartPresentation.GradedHilbert.affineChartPresentationAlgEquiv (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal I) i)))

theorem affineChartBaseChangeEquiv_tmul (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) (s : S) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    affineChartBaseChangeEquiv (S := S) I i (s ⊗ₜ[R] ChartPresentation.GradedHilbert.affineChartMap I i f) =
      ChartPresentation.GradedHilbert.affineChartMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) i
        (s • MvPolynomial.map (algebraMap R S) f) := by
  simp only [affineChartBaseChangeEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change (ChartPresentation.GradedHilbert.affineChartPresentationAlgEquiv (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) i)
    ((Ideal.quotientEquivAlgOfEq S (affineChartIdeal_baseChange (S := S) I i).symm)
      (polynomialQuotientBaseChangeEquiv (S := S) (ChartPresentation.GradedHilbert.affineChartIdeal I i)
        (s ⊗ₜ[R] (ChartPresentation.GradedHilbert.affineChartPresentationAlgEquiv I i).symm (ChartPresentation.GradedHilbert.affineChartMap I i f)))) = _
  rw [ChartPresentation.GradedHilbert.affineChartPresentationAlgEquiv_symm_map I i f]
  rw [polynomialQuotientBaseChangeEquiv_tmul (S := S) (ChartPresentation.GradedHilbert.affineChartIdeal I i) s f]
  erw [Ideal.quotientEquivAlgOfEq_mk S (affineChartIdeal_baseChange (S := S) I i).symm]
  exact ChartPresentation.GradedHilbert.affineChartPresentationAlgEquiv_mk _ _ _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartBaseChange.GradedHilbert
