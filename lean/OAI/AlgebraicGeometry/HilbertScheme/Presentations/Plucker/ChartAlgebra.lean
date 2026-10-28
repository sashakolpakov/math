import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartPoints
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ChartPresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.QuotientPoints

/-! # Chart Algebra -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartAlgebra.Grassmannian

noncomputable section

/-!
The actual homogeneous-localization algebras on the Plücker projective
charts represent normalized quotient matrices. This is a natural
equivalence of algebra-valued points, with an explicit coordinate formula.
-/

open _root_.MvPolynomial

universe u v w z

variable {R : Type u} [CommRing R] {B : Type z} [CommRing B] [Algebra R B]
variable {ι : Type v} {ν : Type w} [Fintype ι] [DecidableEq ι]

abbrev pluckerAffineChartAlgebra (a : ι → ν) :=
  MvPolynomial (ι → ν) R ⧸ Polynomial.ChartPresentation.PolynomialProjective.affineChartIdeal (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a

theorem pluckerAffineChart_equations_iff (a : ι → ν) (p : (ι → ν) → B) :
    (∀ f ∈ Polynomial.ChartPresentation.PolynomialProjective.affineChartIdeal (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a, aeval p f = 0) ↔
      p a = 1 ∧ ∀ f ∈ Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν), eval₂ (algebraMap R B) p f = 0 := by
  constructor
  · intro h
    have hI : (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)).toIdeal ≤
        Polynomial.ChartPresentation.PolynomialProjective.affineChartIdeal (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a := le_sup_left
    have hJ : Ideal.span {X a - 1} ≤
        Polynomial.ChartPresentation.PolynomialProjective.affineChartIdeal (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a := le_sup_right
    refine ⟨?_, fun f hf => h f (hI hf)⟩
    have hx := h (X a - 1) (hJ (Ideal.subset_span (Set.mem_singleton _)))
    simpa only [map_sub, aeval_X, map_one, sub_eq_zero] using hx
  · rintro ⟨ha, hI⟩
    have hker : Polynomial.ChartPresentation.PolynomialProjective.affineChartIdeal (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a ≤
        RingHom.ker (aeval p).toRingHom := by
      apply sup_le
      · intro f hf
        exact hI f hf
      · apply Ideal.span_le.mpr
        rintro f (rfl : f = X a - 1)
        change aeval p (X a - 1) = 0
        rw [map_sub, aeval_X, map_one, ha, sub_self]
    exact fun f hf => hker hf

def pluckerAffineChartAlgebraPointEquiv (a : ι → ν) :
    (pluckerAffineChartAlgebra (R := R) a →ₐ[R] B) ≃
      {Q : Matrix ι ν B // Normalized.Matrices.Grassmannian.IsNormalized a Q} :=
  (Polynomial.QuotientPoints.PolynomialProjective.polynomialQuotientPointEquiv (Polynomial.ChartPresentation.PolynomialProjective.affineChartIdeal (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a)).trans
    ((Equiv.subtypeEquivRight (pluckerAffineChart_equations_iff a)).trans
      (ChartPoints.Grassmannian.pluckerChartPointEquiv (algebraMap R B) a))

abbrev pluckerHomogeneousChart (a : ι → ν) :=
  HomogeneousLocalization.Away (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)))
    (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) (X a))

def pluckerHomogeneousChartPointEquiv (a : ι → ν) :
    (pluckerHomogeneousChart (R := R) a →ₐ[R] B) ≃
      {Q : Matrix ι ν B // Normalized.Matrices.Grassmannian.IsNormalized a Q} :=
  ((Polynomial.ChartPresentation.PolynomialProjective.affineChartPresentationAlgEquiv (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a).symm.arrowCongr
    (AlgEquiv.refl : B ≃ₐ[R] B)).trans (pluckerAffineChartAlgebraPointEquiv (R := R) (B := B) a)

theorem pluckerHomogeneousChartPointEquiv_apply (a : ι → ν)
    (f : pluckerHomogeneousChart (R := R) a →ₐ[R] B) (i : ι) (j : ν) :
    (pluckerHomogeneousChartPointEquiv a f).val i j =
      f (Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a (X (Function.update a i j))) := rfl

theorem pluckerHomogeneousChartPointEquiv_minor (a b : ι → ν)
    (f : pluckerHomogeneousChart (R := R) a →ₐ[R] B) :
    Determinants.Grassmannian.maximalMinor (pluckerHomogeneousChartPointEquiv a f).val b =
      f (Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a (X b)) := by
  let I := Plucker.Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)
  let e := Polynomial.ChartPresentation.PolynomialProjective.affineChartPresentationAlgEquiv I a
  let p := Polynomial.QuotientPoints.PolynomialProjective.polynomialQuotientPointEquiv (Polynomial.ChartPresentation.PolynomialProjective.affineChartIdeal I a) (f.comp e.toAlgHom)
  let q : ChartPoints.Grassmannian.PluckerChartPoint (algebraMap R B) a :=
    ⟨p.val, (pluckerAffineChart_equations_iff a p.val).mp p.property⟩
  exact ChartPoints.Grassmannian.pluckerChartMatrix_minors (algebraMap R B) a q b

theorem pluckerHomogeneousChartPointEquiv_natural
    {C : Type*} [CommRing C] [Algebra R C] (g : B →ₐ[R] C) (a : ι → ν)
    (f : pluckerHomogeneousChart (R := R) a →ₐ[R] B) :
    (pluckerHomogeneousChartPointEquiv a (g.comp f)).val =
      (pluckerHomogeneousChartPointEquiv a f).val.map g := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartAlgebra.Grassmannian
