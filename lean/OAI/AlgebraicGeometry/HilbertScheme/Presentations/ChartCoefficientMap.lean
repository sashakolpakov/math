import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.CoefficientMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartBaseChange

/-! # Chart Coefficient Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartCoefficientMap.GradedHilbert

noncomputable section

/-!
Coefficient change on projective chart rings agrees with the tensor
base-change map, including its action on all polynomial generators.
-/

open _root_.MvPolynomial TensorProduct _root_.HomogeneousLocalization

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] {n : ℕ}

def chartCoefficientMap (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) →+*
      HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I))
        (Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (X i)) :=
  HomogeneousLocalization.map (Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap I) (by
    rintro _ ⟨k, rfl⟩
    exact ⟨k, by rw [map_pow, Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap_X]⟩)

theorem chartCoefficientMap_homogeneous (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n} {d : ℕ} (hf : f.IsHomogeneous d) :
    chartCoefficientMap (S := S) I i (Affine.ChartPresentation.GradedHilbert.affineChartMap I i f) =
      Affine.ChartPresentation.GradedHilbert.affineChartMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) i (MvPolynomial.map (algebraMap R S) f) := by
  rw [Affine.ChartPresentation.GradedHilbert.affineChartMap_homogeneous I i hf,
    Affine.ChartPresentation.GradedHilbert.affineChartMap_homogeneous (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) i (hf.map (algebraMap R S))]
  apply HomogeneousLocalization.val_injective
  change Localization.mk (Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap (S := S) I (Graded.Quotient.GradedHilbert.gradedQuotientMap I f))
    (⟨Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap (S := S) I (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i) ^ d),
      by rw [map_pow, Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap_X]; exact ⟨d, rfl⟩⟩ :
      Submonoid.powers (Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (X i))) =
    Localization.mk (Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)
      (MvPolynomial.map (algebraMap R S) f))
      (⟨Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (X i) ^ d, ⟨d, rfl⟩⟩ :
        Submonoid.powers (Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (X i)))
  simp only [map_pow, Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap_mk, MvPolynomial.map_X]

theorem chartCoefficientMap_comp (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    (chartCoefficientMap (S := S) I i).comp (Affine.ChartPresentation.GradedHilbert.affineChartMap I i) =
      (Affine.ChartPresentation.GradedHilbert.affineChartMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) i).comp
        (MvPolynomial.map (algebraMap R S)) := by
  apply MvPolynomial.ringHom_ext
  · intro x
    exact chartCoefficientMap_homogeneous (S := S) I i (isHomogeneous_C _ x)
  · intro x
    exact chartCoefficientMap_homogeneous (S := S) I i (isHomogeneous_X R x)

theorem chartCoefficientMap_apply (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    chartCoefficientMap (S := S) I i (Affine.ChartPresentation.GradedHilbert.affineChartMap I i f) =
      Affine.ChartPresentation.GradedHilbert.affineChartMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) i (MvPolynomial.map (algebraMap R S) f) :=
  DFunLike.congr_fun (chartCoefficientMap_comp (S := S) I i) f

theorem affineChartBaseChangeEquiv_one_tmul (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1))
    (x : HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))) :
    Affine.ChartBaseChange.GradedHilbert.affineChartBaseChangeEquiv (S := S) I i (1 ⊗ₜ[R] x) = chartCoefficientMap (S := S) I i x := by
  obtain ⟨f, rfl⟩ := Affine.ChartPresentation.GradedHilbert.affineChartMap_surjective I i x
  rw [Affine.ChartBaseChange.GradedHilbert.affineChartBaseChangeEquiv_tmul, one_smul, chartCoefficientMap_apply]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartCoefficientMap.GradedHilbert
