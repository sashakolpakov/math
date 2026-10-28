import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartCoefficientMap
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Chart Pullback -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartPullback.GradedHilbert

noncomputable section

/-!
The affine-chart squares for projective coefficient change are actual
pullbacks of schemes, as follows from their tensor-product presentations.
-/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

theorem affineChart_coefficient_isPushout (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    IsPushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R (HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)))))
      (CommRingCat.ofHom (algebraMap S
        (HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I))
          (Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (X i)))))
      (CommRingCat.ofHom (ChartCoefficientMap.GradedHilbert.chartCoefficientMap (S := S) I i)) := by
  let B := HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
  let e := ChartBaseChange.GradedHilbert.affineChartBaseChangeEquiv (S := S) I i
  apply (CommRingCat.isPushout_tensorProduct R S B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    e.toCommRingCatIso
  · simp
  · simp
  · apply ConcreteCategory.hom_ext
    intro s
    exact e.commutes s
  · apply ConcreteCategory.hom_ext
    intro x
    exact ChartCoefficientMap.GradedHilbert.affineChartBaseChangeEquiv_one_tmul (S := S) I i x

theorem affineChart_coefficient_isPullback (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap S
        (HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I))
          (Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (X i))))))
      (Spec.map (CommRingCat.ofHom (ChartCoefficientMap.GradedHilbert.chartCoefficientMap (S := S) I i)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R
        (HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)))))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (affineChart_coefficient_isPushout I i)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartPullback.GradedHilbert
