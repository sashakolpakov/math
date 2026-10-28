import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ChartPresentation

/-! # Chart Finite Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartFinitePresentation.GradedHilbert

noncomputable section

/-! A finitely presented projective family has finitely generated equations
on each standard affine chart, over arbitrary coefficient rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem projectiveChart_finitePresentation [LocallyOfFinitePresentation (Flatness.GradedHilbert.projectiveStructureMap 𝒜)]
    {s : A} (hs : s ∈ 𝒜 1) : Algebra.FinitePresentation R (HomogeneousLocalization.Away 𝒜 s) := by
  have H : LocallyOfFinitePresentation (Proj.awayι 𝒜 s hs Nat.zero_lt_one ≫ Flatness.GradedHilbert.projectiveStructureMap 𝒜) :=
    inferInstance
  rw [Flatness.GradedHilbert.projectiveStructureMap_away, LocallyOfFinitePresentation.SpecMap_iff] at H
  exact RingHom.finitePresentation_algebraMap.mp H

variable {n : ℕ}

theorem projectiveQuotient_affineChartIdeal_fg (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    [LocallyOfFinitePresentation (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))] (i : Fin (n + 1)) :
    (Polynomial.ChartPresentation.PolynomialProjective.affineChartIdeal I i).FG := by
  let A := HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
  let ψ : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n →ₐ[R] A :=
    { __ := Polynomial.ChartPresentation.PolynomialProjective.affineChartMap I i
      commutes' r := Polynomial.ChartPresentation.PolynomialProjective.affineChartMap_C I i r }
  have : Algebra.FinitePresentation R A := projectiveChart_finitePresentation (Graded.Quotient.GradedHilbert.quotientGrading I)
    ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i))
  have h := Algebra.FinitePresentation.ker_fG_of_surjective ψ (Polynomial.ChartPresentation.PolynomialProjective.affineChartMap_surjective I i)
  change (RingHom.ker (Polynomial.ChartPresentation.PolynomialProjective.affineChartMap I i)).FG at h
  rwa [Polynomial.ChartPresentation.PolynomialProjective.affineChartMap_kernel] at h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartFinitePresentation.GradedHilbert
