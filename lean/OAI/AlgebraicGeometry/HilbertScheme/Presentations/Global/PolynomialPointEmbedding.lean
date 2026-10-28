import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.ProjectivePoint
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionImageEmbedding
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial

/-! # Polynomial Point Embedding -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.PolynomialPointEmbedding.GradedHilbert

noncomputable section

/-! The actual original-base polynomial fiber has a closed embedding
in polynomial projective space whose kernel has the computed Hilbert polynomial. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))
variable {R : Type u} [CommRing R] (a : Spec (CommRingCat.of R) ⟶ M.left)
variable (f : Spec (CommRingCat.of R) ⟶ S) (ha : a ≫ M.hom = f)

def globalPolynomialPointEmbedding :
    (PolynomialInclusion.GradedHilbert.globalPolynomialInclusion M I (ProjectivePoint.GradedHilbert.polynomialPointMorphismOver M a f ha)).ker.subscheme ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  Closed.ImmersionImageEmbedding.closedImageEmbedding (PolynomialInclusion.GradedHilbert.globalPolynomialInclusion M I (ProjectivePoint.GradedHilbert.polynomialPointMorphismOver M a f ha))
    (ProjectivePoint.GradedHilbert.globalPolynomialPointPresentation M n a I f ha) (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a))

instance globalPolynomialPointEmbedding_isClosedImmersion :
    IsClosedImmersion (globalPolynomialPointEmbedding M I a f ha) :=
  Closed.ImmersionImageEmbedding.closedImageEmbedding_isClosedImmersion _ _ _

theorem globalPolynomialPointEmbedding_projection :
    globalPolynomialPointEmbedding M I a f ha ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) =
      Hilbert.Functor.familyProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (PolynomialInclusion.GradedHilbert.globalPolynomialInclusion M I (ProjectivePoint.GradedHilbert.polynomialPointMorphismOver M a f ha)).ker := by
  apply Closed.ImmersionImageEmbedding.closedImageEmbedding_compatibility
  rw [PolynomialInclusion.GradedHilbert.globalPolynomialInclusion_projection]
  exact (Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso_projection M I a).trans
    (Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a)).symm

theorem globalPolynomialPointEmbedding_ambient :
    globalPolynomialPointEmbedding M I a f ha ≫ ProjectivePoint.GradedHilbert.globalProjectiveSchemePointMap M n a =
      (PolynomialInclusion.GradedHilbert.globalPolynomialInclusion M I (ProjectivePoint.GradedHilbert.polynomialPointMorphismOver M a f ha)).ker.subschemeι ≫
        (prod.snd : Over.mk f ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left :=
  Closed.ImmersionImageEmbedding.closedImageEmbedding_compatibility _ _ _ _ _ (ProjectivePoint.GradedHilbert.projectiveQuotientPointIso_global_projective M n a I f ha)

theorem globalPolynomialPointEmbedding_hilbertPolynomial [IsNoetherianRing R] (P : Polynomial ℚ)
    (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a).toIdeal P) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (globalPolynomialPointEmbedding M I a f ha).ker).toIdeal P := by
  rw [globalPolynomialPointEmbedding, Closed.ImmersionImageEmbedding.closedImageEmbedding_ker]
  exact (Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a) P).mpr hP

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.PolynomialPointEmbedding.GradedHilbert
