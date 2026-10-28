import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicProjectiveEmbedding
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ProjectivePresentation

/-! # Canonical Fiber Polynomial Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomialCriterion.GradedHilbert

noncomputable section

/-! Canonical homogeneous ideals of all actual field fibers establish
the exact fiber-polynomial predicate of the validated Presentations statement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {n : ℕ} {T : Over S}

theorem hasFiberHilbertPolynomial_of_canonical_fibers
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) (P : Polynomial ℚ)
    (hP : ∀ (K : Type u) [Field K] (a : Spec (CommRingCat.of K) ⟶ T.left),
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (a ≫ T.hom)
        (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
          (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) F)).toIdeal P) :
    Has.Core.HasFiberHilbertPolynomial (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) F P := by
  intro K _ a
  let b : Over.mk (a ≫ T.hom) ⟶ T := Over.homMk a rfl
  let G := Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F
  dsimp only [Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation]
  refine ⟨Projective.Point.GradedHilbert.projectiveSchemePointMap n (a ≫ T.hom), Affine.IntrinsicProjectiveEmbedding.GradedHilbert.affineNativeProjectiveEmbedding n (a ≫ T.hom) G,
    Projective.Point.GradedHilbert.projectiveSchemePointMap_isPullback n (a ≫ T.hom),
    Affine.IntrinsicProjectiveEmbedding.GradedHilbert.affineNativeProjectiveEmbedding_closed n (a ≫ T.hom) G, ?_, ?_, ?_⟩
  · exact (Affine.IntrinsicProjectiveEmbedding.GradedHilbert.affineNativeProjectiveEmbedding_ambient n (a ≫ T.hom) G).trans
      ((Category.comp_id _).symm.trans (Category.assoc _ _ _))
  · exact Affine.IntrinsicProjectiveEmbedding.GradedHilbert.affineNativeProjectiveEmbedding_projection n (a ≫ T.hom) G
  · exact Eq.mpr (congrArg (fun I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n) => Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)
      (Affine.IntrinsicProjectiveEmbedding.GradedHilbert.affineNativeProjectiveEmbedding_coordinates n (a ≫ T.hom) G)) (hP K a)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomialCriterion.GradedHilbert
