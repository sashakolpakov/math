import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialPointEmbedding
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ProjectivePresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialNaturality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.PointIdeal

/-! # Polynomial Fiber Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialFiberPolynomial.GradedHilbert

noncomputable section

/-! Bounded polynomial families satisfy the exact arbitrary-field-point
fiber Hilbert-polynomial predicate in the validated Presentations statement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {n : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)

theorem boundedNativePolynomialFamily_point_ideal (q : ℕ → ℕ) {T : Over S} (x : T ⟶ M)
    (hx : x ∈ (Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T))
    {K : Type u} [Field K] (a : Spec (CommRingCat.of K) ⟶ T.left) :
    (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n)
      (Over.homMk a : Over.mk (a ≫ x.left) ⟶ Over.mk x.left)
      (PolynomialFamily.GradedHilbert.boundedNativePolynomialFamily M g N hg q x hx)).val =
    (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)
      (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M (a ≫ x.left))).ker := by
  let U : Over S := Over.mk (a ≫ T.hom)
  let b : U ⟶ T := Over.homMk a rfl
  have h := congrArg Subtype.val (PolynomialNaturality.GradedHilbert.boundedNativePolynomialFamily_baseChange M g N hg q b x hx)
  exact h.symm

theorem boundedNativePolynomialFamily_hasFiberHilbertPolynomial (q : ℕ → ℕ) (P : Polynomial ℚ)
    (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P) {T : Over S} (x : T ⟶ M)
    (hx : x ∈ (BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor M g N hg q).obj (.op T)) :
    Has.Core.HasFiberHilbertPolynomial (ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation M.left n)
      (PolynomialFamily.GradedHilbert.boundedNativePolynomialFamily M g N hg q x (BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor_flat M g N hg q x hx)) P := by
  intro K _ a
  dsimp only [ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation]
  rw [boundedNativePolynomialFamily_point_ideal M g N hg q x
    (BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor_flat M g N hg q x hx) a]
  refine ⟨Projective.Point.GradedHilbert.projectiveSchemePointMap n (a ≫ x.left),
    PolynomialPointEmbedding.GradedHilbert.nativePolynomialPointEmbedding M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) (a ≫ x.left),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact Projective.Point.GradedHilbert.projectiveSchemePointMap_isPullback n (a ≫ x.left)
  · exact PolynomialPointEmbedding.GradedHilbert.nativePolynomialPointEmbedding_isClosedImmersion M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) (a ≫ x.left)
  · exact (PolynomialPointEmbedding.GradedHilbert.nativePolynomialPointEmbedding_ambient M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) (a ≫ x.left)).trans
      ((Category.comp_id _).symm.trans (Category.assoc _ _ _))
  · exact PolynomialPointEmbedding.GradedHilbert.nativePolynomialPointEmbedding_projection M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) (a ≫ x.left)
  · exact PolynomialPointEmbedding.GradedHilbert.nativePolynomialPointEmbedding_hilbertPolynomial M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)
      (a ≫ x.left) P (BoundedHilbert.PointIdeal.GradedHilbert.bounded_hilbert_point_ideal_polynomial M g N hg q P hP x hx a)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialFiberPolynomial.GradedHilbert
