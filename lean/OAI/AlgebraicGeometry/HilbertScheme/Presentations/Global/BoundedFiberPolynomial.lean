import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.PolynomialPointEmbedding
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialFiberPolynomial

/-! # Bounded Fiber Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.BoundedFiberPolynomial.GradedHilbert

noncomputable section

/-! Bounded polynomial families over the original base satisfy the exact
arbitrary-field-point Hilbert-polynomial predicate of Presentations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {n : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)

theorem globalBoundedPolynomialFamily_point_ideal (q : ℕ → ℕ) {T : Over S} (x : T ⟶ M)
    (hx : x ∈ (Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T))
    {K : Type u} [Field K] (a : Spec (CommRingCat.of K) ⟶ T.left) :
    (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
      (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T)
      (BoundedPolynomialFamily.GradedHilbert.globalBoundedPolynomialFamily M g N hg q x hx)).val =
    (PolynomialInclusion.GradedHilbert.globalPolynomialInclusion M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)
      (ProjectivePoint.GradedHilbert.polynomialPointMorphismOver M (a ≫ x.left) (a ≫ T.hom)
        ((Category.assoc _ _ _).trans (congrArg (fun f => a ≫ f) x.w)))).ker := by
  let U : Over S := Over.mk (a ≫ T.hom)
  let b : U ⟶ T := Over.homMk a rfl
  have h := congrArg Subtype.val (BoundedPolynomialFamily.GradedHilbert.globalBoundedPolynomialFamily_baseChange M g N hg q b x hx)
  rw [PolynomialInclusion.GradedHilbert.globalBoundedPolynomialFamily_val] at h
  exact h.symm

theorem globalBoundedPolynomialFamily_hasFiberHilbertPolynomial (q : ℕ → ℕ) (P : Polynomial ℚ)
    (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P) {T : Over S} (x : T ⟶ M)
    (hx : x ∈ (BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor M g N hg q).obj (.op T)) :
    Has.Core.HasFiberHilbertPolynomial (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n)
      (BoundedPolynomialFamily.GradedHilbert.globalBoundedPolynomialFamily M g N hg q x (BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor_flat M g N hg q x hx)) P := by
  intro K _ a
  dsimp only [Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation]
  rw [globalBoundedPolynomialFamily_point_ideal M g N hg q x
    (BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor_flat M g N hg q x hx) a]
  have ha : (a ≫ x.left) ≫ M.hom = a ≫ T.hom :=
    (Category.assoc _ _ _).trans (congrArg (fun f => a ≫ f) x.w)
  refine ⟨ProjectivePoint.GradedHilbert.globalProjectiveSchemePointMap M n (a ≫ x.left),
    PolynomialPointEmbedding.GradedHilbert.globalPolynomialPointEmbedding M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) (a ≫ x.left) (a ≫ T.hom) ha,
    ?_, ?_, ?_, ?_, ?_⟩
  · have H := ProjectivePoint.GradedHilbert.globalProjectiveSchemePointMap_isPullback M n (a ≫ x.left)
    rw [ha] at H
    exact H
  · exact PolynomialPointEmbedding.GradedHilbert.globalPolynomialPointEmbedding_isClosedImmersion M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)
      (a ≫ x.left) (a ≫ T.hom) ha
  · exact (PolynomialPointEmbedding.GradedHilbert.globalPolynomialPointEmbedding_ambient M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)
      (a ≫ x.left) (a ≫ T.hom) ha).trans ((Category.comp_id _).symm.trans (Category.assoc _ _ _))
  · exact PolynomialPointEmbedding.GradedHilbert.globalPolynomialPointEmbedding_projection M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)
      (a ≫ x.left) (a ≫ T.hom) ha
  · exact PolynomialPointEmbedding.GradedHilbert.globalPolynomialPointEmbedding_hilbertPolynomial M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)
      (a ≫ x.left) (a ≫ T.hom) ha P (BoundedHilbert.PointIdeal.GradedHilbert.bounded_hilbert_point_ideal_polynomial M g N hg q P hP x hx a)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.BoundedFiberPolynomial.GradedHilbert
