import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientPoint
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldPoints

/-! # Point Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.PointIdeal.GradedHilbert

noncomputable section

/-! The homogeneous ideal of the actual projective point fiber has the
polynomial imposed by the bounded Hilbert parameter locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)

theorem bounded_hilbert_point_ideal_polynomial (q : ℕ → ℕ) (P : Polynomial ℚ)
    (hP : DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P) {T : Over S} (x : T ⟶ M)
    (hx : x ∈ (DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor M g N hg q).obj (.op T))
    {K : Type u} [Field K] (a : Spec (CommRingCat.of K) ⟶ T.left) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) (a ≫ x.left)).toIdeal P := by
  have h := FieldPoints.GradedHilbert.bounded_hilbert_locus_field_point M g N hg q P hP x hx a
  change Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (Ideal.map (MvPolynomial.map (PointCoefficients.schemePointCoefficientMap (a ≫ x.left))) (Ideal.span (Set.range g))) P
  rw [Ideal.map_span, ← Set.range_comp]
  have he : (MvPolynomial.map (PointCoefficients.schemePointCoefficientMap (a ≫ x.left))) ∘ g =
      Finite.SyzygyLifting.GradedHilbert.mapRelationVector ((PointCoefficients.schemePointCoefficientMap a).comp x.left.appTop.hom) g := by
    funext i
    rfl
  rw [he]
  exact h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.PointIdeal.GradedHilbert
