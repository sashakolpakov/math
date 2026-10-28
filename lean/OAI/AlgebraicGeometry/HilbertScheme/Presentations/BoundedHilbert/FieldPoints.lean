import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldSpecialization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PointCoefficients

/-! # Field Points -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldPoints.GradedHilbert

noncomputable section

/-! Every field-valued point of a bounded Hilbert parameter family has the
prescribed polynomial after actual coefficient specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)

theorem bounded_hilbert_locus_field_point (q : ℕ → ℕ) (P : Polynomial ℚ)
    (hP : DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P) {T : Over S} (x : T ⟶ M)
    (hx : x ∈ (DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor M g N hg q).obj (.op T))
    {K : Type u} [Field K] (a : Spec (CommRingCat.of K) ⟶ T.left) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal
      (Finite.SyzygyLifting.GradedHilbert.mapRelationVector ((PointCoefficients.schemePointCoefficientMap a).comp x.left.appTop.hom) g) N
      (fun i => (hg i).map _)).toIdeal P := by
  have h := FieldSpecialization.GradedHilbert.bounded_hilbert_locus_field_specialization M g N hg q P hP x hx
    (a (IsLocalRing.closedPoint K)) (Scheme.stalkClosedPointTo a).hom
  have he : Finite.SyzygyLifting.GradedHilbert.mapRelationVector ((PointCoefficients.schemePointCoefficientMap a).comp x.left.appTop.hom) g =
      Finite.SyzygyLifting.GradedHilbert.mapRelationVector (Scheme.stalkClosedPointTo a).hom
        (fun i => MvPolynomial.map
          ((T.left.presheaf.Γgerm (a (IsLocalRing.closedPoint K))).hom.comp x.left.appTop.hom) (g i)) := by
    funext i
    simp only [Finite.SyzygyLifting.GradedHilbert.mapRelationVector, MvPolynomial.map_map, PointCoefficients.schemePointCoefficientMap_stalk,
      RingHom.comp_assoc]
  change Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Ideal.span (Set.range
    (Finite.SyzygyLifting.GradedHilbert.mapRelationVector ((PointCoefficients.schemePointCoefficientMap a).comp x.left.appTop.hom) g))) P
  rw [he]
  exact h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldPoints.GradedHilbert
