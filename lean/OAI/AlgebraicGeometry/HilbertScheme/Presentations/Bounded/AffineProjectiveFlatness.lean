import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.HomogeneousFlatLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.DegreeFlatness

/-! # Affine Projective Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.AffineProjectiveFlatness.GradedHilbert

noncomputable section

/-! On every affine test scheme, the represented bounded degree conditions
make the actual specialized projective quotient flat over its coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)

theorem bounded_degree_locus_affine_quotients_flat (q : ℕ → ℕ) {T : Over S} [IsAffine T.left]
    (x : T ⟶ M) (hx : x ∈ (HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T)) (d : ℕ) :
    Module.Flat Γ(T.left, ⊤) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient
      (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (Finite.SyzygyLifting.GradedHilbert.mapRelationVector x.left.appTop.hom g) N
        (fun i => (hg i).map _)).toIdeal (d + N)) := by
  apply Affine.DegreeFlatness.GradedHilbert.affine_generated_quotient_flat T.left
  intro t
  have hfree := HomogeneousFlatLocus.GradedHilbert.bounded_degree_locus_all_stalk_quotients_free M g N hg q x hx t d
  have hf : Module.Flat (T.left.presheaf.stalk t) (Homogeneous.DegreeLoci.GradedHilbert.degreeQuotientAtStalk M g N hg x t d) := by
    let := hfree
    infer_instance
  have heq : Finite.SyzygyLifting.GradedHilbert.mapRelationVector (T.left.presheaf.Γgerm t).hom (Finite.SyzygyLifting.GradedHilbert.mapRelationVector x.left.appTop.hom g) =
      (fun i => MvPolynomial.map ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom) (g i)) := by
    funext i
    exact MvPolynomial.map_map x.left.appTop.hom (T.left.presheaf.Γgerm t).hom (g i)
  change Module.Flat (T.left.presheaf.stalk t) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient
    (Ideal.span (Set.range (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (T.left.presheaf.Γgerm t).hom
      (Finite.SyzygyLifting.GradedHilbert.mapRelationVector x.left.appTop.hom g)))) (d + N))
  rw [heq]
  exact hf

theorem bounded_degree_locus_affine_projective_flat (q : ℕ → ℕ) {T : Over S} [IsAffine T.left]
    (x : T ⟶ M) (hx : x ∈ (HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T)) :
    Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading
      (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (Finite.SyzygyLifting.GradedHilbert.mapRelationVector x.left.appTop.hom g) N
        (fun i => (hg i).map _)))) :=
  Finite.DegreeFlatness.GradedHilbert.projectiveQuotient_flat_of_finite_degree_test _ N _
    (fun d _ => bounded_degree_locus_affine_quotients_flat M g N hg q x hx d)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.AffineProjectiveFlatness.GradedHilbert
