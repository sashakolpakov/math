import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeLoci
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.DegreeFlatness

/-! # Homogeneous Flat Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.HomogeneousFlatLocus.GradedHilbert

noncomputable section

/-! A finite locally closed parameter locus forces flatness in every higher
homogeneous degree and of the actual projective family over every base stalk. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)

def boundedDegreeFlatRankSubfunctor (q : ℕ → ℕ) : Subfunctor (yoneda.obj M) :=
  ⨅ d ∈ Finset.range (Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card ι) N + 1),
    Homogeneous.DegreeLoci.GradedHilbert.homogeneousDegreeFlatRankSubfunctor M g N hg d (q d)

theorem boundedDegreeFlatRankSubfunctor_mem (q : ℕ → ℕ) {T : Over S} (x : T ⟶ M) :
    x ∈ (boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T) ↔
      ∀ d ≤ Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card ι) N,
        Homogeneous.DegreeLoci.GradedHilbert.HomogeneousDegreeFlatRank M g N hg d (q d) x := by
  simp only [boundedDegreeFlatRankSubfunctor, Subfunctor.iInf_obj, Set.mem_iInter,
    Finset.mem_range, Nat.lt_succ_iff]
  exact forall_congr' (fun d => imp_congr_right
    (fun _ => Homogeneous.DegreeLoci.GradedHilbert.homogeneousDegreeFlatRankSubfunctor_mem M g N hg d (q d) x))

theorem bounded_homogeneous_flat_locus (q : ℕ → ℕ) :
    SubfunctorRepresentations.ImmersionRepresentable (boundedDegreeFlatRankSubfunctor M g N hg q) :=
  Homogeneous.DegreeLoci.GradedHilbert.homogeneous_finite_degree_locus M g N hg _ q

theorem bounded_degree_locus_all_stalk_quotients_free (q : ℕ → ℕ) {T : Over S} (x : T ⟶ M)
    (hx : x ∈ (boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T)) (t : T.left) (d : ℕ) :
    Module.Free (T.left.presheaf.stalk t) (Homogeneous.DegreeLoci.GradedHilbert.degreeQuotientAtStalk M g N hg x t d) :=
  Finite.DegreeFlatnessLocal.GradedHilbert.homogeneous_quotients_free_of_finite_flat_degrees
    (fun i => MvPolynomial.map ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom) (g i)) N
    (fun i => (hg i).map _) (fun e he =>
      ((boundedDegreeFlatRankSubfunctor_mem M g N hg q x).mp hx e he t).1) d

theorem bounded_degree_locus_projective_stalk_flat (q : ℕ → ℕ) {T : Over S} (x : T ⟶ M)
    (hx : x ∈ (boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T)) (t : T.left) :
    Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal
      (fun i => MvPolynomial.map ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom) (g i)) N
      (fun i => (hg i).map _)))) :=
  Finite.DegreeFlatnessLocal.GradedHilbert.projectiveQuotient_flat_of_finite_degree_test_local _ N _
    (fun e he => ((boundedDegreeFlatRankSubfunctor_mem M g N hg q x).mp hx e he t).1)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.HomogeneousFlatLocus.GradedHilbert
