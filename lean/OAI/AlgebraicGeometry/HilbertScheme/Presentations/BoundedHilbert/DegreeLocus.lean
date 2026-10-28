import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.HomogeneousFlatLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.RankTest

/-! # Degree Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert

noncomputable section

/-! A finite locally closed degree-profile locus enforces flat projective
families and the specified Hilbert polynomial on their residue-field fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

def hilbertTestDegree (n N : ℕ) (i : Fin (n + 1)) : ℕ := Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val - N

theorem hilbertTestDegree_add (n N : ℕ) (i : Fin (n + 1)) :
    hilbertTestDegree n N i + N = Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val :=
  Nat.sub_add_cancel ((Local.RankTest.GradedHilbert.generatorHilbertFunctionBound_ge n N).trans (Nat.le_add_right _ _))

def hilbertFlatDegreeSet (n m N : ℕ) : Finset ℕ :=
  Finset.range (Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n m N + 1) ∪ Finset.univ.image (hilbertTestDegree n N)

def RankProfileRealizes (n N : ℕ) (q : ℕ → ℕ) (P : Polynomial ℚ) : Prop :=
  P.natDegree ≤ n ∧ ∀ i : Fin (n + 1),
    ((Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val)) -
        q (hilbertTestDegree n N i) : ℕ) : ℚ) =
      P.eval ((Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val : ℕ) : ℚ)

variable {S : Scheme.{u}} (M : Over S) {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)

def boundedHilbertDegreeSubfunctor (q : ℕ → ℕ) : Subfunctor (yoneda.obj M) :=
  ⨅ d ∈ hilbertFlatDegreeSet n (Fintype.card ι) N, Homogeneous.DegreeLoci.GradedHilbert.homogeneousDegreeFlatRankSubfunctor M g N hg d (q d)

theorem boundedHilbertDegreeSubfunctor_mem (q : ℕ → ℕ) {T : Over S} (x : T ⟶ M) :
    x ∈ (boundedHilbertDegreeSubfunctor M g N hg q).obj (.op T) ↔
      ∀ d ∈ hilbertFlatDegreeSet n (Fintype.card ι) N, Homogeneous.DegreeLoci.GradedHilbert.HomogeneousDegreeFlatRank M g N hg d (q d) x := by
  simp only [boundedHilbertDegreeSubfunctor, Subfunctor.iInf_obj, Set.mem_iInter]
  exact forall_congr' (fun d => imp_congr_right
    (fun _ => Homogeneous.DegreeLoci.GradedHilbert.homogeneousDegreeFlatRankSubfunctor_mem M g N hg d (q d) x))

theorem bounded_hilbert_degree_locus (q : ℕ → ℕ) :
    SubfunctorRepresentations.ImmersionRepresentable (boundedHilbertDegreeSubfunctor M g N hg q) :=
  Homogeneous.DegreeLoci.GradedHilbert.homogeneous_finite_degree_locus M g N hg _ q

theorem boundedHilbertDegreeSubfunctor_flat (q : ℕ → ℕ) {T : Over S} (x : T ⟶ M)
    (hx : x ∈ (boundedHilbertDegreeSubfunctor M g N hg q).obj (.op T)) :
    x ∈ (Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor M g N hg q).obj (.op T) := by
  apply (Bounded.HomogeneousFlatLocus.GradedHilbert.boundedDegreeFlatRankSubfunctor_mem M g N hg q x).mpr
  intro d hd
  apply (boundedHilbertDegreeSubfunctor_mem M g N hg q x).mp hx d
  exact Finset.mem_union_left _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hd))

theorem bounded_hilbert_locus_residue_polynomial (q : ℕ → ℕ) (P : Polynomial ℚ)
    (hP : RankProfileRealizes.{u} n N q P) {T : Over S} (x : T ⟶ M)
    (hx : x ∈ (boundedHilbertDegreeSubfunctor M g N hg q).obj (.op T)) (t : T.left) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal
      (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap (T.left.presheaf.stalk t) (IsLocalRing.ResidueField (T.left.presheaf.stalk t)))
        (fun i => MvPolynomial.map ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom) (g i))) N
      (fun i => ((hg i).map _).map _)).toIdeal P := by
  let gs := fun i => MvPolynomial.map ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom) (g i)
  have hgs : ∀ i, (gs i).IsHomogeneous N := fun i => (hg i).map _
  have hflat (d : ℕ) : Module.Flat (T.left.presheaf.stalk t)
      (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal gs N hgs).toIdeal (d + N)) := by
    have hfree : Module.Free (T.left.presheaf.stalk t)
        (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal gs N hgs).toIdeal (d + N)) :=
      Bounded.HomogeneousFlatLocus.GradedHilbert.bounded_degree_locus_all_stalk_quotients_free M g N hg q x
        (boundedHilbertDegreeSubfunctor_flat M g N hg q x hx) t d
    let := hfree
    infer_instance
  apply (Local.RankTest.GradedHilbert.homogeneous_local_hilbertPolynomial_rank_test
    (K := IsLocalRing.ResidueField (T.left.presheaf.stalk t)) gs N hgs hflat P).mpr
  refine ⟨hP.1, fun i => ?_⟩
  have hi : hilbertTestDegree n N i ∈ hilbertFlatDegreeSet n (Fintype.card ι) N :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hr := ((boundedHilbertDegreeSubfunctor_mem M g N hg q x).mp hx _ hi t).2
  change Module.finrank (T.left.presheaf.stalk t)
    (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal gs N hgs).toIdeal (hilbertTestDegree n N i + N)) +
      q (hilbertTestDegree n N i) = Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (hilbertTestDegree n N i + N)) at hr
  rw [hilbertTestDegree_add] at hr
  have heq : Module.finrank (T.left.presheaf.stalk t)
      (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal gs N hgs).toIdeal
        (Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val)) =
      Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val)) -
        q (hilbertTestDegree n N i) := by omega
  rw [heq]
  exact hP.2 i

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert
