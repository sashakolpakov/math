import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeCokernel
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LocusIntersections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.QuasiCompact

/-! # Degree Loci -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeLoci.GradedHilbert

noncomputable section

/-! Actual locally closed schemes imposing finitely many homogeneous quotient
flatness and rank conditions in a polynomial family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.QuasiCompact.Grassmannian
variable {S : Scheme.{u}} (M : Over S) {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(M.left, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)

abbrev degreeQuotientAtStalk {T : Over S} (x : T ⟶ M) (t : T.left) (d : ℕ) :=
  Hilbert.Polynomial.GradedHilbert.DegreeQuotient (RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal
    (fun i => MvPolynomial.map ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom) (g i)) N
    (fun i => (hg i).map _)).toIdeal (d + N)

def HomogeneousDegreeFlatRank (d q : ℕ) {T : Over S} (x : T ⟶ M) : Prop :=
  ∀ t : T.left, Module.Flat (T.left.presheaf.stalk t) (degreeQuotientAtStalk M g N hg x t d) ∧
    Module.finrank (T.left.presheaf.stalk t) (degreeQuotientAtStalk M g N hg x t d) + q =
      Fintype.card (CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N))

def homogeneousDegreeFlatRankSubfunctor (d q : ℕ) : Subfunctor (yoneda.obj M) :=
  Presentations.Matrix.FlatRankLocus.Grassmannian.matrixFlatRankSubfunctor (ι := ULift.{u} (Fin q)) M (DegreeMatrix.GradedHilbert.homogeneousDegreeMatrix g N hg d)

theorem homogeneousDegreeFlatRankSubfunctor_mem (d q : ℕ) {T : Over S} (x : T ⟶ M) :
    x ∈ (homogeneousDegreeFlatRankSubfunctor M g N hg d q).obj (.op T) ↔
      HomogeneousDegreeFlatRank M g N hg d q x := by
  have e (t : T.left) := DegreeCokernel.GradedHilbert.homogeneousSpecializedMatrixCokernelEquiv
    ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom) g N hg d
  constructor
  · intro hx t
    have h := hx t
    dsimp only [Presentations.Matrix.FlatRankLocus.Grassmannian.matrixAtStalk] at h
    have hf : Module.Flat (T.left.presheaf.stalk t)
        ((CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N) → T.left.presheaf.stalk t) ⧸
          (Matrix.toLin' ((DegreeMatrix.GradedHilbert.homogeneousDegreeMatrix g N hg d).map
            ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom))).range) := h.1
    let := hf
    refine ⟨Module.Flat.of_linearEquiv (e t).symm, ?_⟩
    rw [← (e t).finrank_eq]
    have hr := h.2
    simp only [Fintype.card_ulift, Fintype.card_fin] at hr
    exact hr
  · intro hx t
    have h := hx t
    let := h.1
    refine ⟨Module.Flat.of_linearEquiv (e t), ?_⟩
    change Module.finrank (T.left.presheaf.stalk t)
      ((CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N) → T.left.presheaf.stalk t) ⧸
        (Matrix.toLin' ((DegreeMatrix.GradedHilbert.homogeneousDegreeMatrix g N hg d).map
          ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom))).range) +
          Fintype.card (ULift.{u} (Fin q)) = _
    rw [(e t).finrank_eq, Fintype.card_ulift, Fintype.card_fin]
    exact h.2

theorem homogeneous_degree_flat_rank_immersion (d q : ℕ) :
    SubfunctorRepresentations.ImmersionRepresentable (homogeneousDegreeFlatRankSubfunctor M g N hg d q) := by
  obtain ⟨Z, j, hj, _, hqc, e, he⟩ :=
    MatrixRank.QuasiCompact.Grassmannian.matrix_flat_fixed_rank_immersion (ι := ULift.{u} (Fin q)) M (DegreeMatrix.GradedHilbert.homogeneousDegreeMatrix g N hg d)
  exact ⟨Z, j, hj, hqc, e, he⟩

theorem homogeneous_finite_degree_locus (D : Finset ℕ) (q : ℕ → ℕ) :
    SubfunctorRepresentations.ImmersionRepresentable (⨅ d ∈ D, homogeneousDegreeFlatRankSubfunctor M g N hg d (q d)) :=
  Finite.LocusIntersections.immersionRepresentable_finset_inf D _ (fun d _ => homogeneous_degree_flat_rank_immersion M g N hg d (q d))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeLoci.GradedHilbert
