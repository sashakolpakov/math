import OAI.AlgebraicGeometry.PELModuli.IntegralModel.MatrixKernelRankLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.SubfunctorLocus

/-! # Matrix Kernel Rank Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.MatrixKernelRankLocus

noncomputable section

/-! Matrix-kernel ranks on all geometric fibers have an actual
locally closed representing locus on every reduced test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} (M : Over S)
  {μ ν : Type} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
  (A : Matrix ν μ Γ(M.left, ⊤)) (r : ℕ)

theorem matrixKernelRank_reduced_iff_geometric (T : Over S) [IsReduced T.left] (x : T ⟶ M) :
    x ∈ (MatrixKernelRankLocus.matrixKernelRankSubfunctor M A r).obj (.op T) ↔
      ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T.left),
        Module.finrank k (Matrix.toLin'
          (AbelianModuli.HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M A (.of k) (SubfunctorLocus.geometricTestMap x p))).ker = r := by
  rw [SubfunctorLocus.immersion_subfunctor_mem_iff_geometric (MatrixKernelRankLocus.matrixKernelRankSubfunctor M A r)
    (MatrixKernelRankLocus.matrixKernelRank_immersion M A r) T x]
  constructor
  · intro h k _ _ p
    exact (MatrixKernelRankLocus.matrixKernelRank_field_iff M A r (SubfunctorLocus.geometricTestMap x p)).mp (h k p)
  · intro h k _ _ p
    exact (MatrixKernelRankLocus.matrixKernelRank_field_iff M A r (SubfunctorLocus.geometricTestMap x p)).mpr (h k p)

theorem exists_reduced_test_matrix_kernel_rank_locus :
    ∃ (Z : Over S) (j : Z ⟶ M), IsImmersion j.left ∧ QuasiCompact j.left ∧
      ∀ (T : Over S) [IsReduced T.left] (x : T ⟶ M),
        (∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T.left),
          Module.finrank k (Matrix.toLin'
            (AbelianModuli.HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M A (.of k) (SubfunctorLocus.geometricTestMap x p))).ker = r) ↔
          ∃! f : T ⟶ Z, f ≫ j = x := by
  obtain ⟨Z, j, hj, hqc, e, he⟩ := MatrixKernelRankLocus.matrixKernelRank_immersion M A r
  let := hj
  let : Mono j := Over.mono_of_mono_left j
  refine ⟨Z, j, hj, hqc, ?_⟩
  intro T hT x
  rw [← matrixKernelRank_reduced_iff_geometric M A r T x,
    HilbertScheme.Presentations.SubfunctorRepresentations.represented_subfunctor_mem (MatrixKernelRankLocus.matrixKernelRankSubfunctor M A r) j e he T x]
  exact ⟨fun ⟨f, hf⟩ => ⟨f, hf, fun q hq => (cancel_mono j).mp (hq.trans hf.symm)⟩,
    fun ⟨f, hf, _⟩ => ⟨f, hf⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.MatrixKernelRankLocus
