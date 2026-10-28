import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedMatrixRankLoci
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Matrix Kernel Rank Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.MatrixKernelRankLocus

noncomputable section

/-! Actual locally closed parameter loci for the dimension of a finite
matrix kernel. The field criterion is proved by transposed cokernels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Matrix

theorem transpose_cokernel_finrank_eq_kernel
    {k : Type} [Field k] {μ ν : Type} [Fintype μ] [Fintype ν]
    [DecidableEq μ] [DecidableEq ν] (A : Matrix ν μ k) :
    Module.finrank k ((μ → k) ⧸ (Matrix.toLin' A.transpose).range) =
      Module.finrank k (Matrix.toLin' A).ker := by
  have hq := Submodule.finrank_quotient_add_finrank (Matrix.toLin' A.transpose).range
  have hk := (Matrix.toLin' A).finrank_range_add_finrank_ker
  have ht := Matrix.rank_transpose A
  change Module.finrank k (Matrix.toLin' A.transpose).range =
    Module.finrank k (Matrix.toLin' A).range at ht
  rw [Module.finrank_fintype_fun_eq_card] at hq hk
  omega

variable {S : Scheme.{0}} (M : Over S)
  {μ ν : Type} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
  (A : Matrix ν μ Γ(M.left, ⊤)) (r : ℕ)

def matrixKernelRankSubfunctor : Subfunctor (yoneda.obj M) :=
  AbelianModuli.HilbertConstruction.PrescribedMatrixRankLoci.prescribedMatrixRankSubfunctor M A.transpose r

theorem matrixKernelRank_immersion : HilbertScheme.Presentations.SubfunctorRepresentations.ImmersionRepresentable (matrixKernelRankSubfunctor M A r) :=
  AbelianModuli.HilbertConstruction.PrescribedMatrixRankLoci.prescribedMatrixRank_immersion M A.transpose r

theorem matrixKernelRank_field_iff {k : Type} [Field k]
    {f : Spec (.of k) ⟶ S} (x : Over.mk f ⟶ M) :
    x ∈ (matrixKernelRankSubfunctor M A r).obj (.op (Over.mk f)) ↔
      Module.finrank k (Matrix.toLin' (AbelianModuli.HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M A (.of k) x)).ker = r := by
  rw [matrixKernelRankSubfunctor, AbelianModuli.HilbertConstruction.PrescribedMatrixRankLoci.prescribedMatrixRank_affine_iff]
  have hflat : Module.Flat k ((μ → k) ⧸
      (Matrix.toLin' (AbelianModuli.HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M A.transpose (.of k) x)).range) := inferInstance
  simp only [hflat, true_and, Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, forall_const]
  exact congrArg (· = r) (transpose_cokernel_finrank_eq_kernel
    (AbelianModuli.HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M A (.of k) x)) |>.to_iff

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.MatrixKernelRankLocus
