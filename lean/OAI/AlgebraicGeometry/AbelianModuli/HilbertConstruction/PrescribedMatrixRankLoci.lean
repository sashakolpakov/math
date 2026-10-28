import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AugmentedMatrixCokernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankAffineCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.QuasiCompact
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LocusIntersections

/-! # Prescribed Matrix Rank Loci -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedMatrixRankLoci

noncomputable section

/-! Actual quasi-compact locally closed loci for arbitrary prescribed cokernel ranks, with exact affine criteria. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LocusIntersections OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.QuasiCompact.Grassmannian

universe u v

variable {μ ν : Type u} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤)) (r : ℕ)

def prescribedMatrixRankSubfunctor : Subfunctor (yoneda.obj M) :=
  HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.matrixFlatRankSubfunctor (ι := ν) M (AugmentedMatrixCokernels.identityAugmentedMatrix (κ := ULift.{u} (Fin r)) A)

theorem prescribedMatrixRank_immersion : HilbertScheme.Presentations.SubfunctorRepresentations.ImmersionRepresentable (prescribedMatrixRankSubfunctor M A r) := by
  obtain ⟨Z, j, hj, _, hqc, e, he⟩ := HilbertScheme.Presentations.MatrixRank.QuasiCompact.Grassmannian.matrix_flat_fixed_rank_immersion (ι := ν) M
    (AugmentedMatrixCokernels.identityAugmentedMatrix (κ := ULift.{u} (Fin r)) A)
  exact ⟨Z, j, hj, hqc, e, he⟩

theorem prescribedMatrixRank_affine_iff (R : CommRingCat.{u}) {f : Spec R ⟶ S} (x : Over.mk f ⟶ M) :
    x ∈ (prescribedMatrixRankSubfunctor M A r).obj (.op (Over.mk f)) ↔
      (Module.Flat R ((ν → R) ⧸ (Matrix.toLin' (HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M A R x)).range) ∧
        ∀ p, Module.rankAtStalk (R := R)
          ((ν → R) ⧸ (Matrix.toLin' (HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M A R x)).range) p = r) := by
  have h := HilbertConstruction.Matrix.RankAffineCriterion.matrixRank_affine_iff (ι := ν) M
    (AugmentedMatrixCokernels.identityAugmentedMatrix (κ := ULift.{u} (Fin r)) A) R x
  change HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ν) M
    (AugmentedMatrixCokernels.identityAugmentedMatrix (κ := ULift.{u} (Fin r)) A) x ↔ _
  refine h.trans ?_
  have he : HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M (AugmentedMatrixCokernels.identityAugmentedMatrix (κ := ULift.{u} (Fin r)) A) R x =
      AugmentedMatrixCokernels.identityAugmentedMatrix (κ := ULift.{u} (Fin r)) (HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M A R x) :=
    AugmentedMatrixCokernels.identityAugmentedMatrix_map A _
  rw [he, AugmentedMatrixCokernels.identityAugmentedMatrix_flatRank_iff]
  simp only [Fintype.card_ulift, Fintype.card_fin]

theorem prescribedMatrixRanks_finite_intersection {κ : Type v} [Fintype κ]
    (μ ν : κ → Type u) [∀ i, Fintype (μ i)] [∀ i, Fintype (ν i)]
    [∀ i, DecidableEq (μ i)] [∀ i, DecidableEq (ν i)]
    (A : ∀ i, Matrix (ν i) (μ i) Γ(M.left, ⊤)) (r : κ → ℕ) :
    HilbertScheme.Presentations.SubfunctorRepresentations.ImmersionRepresentable (⨅ i, prescribedMatrixRankSubfunctor M (A i) (r i)) := by
  have h := HilbertScheme.Presentations.Finite.LocusIntersections.immersionRepresentable_finset_inf (Finset.univ : Finset κ)
    (fun i => prescribedMatrixRankSubfunctor M (A i) (r i)) (fun i _ => prescribedMatrixRank_immersion M (A i) (r i))
  simpa using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedMatrixRankLoci
