import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankKernelClassifier
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Rank Locus Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankLocusTransport

noncomputable section

/-! An all-test-scheme equivalence of two matrix rank conditions
constructs an actual map of the represented loci. Its square with
the ambient map is Cartesian, by the unique-lift universal property. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι μ ν : Type u} [Fintype ι] [Fintype μ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]
variable {S : Scheme.{u}} (M N : Over S) (F : Matrix ν μ Γ(M.left, ⊤)) (G : Matrix ν μ Γ(N.left, ⊤))
variable (a : N ⟶ M)
variable (H : ∀ (T : Over S) (x : T ⟶ N),
  HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ι) M F (x ≫ a) ↔ HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ι) N G x)

include H

theorem matrixRankLocusTransport_existsUnique :
    ∃! f : HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) N G ⟶ HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F,
      f ≫ HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap M F = HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap N G ≫ a :=
  (HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.matrixCokernelFlatRank_iff_unique_lift M F (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap N G ≫ a)).mp
    ((H _ _).mpr (RankKernelClassifier.matrixRankParameter_flatRank N G))

def matrixRankLocusTransport : HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) N G ⟶ HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F :=
  (matrixRankLocusTransport_existsUnique M N F G a H).choose

theorem matrixRankLocusTransport_factor :
    matrixRankLocusTransport M N F G a H ≫ HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap M F =
      HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap N G ≫ a :=
  (matrixRankLocusTransport_existsUnique M N F G a H).choose_spec.1

theorem matrixRankLocusTransport_isPullback :
    IsPullback (matrixRankLocusTransport M N F G a H) (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap N G)
      (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap M F) a where
  w := matrixRankLocusTransport_factor M N F G a H
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s => by
    have hf : HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ι) M F (s.fst ≫ HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap M F) :=
      (HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.matrixFlatRankSubfunctor (ι := ι) M F).map s.fst.op (RankKernelClassifier.matrixRankParameter_flatRank M F)
    rw [s.condition] at hf
    have hex := (HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.matrixCokernelFlatRank_iff_unique_lift N G s.snd).mp ((H _ _).mp hf)
    let u := hex.choose
    have hu := hex.choose_spec.1
    have huniq := hex.choose_spec.2
    refine ⟨u, ?_, hu, ?_⟩
    · change u ≫ matrixRankLocusTransport M N F G a H = s.fst
      apply (cancel_mono (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F)).mp
      rw [Category.assoc, matrixRankLocusTransport_factor, ← Category.assoc, hu]
      exact s.condition.symm
    · intro v _ hv
      exact huniq v hv)⟩

theorem matrixRankLocusTransport_isPullback_left :
    IsPullback (matrixRankLocusTransport M N F G a H).left (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap N G).left
      (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap M F).left a.left :=
  (matrixRankLocusTransport_isPullback M N F G a H).map (Over.forget S)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankLocusTransport
