import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeFlatMatrixGrassmannian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ConfigurationPolynomialRankLocus

/-! # Rank Kernel Classifier -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankKernelClassifier

noncomputable section

/-! The represented matrix rank locus carries a canonical morphism to
the Grassmannian of its kernel quotient. In particular this constructs
the polynomial kernel classifier on every stable configuration chart. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι μ ν : Type u} [Fintype ι] [Fintype μ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]
variable {S : Scheme.{u}} (M : Over S) (F : Matrix ν μ Γ(M.left, ⊤))

omit [DecidableEq ι] [DecidableEq ν] in
theorem matrixCokernelFlatRank_pullback_identity {T : Over S} (x : T ⟶ M) :
    HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ι) T (F.map x.left.appTop.hom) (𝟙 T) ↔
      HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ι) M F x := by
  have he : ∀ t : T.left,
      HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.matrixAtStalk T (F.map x.left.appTop.hom) (𝟙 T) t = HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.matrixAtStalk M F x t := by
    intro t
    ext i j
    simp [HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.matrixAtStalk]
  unfold HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank
  apply forall_congr'
  intro t
  rw [he t]

theorem matrixRankParameter_flatRank :
    HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ι) M F (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F) := by
  apply (HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.matrixCokernelFlatRank_iff_unique_lift (ι := ι) M F (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F)).mpr
  refine ⟨𝟙 _, by simp, fun y hy => ?_⟩
  apply (cancel_mono (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F)).mp
  simpa only [Category.id_comp] using hy

theorem matrixRankPulledMatrix_flatRank :
    HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ι) (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F)
      (F.map (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F).left.appTop.hom) (𝟙 _) :=
  (matrixCokernelFlatRank_pullback_identity (ι := ι) M F (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F)).mpr
    (matrixRankParameter_flatRank (ι := ι) M F)

def matrixRankKernelClassifier :
    HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F ⟶ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := μ) S :=
  SchemeFlatMatrixGrassmannian.schemeFlatMatrixKernelOver (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F)
    (F.map (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F).left.appTop.hom)
    (matrixRankPulledMatrix_flatRank (ι := ι) M F)

theorem matrixRankKernelClassifier_affine (R : CommRingCat.{u})
    (x : Spec R ⟶ (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F).left) :
    x ≫ (matrixRankKernelClassifier (ι := ι) M F).left =
      (HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint (x ≫ (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F).hom)
        (SchemeFlatMatrixGrassmannian.affineMatrixKernelPoint (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F)
          (F.map (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F).left.appTop.hom)
          (matrixRankPulledMatrix_flatRank (ι := ι) M F) R x)).left :=
  SchemeFlatMatrixGrassmannian.schemeFlatMatrixKernelMap_affine _ _ _ R x

def stableConfigurationPolynomialKernelClassifier
    (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m)
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D k : ℕ) :
    Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D k ⟶
      HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianOver (ι := ULift.{u} (Fin k)) (ν := HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n D) (Spec (.of R)) :=
  matrixRankKernelClassifier (ι := ULift.{u} (Fin k))
    (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) (Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i j D)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankKernelClassifier
