import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankKernelClassifier

/-! # Rank Classifier Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankClassifierCoefficients

noncomputable section

/-! The Grassmannian classifier of the rank locus is characterized on
affine tests by the original ambient matrix pulled along that test.
This removes the intermediate universal pullback matrix from its formula. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι μ ν : Type u} [Fintype ι] [Fintype μ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]
variable {S : Scheme.{u}} (M : Over S) (F : Matrix ν μ Γ(M.left, ⊤))

omit [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν] in
theorem affineSchemeMatrixCoefficients_pullback {T : Over S} (x : T ⟶ M)
    (R : CommRingCat.{u}) (y : Spec R ⟶ T.left) :
    SchemeFlatMatrixGrassmannian.affineSchemeMatrixCoefficients T (F.map x.left.appTop.hom) R y =
      SchemeFlatMatrixGrassmannian.affineSchemeMatrixCoefficients M F R (y ≫ x.left) := by
  ext i j
  exact congrArg (Scheme.ΓSpecIso R).hom
    (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop y x.left).symm (F i j))

theorem matrixRankKernelClassifier_affine_of_kernel (R : CommRingCat.{u})
    (x : Spec R ⟶ (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F).left)
    (Q : Module.Grassmannian R (μ → R) (Fintype.card ι))
    (hQ : Q.toSubmodule =
      (Matrix.toLin' (SchemeFlatMatrixGrassmannian.affineSchemeMatrixCoefficients M F R
        (x ≫ (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F).left))).ker) :
    x ≫ (RankKernelClassifier.matrixRankKernelClassifier (ι := ι) M F).left =
      (HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint (x ≫ (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F).hom) Q).left := by
  rw [RankKernelClassifier.matrixRankKernelClassifier_affine]
  have he : SchemeFlatMatrixGrassmannian.affineMatrixKernelPoint (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F)
      (F.map (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F).left.appTop.hom)
      (RankKernelClassifier.matrixRankPulledMatrix_flatRank M F) R x = Q := by
    apply Module.Grassmannian.ext
    change (Matrix.toLin' (SchemeFlatMatrixGrassmannian.affineSchemeMatrixCoefficients (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M F)
      (F.map (HilbertScheme.Presentations.MatrixRank.Data.Grassmannian.matrixRankParameterMap (ι := ι) M F).left.appTop.hom) R x)).ker = Q.toSubmodule
    rw [affineSchemeMatrixCoefficients_pullback]
    exact hQ.symm
  rw [he]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankClassifierCoefficients
