import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.QuotientInjectivity
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedMatrixPoints

/-! # Classifying Affine Formula -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ClassifyingAffineFormula.Grassmannian

noncomputable section

/-! The quotient classifying map has the expected formula on every affine test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable (R : CommRingCat.{u}) (A : Type u) [CommRing A] [Algebra R A]

theorem quotientClassifyingMap_on_affine_matrix
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι))
    (a : ι → ν) (Q : Matrix ι ν A) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q)
    (hN : (Matrix.toLin' Q).ker = Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R A) N.toSubmodule) :
    (Relative.AffinePoints.relativeAffineScheme R A).hom ≫ Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R N =
      (Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A a Q hQ).left := by
  let U := Relative.AffinePoints.relativeAffineScheme R A
  apply Scheme.Cover.hom_ext ((Affine.QuotientClassifyingMap.Grassmannian.quotientPrincipalCover R N).openCover.pullback₁ U.hom)
  intro p
  change PrimeSpectrum R at p
  let D := (Affine.QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val
  change pullback.fst U.hom D.scheme.hom ≫
    (U.hom ≫ Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R N) =
      pullback.fst U.hom D.scheme.hom ≫ (Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A a Q hQ).left
  let T : Over (Spec R) := Over.mk (pullback.fst U.hom D.scheme.hom ≫ U.hom)
  let f : T ⟶ U := Over.homMk (pullback.fst U.hom D.scheme.hom)
  let g : T ⟶ D.scheme := Over.homMk (pullback.snd U.hom D.scheme.hom) pullback.condition.symm
  have he : g ≫ D.classifyingMap = f ≫ Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A a Q hQ := by
    rw [D.classifyingMap_comp, Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap_comp,
      ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap_eq_iff, D.pointMatrix_kernel,
      Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedPointMatrix_kernel R A a Q hQ f N.toSubmodule hN]
  have hd : D.scheme.hom ≫ Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R N = D.classifyingMap.left :=
    Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap_chart R N p
  rw [← Category.assoc, pullback.condition, Category.assoc]
  exact (congrArg (fun k => pullback.snd U.hom D.scheme.hom ≫ k) hd).trans
    (congrArg Over.Hom.left he)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ClassifyingAffineFormula.Grassmannian
