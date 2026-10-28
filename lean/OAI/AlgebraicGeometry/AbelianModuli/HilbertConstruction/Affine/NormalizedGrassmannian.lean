import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ParameterScheme
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Quotients

/-! # Normalized Grassmannian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.NormalizedGrassmannian

noncomputable section

/-! The affine quotient classification agrees with normalized matrices over the coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Quotients.Grassmannian

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable (R : CommRingCat.{u}) (a : ι → ν) (Q : Matrix ι ν R) (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q)

theorem quotientClassifyingMap_normalized :
    HilbertScheme.Presentations.Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ) =
      (HilbertScheme.Presentations.Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R R a Q hQ).left := by
  have hker : (Matrix.toLin' Q).ker = HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R R)
      (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ).toSubmodule :=
    (HilbertScheme.Presentations.Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_id (Matrix.toLin' Q).ker).symm
  have h := HilbertScheme.Presentations.Quotient.ClassifyingAffineFormula.Grassmannian.quotientClassifyingMap_on_affine_matrix R R
    (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ) a Q hQ hker
  change Spec.map (𝟙 R) ≫ HilbertScheme.Presentations.Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ) = _ at h
  simpa only [Spec.map_id, Category.id_comp] using h

theorem grassmannParameterAffinePointEquiv_normalized {S : Scheme.{u}} (f : Spec R ⟶ S) :
    Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ) =
      HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap a (Q.map (Scheme.ΓSpecIso R).inv.hom)
        (hQ.map (Scheme.ΓSpecIso R).inv.hom) := by
  apply (Over.forget S).map_injective
  change (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ)).left =
    (HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap (T := Over.mk f) a
      (Q.map (Scheme.ΓSpecIso R).inv.hom) (hQ.map (Scheme.ΓSpecIso R).inv.hom)).left
  rw [Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv_left, quotientClassifyingMap_normalized,
    HilbertScheme.Presentations.Grassmannian.PointBaseChange.affineNormalizedClassifyingMap_left]
  change HilbertScheme.Presentations.Grassmannian.PointBaseChange.matrixClassifyingSchemeMap a (Spec.map (𝟙 R))
    (Q.map (Scheme.ΓSpecIso R).inv.hom) (hQ.map (Scheme.ΓSpecIso R).inv.hom) ≫
      HilbertScheme.Presentations.Grassmannian.BaseMap.grassmannianBaseMap f = HilbertScheme.Presentations.Grassmannian.PointBaseChange.matrixClassifyingSchemeMap a f
        (Q.map (Scheme.ΓSpecIso R).inv.hom) (hQ.map (Scheme.ΓSpecIso R).inv.hom)
  rw [HilbertScheme.Presentations.Grassmannian.PointBaseChange.matrixClassifyingSchemeMap_baseMap, Spec.map_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.NormalizedGrassmannian
