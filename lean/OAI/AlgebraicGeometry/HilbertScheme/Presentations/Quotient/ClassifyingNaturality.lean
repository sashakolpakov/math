import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ClassifyingAffineFormula
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.PointBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange

/-! # Classifying Naturality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ClassifyingNaturality.Grassmannian

noncomputable section

/-! The actual quotient classifying map is natural under arbitrary ring homomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

theorem quotientClassifyingMap_natural (R S : CommRingCat.{u}) (φ : R →+* S)
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι)) :
    Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap S (Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ N) ≫
        Presentations.Grassmannian.BaseMap.grassmannianBaseMap (Spec.map (CommRingCat.ofHom φ)) =
      Spec.map (CommRingCat.ofHom φ) ≫ Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R N := by
  let : Algebra R S := φ.toAlgebra
  let M := Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ N
  let f := Spec.map (CommRingCat.ofHom φ)
  apply (Affine.QuotientClassifyingMap.Grassmannian.quotientPrincipalCover S M).openCover.hom_ext
  intro p
  change PrimeSpectrum S at p
  let D := (Affine.QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt S M p).val
  let A := Localization.Away D.denominator
  have hker : (Matrix.toLin' D.matrix).ker =
      Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R A) N.toSubmodule :=
    D.kernel.trans (Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_comp φ (algebraMap S A) N.toSubmodule).symm
  have hb : D.scheme.hom ≫ f = (Relative.AffinePoints.relativeAffineScheme R A).hom :=
    (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap S A))).symm
  have hD : D.classifyingMap.left =
      (Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap S A D.columns D.matrix D.normalized).left := rfl
  let Q : Matrix ι ν Γ(Spec (CommRingCat.of A), ⊤) :=
    D.matrix.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hQ : Normalized.Matrices.Grassmannian.IsNormalized D.columns Q := D.normalized.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hc : D.classifyingMap.left ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap f =
      (Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A D.columns D.matrix D.normalized).left := by
    exact (congrArg (fun k => k ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap f)
      (hD.trans (Presentations.Grassmannian.PointBaseChange.affineNormalizedClassifyingMap_left D.columns S A D.matrix D.normalized))).trans
      ((Presentations.Grassmannian.PointBaseChange.matrixClassifyingSchemeMap_baseMap D.columns f D.scheme.hom Q hQ).trans
        ((congrArg (fun g : Spec (CommRingCat.of A) ⟶ Spec R =>
          Presentations.Grassmannian.PointBaseChange.matrixClassifyingSchemeMap D.columns g Q hQ) hb).trans
          (Presentations.Grassmannian.PointBaseChange.affineNormalizedClassifyingMap_left D.columns R A D.matrix D.normalized).symm))
  have hg : D.classifyingMap.left ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap f =
      (D.scheme.hom ≫ f) ≫ Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R N :=
    hc.trans ((ClassifyingAffineFormula.Grassmannian.quotientClassifyingMap_on_affine_matrix R A N D.columns D.matrix D.normalized hker).symm.trans
      (congrArg (fun g => g ≫ Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R N) hb.symm))
  change D.scheme.hom ≫ (Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap S M ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap f) =
    D.scheme.hom ≫ (f ≫ Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R N)
  have hd : D.scheme.hom ≫ Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap S M = D.classifyingMap.left :=
    Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap_chart S M p
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap f) hd).trans (hg.trans (Category.assoc _ _ _)))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ClassifyingNaturality.Grassmannian
