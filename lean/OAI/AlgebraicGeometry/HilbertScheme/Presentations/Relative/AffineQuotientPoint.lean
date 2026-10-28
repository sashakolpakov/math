import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ClassifyingNaturality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedChartPoint
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality

/-! # Affine Quotient Point -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian

noncomputable section

/-! An actual finite projective coordinate quotient over an affine test
ring gives a Grassmannian point over any base, naturally in the test ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable {R A : Type u} [CommRing R] [CommRing A] {S : Scheme.{u}}

def relativeQuotientClassifyingPoint (f : Spec (.of R) ⟶ S)
    (H : Module.Grassmannian R (ν → R) (Fintype.card ι)) :
    Over.mk f ⟶ Presentations.Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := ν) S := by
  have h : (Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap (.of R) H ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap f) ≫
      Presentations.Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S = f := by
    rw [Category.assoc, Presentations.Grassmannian.BaseMap.grassmannianBaseMap_over, ← Category.assoc,
      Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap_over, Category.id_comp]
  exact Over.homMk (Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap (.of R) H ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap f) h

theorem relativeQuotientClassifyingPoint_natural (f : Spec (.of R) ⟶ S) (φ : R →+* A)
    (H : Module.Grassmannian R (ν → R) (Fintype.card ι)) :
    Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ ≫ relativeQuotientClassifyingPoint f H =
      relativeQuotientClassifyingPoint (Spec.map (CommRingCat.ofHom φ) ≫ f) (Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ H) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom φ) ≫ (Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap (.of R) H ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap f) =
    Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap (.of A) (Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ H) ≫
      Presentations.Grassmannian.BaseMap.grassmannianBaseMap (Spec.map (CommRingCat.ofHom φ) ≫ f)
  rw [Presentations.Grassmannian.BaseMap.grassmannianBaseMap_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap f)
      (Quotient.ClassifyingNaturality.Grassmannian.quotientClassifyingMap_natural (.of R) (.of A) φ H).symm).trans (Category.assoc _ _ _))

theorem relativeQuotientClassifyingPoint_normalized (f : Spec (.of R) ⟶ S)
    (a : ι → ν) (Q : Matrix ι ν R) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    relativeQuotientClassifyingPoint f (Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ) =
      Affine.NormalizedChartPoint.Grassmannian.affineNormalizedChartPoint f a Q hQ ≫ Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S := by
  have hker : (Matrix.toLin' Q).ker = Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R R)
      (Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ).toSubmodule := by
    change (Matrix.toLin' Q).ker = Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (RingHom.id R) (Matrix.toLin' Q).ker
    rw [Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_id]
  have h := Quotient.ClassifyingAffineFormula.Grassmannian.quotientClassifyingMap_on_affine_matrix (.of R) R (Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ) a Q hQ hker
  let QΓ : Matrix ι ν Γ(Spec (.of R), ⊤) := Q.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hQΓ : Normalized.Matrices.Grassmannian.IsNormalized a QΓ := hQ.map _
  have hraw : Spec.map (𝟙 (CommRingCat.of R)) ≫ Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap (.of R) (Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ) =
      Presentations.Grassmannian.PointBaseChange.matrixClassifyingSchemeMap a (Spec.map (𝟙 (CommRingCat.of R))) QΓ hQΓ := h
  have h' : Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap (.of R) (Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ) =
      Presentations.Grassmannian.PointBaseChange.matrixClassifyingSchemeMap a (𝟙 (Spec (.of R))) QΓ hQΓ := by
    simpa only [Spec.map_id, Category.id_comp] using hraw
  apply Over.OverMorphism.ext
  change Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap (.of R) (Normalized.Quotients.Grassmannian.normalizedGrassmannian a Q hQ) ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap f =
    Presentations.Grassmannian.PointBaseChange.matrixClassifyingSchemeMap a f QΓ hQΓ
  rw [h']
  simpa only [Category.id_comp] using Presentations.Grassmannian.PointBaseChange.matrixClassifyingSchemeMap_baseMap a f (𝟙 (Spec (.of R))) QΓ hQΓ

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian
