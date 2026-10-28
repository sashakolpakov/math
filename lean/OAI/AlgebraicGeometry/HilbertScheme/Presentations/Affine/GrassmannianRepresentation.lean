import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.PointQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ClassifyingNaturality

/-! # Grassmannian Representation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-!
Affine points of the constructed projective Grassmannian are exactly the
actual finite projective coordinate quotients of constant rank. Both
directions of this equivalence are constructed and verified.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable {R : CommRingCat.{u}}
variable {g : Over.mk (𝟙 (Spec R)) ⟶ Presentations.Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := ν) (Spec R)}
variable (D : Presentations.Grassmannian.PointFiniteCharts.FiniteGrassmannianMatrixPresentation R g)

def Grassmannian.PointFiniteCharts.FiniteGrassmannianMatrixPresentation.affineCover : (Spec R).AffineOpenCover where
  I₀ := D.index
  X i := CommRingCat.of (Localization.Away (D.denominator i))
  f i := (Relative.AffinePoints.relativeAffineScheme R (Localization.Away (D.denominator i))).hom
  idx p := (D.covers p).choose
  covers p := by
    change p ∈ (Spec.map (CommRingCat.ofHom (algebraMap R
      (Localization.Away (D.denominator (D.covers p).choose))))).opensRange
    rw [Scheme.Hom.opensRange_localizationAway]
    exact (D.covers p).choose_spec
  map_prop i := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (D.denominator i)))))
    infer_instance

theorem Grassmannian.PointFiniteCharts.FiniteGrassmannianMatrixPresentation.quotient_classifyingMap :
    Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R D.quotient = g.left := by
  apply D.affineCover.openCover.hom_ext
  intro i
  change D.index at i
  change (Relative.AffinePoints.relativeAffineScheme R (Localization.Away (D.denominator i))).hom ≫ Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R D.quotient =
    (Relative.AffinePoints.relativeAffineScheme R (Localization.Away (D.denominator i))).hom ≫ g.left
  exact (Quotient.ClassifyingAffineFormula.Grassmannian.quotientClassifyingMap_on_affine_matrix R (Localization.Away (D.denominator i))
    D.quotient (D.columns i) (D.matrix i) (D.normalized i) (D.relations_localized i).symm).trans
      (D.classifies i).symm

theorem Grassmannian.PointFiniteCharts.FiniteGrassmannianMatrixPresentation.quotient_classifyingOver :
    Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingOver R D.quotient = g :=
  (Over.forget (Spec R)).map_injective D.quotient_classifyingMap

variable (R) in
theorem Affine.GrassmannianRepresentation.Grassmannian.quotientClassifyingOver_bijective :
    Function.Bijective (Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingOver (ι := ι) (ν := ν) R) := by
  constructor
  · intro N M h
    exact Affine.QuotientInjectivity.Grassmannian.quotientClassifyingMap_injective (congrArg Over.Hom.left h)
  · intro g
    let D := Presentations.Grassmannian.PointFiniteCharts.grassmannianPointFinitePresentation R g
    exact ⟨D.quotient, D.quotient_classifyingOver⟩

variable (R) in
/-- The Grassmannian represents actual finite projective quotients on affine tests. -/
def Affine.GrassmannianRepresentation.Grassmannian.affineGrassmannianPointEquiv :
    Module.Grassmannian R (ν → R) (Fintype.card ι) ≃
      (Over.mk (𝟙 (Spec R)) ⟶ Presentations.Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := ν) (Spec R)) :=
  Equiv.ofBijective (Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingOver R) (Affine.GrassmannianRepresentation.Grassmannian.quotientClassifyingOver_bijective R)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations
