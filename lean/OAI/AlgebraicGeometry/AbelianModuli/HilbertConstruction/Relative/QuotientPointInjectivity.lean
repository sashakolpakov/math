import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineQuotientPoint
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.QuotientInjectivity
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.BaseChange

/-! # Quotient Point Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.QuotientPointInjectivity

noncomputable section

/-! A relative Grassmannian point retains the exact finite
projective quotient kernel of the original affine coefficient ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable {R : Type u} [CommRing R] {S : Scheme.{u}}

theorem relativeQuotientClassifyingPoint_injective (f : Spec (.of R) ⟶ S) :
    Function.Injective (HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint (ι := ι) (ν := ν) f) := by
  intro Q L h
  apply HilbertScheme.Presentations.Affine.QuotientInjectivity.Grassmannian.quotientClassifyingMap_injective (R := CommRingCat.of R) (ι := ι) (ν := ν)
  apply (HilbertScheme.Presentations.Grassmannian.BaseChange.grassmannianBaseMap_isPullback (ι := ι) (ν := ν) f).hom_ext
  · exact congrArg Over.Hom.left h
  · rw [HilbertScheme.Presentations.Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap_over, HilbertScheme.Presentations.Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap_over]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.QuotientPointInjectivity
