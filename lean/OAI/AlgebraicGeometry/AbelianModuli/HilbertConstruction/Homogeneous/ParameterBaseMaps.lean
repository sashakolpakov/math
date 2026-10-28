import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientClassification

/-! # Parameter Base Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ParameterBaseMaps

noncomputable section

/-! Homogeneous quotient parameter maps commute with a change of base scheme while retaining the same coefficient-ring quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} (f : T ⟶ S) (n d r : ℕ)

def homogeneousParameterBaseMap :
    (QuotientParameters.homogeneousQuotientParameterScheme.{u, 0} (Fin (n + 1)) d r T).left ⟶
      (QuotientParameters.homogeneousQuotientParameterScheme.{u, 0} (Fin (n + 1)) d r S).left :=
  HilbertScheme.Presentations.Grassmannian.BaseMap.grassmannianBaseMap f

theorem homogeneousParameterBaseMap_over :
    homogeneousParameterBaseMap f n d r ≫
      (QuotientParameters.homogeneousQuotientParameterScheme.{u, 0} (Fin (n + 1)) d r S).hom =
    (QuotientParameters.homogeneousQuotientParameterScheme.{u, 0} (Fin (n + 1)) d r T).hom ≫ f :=
  HilbertScheme.Presentations.Grassmannian.BaseMap.grassmannianBaseMap_over f

def homogeneousParameterBaseMapOver :
    (Over.map f).obj (QuotientParameters.homogeneousQuotientParameterScheme.{u, 0} (Fin (n + 1)) d r T) ⟶
      QuotientParameters.homogeneousQuotientParameterScheme.{u, 0} (Fin (n + 1)) d r S :=
  Over.homMk (homogeneousParameterBaseMap f n d r) (homogeneousParameterBaseMap_over f n d r)

theorem homogeneousQuotientClassifier_postcomp (R : CommRingCat.{u}) (g : Spec R ⟶ T)
    (U : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) r) :
    (QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) d r R g U).left ≫
      homogeneousParameterBaseMap f n d r =
    (QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) d r R (g ≫ f) U).left := by
  rw [QuotientClassification.homogeneousQuotientAffinePointEquiv_coordinates, QuotientClassification.homogeneousQuotientAffinePointEquiv_coordinates,
    Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv_left, Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv_left]
  change (_ ≫ HilbertScheme.Presentations.Grassmannian.BaseMap.grassmannianBaseMap g) ≫ HilbertScheme.Presentations.Grassmannian.BaseMap.grassmannianBaseMap f = _ ≫ HilbertScheme.Presentations.Grassmannian.BaseMap.grassmannianBaseMap (g ≫ f)
  rw [HilbertScheme.Presentations.Grassmannian.BaseMap.grassmannianBaseMap_comp, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ParameterBaseMaps
