import OAI.ArithmeticGeometry.Descent.CMVariety.ConnectedEmbeddedCoefficients
import OAI.ArithmeticGeometry.Descent.CMVariety.GroupFamilyDimension
import OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli

/-! # Abelian Family -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! The constructed arithmetic group family has the original fixed
relative dimension and is an actual HilbertConstruction abelian scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (D : ConnectedEmbeddedCoefficients.Abelian.GeometricGroupCoefficientModel A)

abbrev ConnectedEmbeddedCoefficients.Abelian.GeometricGroupCoefficientModel.relativeDimension (_D : ConnectedEmbeddedCoefficients.Abelian.GeometricGroupCoefficientModel A) : ℕ :=
  AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap

theorem ConnectedEmbeddedCoefficients.Abelian.GeometricGroupCoefficientModel.smoothDimension :
    SmoothOfRelativeDimension D.relativeDimension D.data.toModel.model.hom := by
  let M := D.data.toModel.model
  let p := Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ ℂ D.data.toModel.coefficients
  have : IsSchemeTheoreticallyDominant p := Models.SpreadingOut.GenericFaithfulness.Construction.spec_injective_schematically_dominant
    (algebraMap (Models.CoefficientSystem.Constructions.Foundations.coefficientRing ℚ ℂ D.data.toModel.coefficients) ℂ) Subtype.val_injective
  have : IsDominant p := inferInstance
  have : Smooth A.toOver.hom := inferInstanceAs (Smooth A.variety.structureMap)
  have : IsIntegral A.toOver.left := A.variety.property
  have : IsProper A.toOver.hom := inferInstanceAs (IsProper A.variety.structureMap)
  have : GeometricallyConnected A.toOver.hom := Models.SpreadingOut.GeometricFieldComponents.Construction.integral_geometricallyConnected_over_algClosed A.toOver.hom
  have : IsIso D.data.toModel.genericIso.hom.left :=
    ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).mapIso D.data.toModel.genericIso).isIso_hom
  have hdim : topologicalKrullDim ((Over.pullback p).obj M).left =
      (D.relativeDimension : WithBot ℕ∞) :=
    D.data.toModel.genericIso.hom.left.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
      (AlgebraicGeometry.PELModuli.IntegralModel.Group.FamilyDimension.group_krullDim_eq_transcendenceDimension A.toOver)
  exact GroupFamilyDimension.Abelian.smooth_group_dimension_of_dominant_fiber M p D.relativeDimension hdim

def ConnectedEmbeddedCoefficients.Abelian.GeometricGroupCoefficientModel.abelian : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme D.relativeDimension (Models.CoefficientSystem.Constructions.Foundations.coefficientBase ℚ ℂ D.data.toModel.coefficients) where
  scheme := D.data.toModel.model
  group := D.group
  commutative := D.commutative
  proper := D.proper
  smoothDimension := D.smoothDimension
  connected := D.connected

def ConnectedEmbeddedCoefficients.Abelian.GeometricGroupCoefficientModel.fiberIso : (D.abelian.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ ℂ D.data.toModel.coefficients)).scheme ≅ A.toOver :=
  D.data.toModel.genericIso

instance ConnectedEmbeddedCoefficients.Abelian.GeometricGroupCoefficientModel.fiberIso_group : IsMonHom D.fiberIso.hom := D.comparison_group

def ConnectedEmbeddedCoefficients.Abelian.GeometricGroupCoefficientModel.presentation : StandardModuli.Abelian.ComplexAbelianPresentation
    (D.abelian.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ ℂ D.data.toModel.coefficients)) where
  variety := A
  comparison := D.fiberIso
  comparison_group := D.fiberIso_group

end

end OAI.ArithmeticGeometry.Descent.CMVariety
