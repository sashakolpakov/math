import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.CoverCupTensor
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationGraphPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.GraphIntrinsicCupConstraint
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TangentBilinear

/-! # Polarized Family Tangent Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedFamilyTangentCoordinates.Construction

noncomputable section

/-! The original polarized family cup boundary gives zero alternating
tensor of its actual tangent obstruction and graph logarithm. The
polarization pairing then gives twice the alternating coefficient tensor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] FixedFiber.IntrinsicChartRange.Construction.fixedTranslationProjectionAffine AbelianModuli.ReferenceFamily.Polarized.ConormalBilinear.polarizedPairingH1Module

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback
attribute [local instance] AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_smooth AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_proper
  AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_connected AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_integral AbelianModuli.ReferenceFamily.FamilyTangent.IntrinsicVanishing.familyNativeFixedFiber_group

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
    (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover A.graphBundle)
    {I : Type} [Fintype I]
    (b : Module.Basis I ℂ (AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme)))

local instance polarizedTangentCoordinatesH1Module :
    Module ℂ (SheafCohomology.AffineH.Projective.H (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme).left) 1) :=
  AbelianModuli.ReferenceFamily.StructureComplexScalars.structureH1ComplexModule (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme)

/-- The polarization pairing applied to the tangent class is the defined bilinear value. -/
theorem polarizedFamilyTangentBilinear_coordinates (d : Derivation ℂ R ℂ)
    (z : AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme)) :
    AbelianModuli.ReferenceFamily.Polarized.ConormalBilinear.polarizedH1ConormalEquiv (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
      (AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyTangentSheafClass R A.abelian.scheme C.cover d z) =
      AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A C.cover d z := by
  ext w
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedFamilyTangentCoordinates.Construction
