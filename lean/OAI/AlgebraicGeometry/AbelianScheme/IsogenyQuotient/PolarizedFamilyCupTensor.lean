import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyReferenceCupTensor
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedFamilyTangentCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlternatingTensorTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationGraphPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.GraphIntrinsicCupConstraint
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TangentBilinear

/-! # Polarized Family Cup Tensor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedFamilyCupTensor.Construction

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

attribute [local instance] FamilyReferenceCupTensor.Construction.polarizedCupH1Module

theorem polarizedFamily_alternatingCoefficientTensor (d : Derivation ℂ R ℂ) :
    ∑ a, (AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A C.cover d (b a) ⊗ₜ[ℂ] b.coord a -
      b.coord a ⊗ₜ[ℂ] AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A C.cover d (b a)) = 0 := by
  exact AlternatingTensorTransport.Construction.alternatingTensor_transport_cancel
    (AbelianModuli.ReferenceFamily.Polarized.ConormalBilinear.polarizedH1ConormalEquiv
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))).toLinearMap
    (fun a => AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyTangentSheafClass R A.abelian.scheme C.cover d (b a))
    (fun a => AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogSheafClass R A.abelian.scheme C.cover C.transitions (b.coord a))
    (fun a => AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A C.cover d (b a))
    (fun a => b.coord a) (2 : ℂ) (by norm_num)
    (fun a => PolarizedFamilyTangentCoordinates.Construction.polarizedFamilyTangentBilinear_coordinates R A C d (b a))
    (fun a => PolarizationGraphPairing.Construction.polarizationGraphLineLog_polarizedPairing R A C (b.coord a))
    (FamilyReferenceCupTensor.Construction.polarizedFamily_originalCupTensor R A C b d)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedFamilyCupTensor.Construction
