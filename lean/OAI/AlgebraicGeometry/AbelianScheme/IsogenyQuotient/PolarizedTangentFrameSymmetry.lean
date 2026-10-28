import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedFamilyCupTensor
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BilinearTensorSymmetry

/-! # Polarized Tangent Frame Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedTangentFrameSymmetry.Construction

noncomputable section

/-! Symmetry of the original polarized family tangent pairing on an
actual affine frame cover follows from the original graph cup boundary
and the proved translation-logarithm comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct BigOperators

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BilinearTensorSymmetry

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback
attribute [local instance] AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_smooth AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_proper
  AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_connected AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_integral AbelianModuli.ReferenceFamily.FamilyTangent.IntrinsicVanishing.familyNativeFixedFiber_group

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
    (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover A.graphBundle)

theorem polarizedFamilyTangentBilinear_frame_symmetric
    (d : Derivation ℂ R ℂ)
    (z w : AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme)) :
    AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A C.cover d z w =
      AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A C.cover d w z := by
  let V := AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme)
  let b := Module.finBasis ℂ V
  let F := AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A C.cover d
  apply AbelianModuli.ReferenceFamily.BilinearTensorSymmetry.bilinear_symm_of_alternating_coefficientTensor_zero b F _ z w
  unfold AbelianModuli.ReferenceFamily.BilinearTensorSymmetry.bilinearCoefficientTensor
  simpa only [map_sum, TensorProduct.comm_tmul, ← Finset.sum_sub_distrib] using
    PolarizedFamilyCupTensor.Construction.polarizedFamily_alternatingCoefficientTensor R A C b d

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedTangentFrameSymmetry.Construction
