import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedPicardTangentBijection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity

/-! # Picard Tangent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.PicardTangent

noncomputable section

/-! For every original polarized object, the actual dual tangent
space identifies with native algebraic H1. The projective presentation
is constructed from the object's polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

local instance polarizedPicardH1Module : Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1) :=
  StructureComplexScalars.structureH1ComplexModule A.abelian.scheme
local instance polarizedPicardDualIntegral : IsIntegral A.dual.abelian.scheme.left :=
  Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A.dual.abelian
local instance polarizedPicardTargetIntegral : IsIntegral A.abelian.scheme.left :=
  Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A.abelian
local instance polarizedPicardTargetDiagonal :
    IsAffineHom (CategoryTheory.Limits.pullback.diagonal
      (CategoryTheory.Limits.terminal.from
        (CategoryTheory.MonoidalCategory.tensorObj (LieRanks.dualNumberTest ℂ) A.abelian.scheme).left)) :=
  Dual.AffineDiagonal.dualFamily_affineDiagonal A.abelian.scheme

def polarizedPicardTangentEquiv :
    (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.dual.abelian.scheme.hom) → ℂ) ≃ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1 :=
  RepresentedPicardTangentBijection.representedPicardTangentEquiv A.abelian A.dual (Projectivity.polarizedNativeProjectivePresentation A)

theorem polarizedPicardTangentEquiv_apply
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.dual.abelian.scheme.hom) → ℂ) :
    polarizedPicardTangentEquiv A v = Dual.ParameterDeformationClass.dualParameterDeformationClass A.dual.poincare
      A.dual.normalizedAtDualZero.some (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv A.dual.abelian.scheme 1 v) := rfl

theorem polarizedStructureH1_finrank :
    Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1) = g :=
  RepresentedPicardTangentBijection.representedStructureH1_finrank A.abelian A.dual (Projectivity.polarizedNativeProjectivePresentation A)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.PicardTangent
