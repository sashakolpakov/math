import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TangentAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IsogenyTangent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Projectivity

/-! # Tangent Equiv -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TangentEquiv

noncomputable section

/-! The original polarization and representing Poincare family
construct a native tangent-to-H1 equivalence at every polarized object. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

local instance polarizedH1EquivIntegral : IsIntegral A.abelian.scheme.left :=
  Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A.abelian

local instance polarizedH1EquivModule : Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1) :=
  StructureComplexScalars.structureH1ComplexModule A.abelian.scheme

theorem polarizedStructureH1TangentLinear_bijective : Function.Bijective (TangentAction.polarizedStructureH1TangentLinear A) :=
  (RepresentedPicardTangentBijection.representedPicardTangentLinear_bijective A.abelian A.dual (Projectivity.polarizedNativeProjectivePresentation A)).comp
    (Intrinsic.IsogenyTangent.AbelianIntrinsicAdapter.nativeGroupTangentMap_isogeny_bijective A.abelian A.dual.abelian
      (Projectivity.polarizedNativeProjectivePresentation A) (Dual.Projectivity.dualNativeProjectivePresentation A) A.polarization.isogeny)

def polarizedStructureH1TangentEquiv :
    (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.abelian.scheme.hom) → ℂ) ≃ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1 :=
  LinearEquiv.ofBijective (TangentAction.polarizedStructureH1TangentLinear A) (polarizedStructureH1TangentLinear_bijective A)

theorem polarizedStructureH1TangentEquiv_apply
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.abelian.scheme.hom) → ℂ) :
    polarizedStructureH1TangentEquiv A v = TangentAction.polarizedStructureH1TangentLinear A v := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TangentEquiv
