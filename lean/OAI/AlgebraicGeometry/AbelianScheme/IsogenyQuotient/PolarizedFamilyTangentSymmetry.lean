import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedTangentFrameSymmetry
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyTangentCoverIndependence

/-! # Polarized Family Tangent Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedFamilyTangentSymmetry.Construction

noncomputable section

/-! Every actual polarized abelian family has a symmetric original
tangent bilinear form on every original affine cover. The graph frames,
cup relation, H1 pairing, and change of cover are all constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback
attribute [local instance] AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_smooth AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_proper
  AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_connected AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_integral AbelianModuli.ReferenceFamily.FamilyTangent.IntrinsicVanishing.familyNativeFixedFiber_group

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
    (U V : Scheme.AffineOpenCover.{0, 0} A.abelian.scheme.left)

theorem polarizedFamilyTangentBilinear_cover_independent :
    AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A U = AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A V := by
  unfold AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear
  rw [FamilyTangentCoverIndependence.Construction.familyBaseTangentObstruction_cover_independent R A.abelian.scheme U V]

theorem polarizedFamilyTangentBilinear_symmetric (d : Derivation ℂ R ℂ)
    (z w : AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme)) :
    AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A U d z w =
      AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A U d w z := by
  let C := AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.lineBundleAffineFrameCover A.graphBundle
  rw [polarizedFamilyTangentBilinear_cover_independent R A U C.cover]
  exact PolarizedTangentFrameSymmetry.Construction.polarizedFamilyTangentBilinear_frame_symmetric R A C d z w

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedFamilyTangentSymmetry.Construction
