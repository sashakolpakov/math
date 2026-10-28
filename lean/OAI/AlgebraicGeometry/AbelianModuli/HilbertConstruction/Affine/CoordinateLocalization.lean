import Mathlib.RingTheory.Localization.Basic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.BasisCoefficientTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.LineBundleLocalization

/-! # Coordinate Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateLocalization

noncomputable section

/-! The global coefficient algebra of the actual affine localization
point is the specified localization. This transfers the section
localization theorem to that exact scheme morphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} [IsAffine S]

theorem affineCoordinateLocalization_global
    (T : Submonoid Γ(S, ⊤)) (B : Type u) [CommRing B] [Algebra Γ(S, ⊤) B] [IsLocalization T B] :
    IsLocalization T (TensorSectionComparison.morphismGlobalAlgebra (QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) B))) := by
  let q := QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) B)
  let e : B ≃ₐ[Γ(S, ⊤)] TensorSectionComparison.morphismGlobalAlgebra q :=
    { (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm with
      commutes' := fun r => (RingHom.congr_fun
        (Localized.BasisCoefficientTransport.affineCoordinateMap_appTop (algebraMap Γ(S, ⊤) B)) r).symm }
  exact IsLocalization.isLocalization_of_algEquiv T e

theorem affineCoordinateLocalization_sections
    {X : Scheme.{u}} [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ S) (L : Line.Bundles.LineBundle X) (T : Submonoid Γ(S, ⊤))
    (B : Type u) [CommRing B] [Algebra Γ(S, ⊤) B] [IsLocalization T B] :
    IsLocalizedModule T
      ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap
        (pullback.fst f (QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) B))) f.appTop.hom L.sheaf).app (.op ⊤)).hom := by
  have := affineCoordinateLocalization_global T B
  exact Flat.LineBundleLocalization.localized_lineBundle_section_pullback
    (IsPullback.of_hasPullback f (QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) B))) L T

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateLocalization
