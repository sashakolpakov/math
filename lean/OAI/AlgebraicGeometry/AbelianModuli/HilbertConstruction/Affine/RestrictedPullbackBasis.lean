import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeometricSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.PullbackSquare
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictedSectionBases

/-! # Restricted Pullback Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RestrictedPullbackBasis

noncomputable section

/-! An actual basis of a comparison sheaf on a preimage open gives a basis of the affine scalar extension of the original sheaf's sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct
universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    [IsAffine U.toScheme] [IsAffine (f ⁻¹ᵁ U).toScheme]
    (M : X.Modules) [M.IsQuasicoherent] (Q : Y.Modules)

def affineRestrictedPullbackBasis
    (e : (Scheme.Modules.pullback f).obj M ≅ Q)
    (basis : Γ(Q, f ⁻¹ᵁ U) ≃ₗ[Γ(Y, f ⁻¹ᵁ U)] Γ(Y, f ⁻¹ᵁ U)) :
    letI : Algebra Γ(U.toScheme, ⊤) Γ((f ⁻¹ᵁ U).toScheme, ⊤) :=
      (f ∣_ U).appTop.hom.toAlgebra
    Γ((f ⁻¹ᵁ U).toScheme, ⊤) ⊗[Γ(U.toScheme, ⊤)] Γ(M.restrict U.ι, ⊤) ≃ₗ[
      Γ((f ⁻¹ᵁ U).toScheme, ⊤)] Γ((f ⁻¹ᵁ U).toScheme, ⊤) := by
  letI : Algebra Γ(U.toScheme, ⊤) Γ((f ⁻¹ᵁ U).toScheme, ⊤) :=
    (f ∣_ U).appTop.hom.toAlgebra
  let comparison : (Scheme.Modules.pullback (f ∣_ U)).obj (M.restrict U.ι) ≅
      Q.restrict (f ⁻¹ᵁ U).ι :=
    (OpenModule.PullbackSquare.OpenPullbackSquare.adjointPullbackSquare f U).app M ≪≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso e
  exact (GeometricSections.AffineGeometricSections.iso (f ∣_ U) (M.restrict U.ι)).toLinearEquiv ≪≫ₗ
    ((SectionAdjunction.AffineSectionAdjunction.sections (f ⁻¹ᵁ U).toScheme).mapIso comparison).toLinearEquiv ≪≫ₗ
      Open.RestrictedSectionBases.moduleRestrictTopBasisEquiv Q (f ⁻¹ᵁ U) basis

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RestrictedPullbackBasis
