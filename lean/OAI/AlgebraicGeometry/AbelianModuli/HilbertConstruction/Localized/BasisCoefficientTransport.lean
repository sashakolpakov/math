import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuotientCoefficientMap
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.Module

/-! # Basis Coefficient Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.BasisCoefficientTransport

noncomputable section

/-! A basis on a principal localization can be transported through any
further coefficient algebra. Affine coordinate points have the exact global
coefficient map used by this tensor transport. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u v w

def localizedModuleBasis_baseChange
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (r : R) (B : Type w) [CommRing B] [Algebra R B]
    [Algebra (Localization.Away r) B] [IsScalarTower R (Localization.Away r) B]
    {ι : Type*} (b : Module.Basis ι (Localization.Away r) (LocalizedModule.Away r M)) :
    Module.Basis ι B (B ⊗[R] M) :=
  ((b.map (LocalizedModule.equivTensorProduct (Submonoid.powers r) M)).baseChange B).map
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away r) B B M)

theorem affineCoordinateMap_appTop
    {S : Scheme.{u}} [IsAffine S] {B : Type u} [CommRing B] (φ : Γ(S, ⊤) →+* B) :
    (Affine.QuotientCoefficientMap.affineCoordinateMap φ).appTop.hom = (Scheme.ΓSpecIso (.of B)).inv.hom.comp φ := by
  apply RingHom.ext
  intro r
  apply (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.injective
  have h := RingHom.congr_fun (Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap φ) r
  exact h.trans ((Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.apply_symm_apply (φ r)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.BasisCoefficientTransport
